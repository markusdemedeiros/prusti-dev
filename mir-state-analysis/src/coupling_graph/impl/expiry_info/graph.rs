// © 2024, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(unused_imports)]
use prusti_rustc_interface::{
    borrowck::{
        borrow_set::{BorrowData, TwoPhaseActivation},
        consumers::{
            calculate_borrows_out_of_scope_at_location, places_conflict, BorrowIndex, Borrows,
            OutlivesConstraint, PlaceConflictBias, RichLocation,
        },
    },
    data_structures::fx::{FxHashSet, FxIndexMap},
    dataflow::{Analysis, AnalysisDomain, ResultsCursor},
    index::{
        bit_set::{BitSet, HybridBitSet},
        Idx,
    },
    middle::{
        mir::{
            visit::Visitor, BasicBlock, Body, CallReturnPlaces, ConstantKind, Local, Location,
            Operand, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorEdges,
            TerminatorKind, RETURN_PLACE, START_BLOCK,
        },
        ty::{RegionVid, TyCtxt},
    },
};

use std::collections::HashSet;

use prusti_rustc_interface::data_structures::fx::FxHashMap; 

use crate::coupling_graph::CgContext;

use super::control_flow::ControlFlowFlag;


// Labelled, directed ?-hypergraph of expiry groups
// 
// Vertices are possibly tagged lifetimes
// Edges are uniquely identified by a "Group", each group is labelled.
// Hyper-edges { A, B, C } -> { D, E, F } interpreted as a family of triangles:
//      A -> { D, E, F }
//      B -> { D, E, F }
//      C -> { D, E, F }
// Thus, the graph may remove individual parents of an edge 
//  { A, B, C } -> { D, E, F }  =>  { B, C } -> { D, E, F }

type VertexTag = Location; 

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub(crate) struct Vertex {
    region: RegionVid,
    tag: Option<VertexTag>,
}

impl Vertex {
    pub(crate) fn untagged(region: RegionVid) -> Self {
        Self {
            region,
            tag: None
        }
    }


    /// Tags a vertex only if it is untagged
    pub(crate) fn tag_safe(&mut self, tag: VertexTag) {
        self.tag = self.tag.or_else(|| Some(tag));
    }

    pub(crate) fn is_tagged(&self) -> bool {
        self.tag.is_some()
    }
}

impl std::fmt::Debug for Vertex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.tag {
            Some(t) => write!(f, "{:?}@{:?}", self.region, t),
            None => write!(f, "{:?}", self.region)
        }
    }
}

type Group = usize;

/// DSL for the actions an exiry may require from the lower passes
/// These make up the annotations on each group
#[derive(PartialEq, Eq, Hash, Clone)]
pub(crate) enum Annotation {
    /// Base-level expiry associated to the loan Vertex
    BasicExpiry(Vertex),
    Freeze(Vertex),
    Thaw(Vertex),
    Branch(Vec<(ControlFlowFlag, Vec<Annotation>)>),
}

impl std::fmt::Debug for Annotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BasicExpiry(v) => write!(f, "basic({:?})", v),
            Self::Freeze(v) => write!(f, "freeze({:?})", v),
            Self::Thaw(v) => write!(f, "thaw({:?})", v),
            Self::Branch(bs) =>write!(f, "<branched annotations>"),
        }
    }
}


/// Information associated to each expiry group
#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub(crate) struct GroupData {
    /// None when the edge is Opaque 
    /// Some when the edge is Transparent or Translucent
    annotations : Option<Vec<Annotation>>,
    // parents of the edge when it was issued
    // initial_parents : Option<FxHashSet<Vertex>>,
}

impl GroupData {
    /// Annotations for a basic expiry 
    pub(crate) fn basic_data(vertex: Vertex) -> Self {
        Self {
            annotations: Some(vec![Annotation::BasicExpiry(vertex)])
        }
    }

    pub(crate) fn tag(&mut self, v: RegionVid, location: Location) {
        if let Some(ans) = &mut self.annotations {
            for an in ans.iter_mut() {
                match an {
                    Annotation::BasicExpiry(v1) => if v1.tag.is_none() && v1.region == v { v1.tag = Some(location); },
                    Annotation::Freeze(v1) => if v1.tag.is_none() && v1.region == v { v1.tag = Some(location); },
                    Annotation::Thaw(v1) => if v1.tag.is_none() && v1.region == v { v1.tag = Some(location); },
                    Annotation::Branch(_) => todo!("implement branch tagging"),
                }
            }
        }
    }
}


#[derive(Debug, Clone)]
pub(crate) struct Eg { 
    /// Edge structure of the groups 
    parents : FxHashMap<Group, FxHashSet<Vertex>>,
    children : FxHashMap<Group, FxHashSet<Vertex>>,

    /// Set of vertices in the graph
    live_regions : FxHashSet<Vertex>,

    /// Edges of the graph, plus their annotations
    annotations : FxHashMap<Group, GroupData>,

    /// Next fresh group
    /// INVARIANT any group >= fresh_group is fresh
    fresh_group : Group, 
}

impl PartialEq for Eg {
    fn eq(&self, other: &Self) -> bool {
        // FIXME: this is too strong for loops; renaming the groups should have no effect
        self.parents == other.parents && 
        self.children == other.children && 
        self.live_regions == other.live_regions && 
        self.annotations == other.annotations 
    }
}

impl Eq for Eg {}

impl Default for Eg {
    fn default() -> Self {
        Self {
            parents: Default::default(),
            children: Default::default(),
            live_regions: Default::default(),
            annotations: Default::default(),
            fresh_group: 0,
        }
        
    }
}

impl Eg {
    fn gen_fresh_group (self: &mut Self) -> Group {
        let r = self.fresh_group;
        self.fresh_group += 1;
        return r;
    }

    /// Given a vertex X and children C, add the shape
    ///     X --[expire X]--> C
    ///  to the graph. X must exist in the graph already. 
    pub(crate) fn issue_group(self: &mut Self, vertex: Vertex, children: FxHashSet<Vertex>) -> Group {
        assert!(self.live_regions.contains(&vertex));
        let group = self.gen_fresh_group();
        assert!(self.annotations.insert(group, GroupData::basic_data(vertex)).is_none());
        assert!(self.children.insert(group, children).is_none());
        assert!(self.parents.insert(group, [vertex].into_iter().collect::<_>()).is_none()); 
        return group;
    }

    fn hyperpath_to (&self, target : Vertex) -> (FxHashSet<Vertex>, FxHashSet<Group>) {
        println!(" ** Trying to find the hyperpath to {:?}", target);
        let mut work_to_do : Vec<_> = vec![target];
        let mut def_expired_leaves : FxHashSet<Vertex> = Default::default();
        let mut def_expired_groups : FxHashSet<Group> = Default::default();

        // Traverse the graph backwards, collecting all the group annotations along the way 

        // FIXME: I'm like 99% sure this is not right
        // Conceptually it's pretty simple but there are lots of problems with hyperpaths

        while let Some(next_goal) = work_to_do.pop() {
            let groups_to_remove = self.children.iter().filter(|(k, v)| v.contains(&next_goal)).map(|x| *x.0).collect::<Vec<_>>(); 
            for p in groups_to_remove.into_iter() {
                def_expired_groups.insert(p);

                let parents1 = self.parents.get(&p).unwrap();

                // Add the parents to the list of goals
                for p in parents1.iter() {
                    if !self.is_leaf(*p) {
                        work_to_do.push(p.clone());
                    } else {
                        def_expired_leaves.insert(p.clone());
                    }
                } 
            }
        }
        return (def_expired_leaves, def_expired_groups);
    }


    // Unpicks as much as possible from a branch. Collects the annotations, and the net to- and from-vertices.
    fn expire_for_coupling(&mut self, expire_leaves : FxHashSet<Vertex>) -> (FxHashSet<Vertex>, FxHashSet<Vertex>, Vec<Annotation>) {
        let mut net_leaf_vertices : FxHashSet<Vertex> = Default::default(); 
        let mut net_target_vertices : FxHashSet<Vertex> = Default::default(); 
        let mut annotations : Vec<Annotation> = vec![];
        while let Some(grp) = self.try_find_dead_group(&expire_leaves) {
            for p in self.parents.remove(&grp).unwrap().into_iter() {
                net_leaf_vertices.insert(p);
            }
            for c in self.children.remove(&grp).unwrap().into_iter() {
                net_target_vertices.insert(c);
            }
            annotations.append(&mut self.annotations.remove(&grp).unwrap().annotations.unwrap()); // FIXME this unwrap should have a default case for coupled edges
        }
        let common = net_leaf_vertices.intersection(&net_target_vertices).cloned().collect::<FxHashSet<_>>();
        net_leaf_vertices.retain(|x| !common.contains(x));
        net_target_vertices.retain(|x| !common.contains(x));
        return (net_leaf_vertices, net_target_vertices, annotations);
    }


    pub(crate) fn couple(v: Vec<(ControlFlowFlag, Self)>) -> Self {
        println!("---------------------------------------- coupling ----------------------------------------");

        let mut m : FxHashMap<ControlFlowFlag, Self> = Default::default();
        for (f, g) in v.into_iter() {
            println!("graph {:?}:", f);
            println!("{}\n", g.pretty());
            m.insert(f, g);
        }

        // FIXME: This map be our progress measure for the loop
        // FIXME: Include frozen vertices
        // Get a vertex which is a leaf in both branches 
        let mut leaves = m.iter().map(|(_, v)| v.leaves().into_iter().map(|v| *v).collect::<Vec<_>>()).next().unwrap();
        for (_, g) in m.iter() {
            leaves.retain(|v| g.is_leaf(*v));
        }
        println!("common leaves: {:?}", leaves);


        // Figure out what we can reach in both graphs... there has to be at least one or else Polonius would mark all remaining origins as dead
        let mut common_directly_blocked= m.iter().next().map(|(_, x)| x.live_regions.iter().cloned().collect::<Vec<_>>()).unwrap();
        for (_, g) in m.iter() {
            let b = g.directly_blocked();
            common_directly_blocked.retain(|x| b.contains(x));
            common_directly_blocked.retain(|x| !g.is_leaf(*x));
        }
        println!("common directly blocked: {:?}", common_directly_blocked);

        let target = common_directly_blocked[0];  
        println!("coupling for : {:?}", target);

        // Figure out the part of the graph which definitely has to expure to obtain target 
        // If an origin has to expure to obtain target in _any_ branch, it must expire at the same time in _all_ branches. 

        let mut del : FxHashSet<Vertex> = Default::default();
        for (_ , g) in m.iter() {
            for d in  g.clone().hyperpath_to(target).0.into_iter() {
                del.insert(d);
            }
        }
        println!("definitely expired leaves: {:?}", del);

        // Now, in all graphs, expire all definitely expired leaves and unpick all dead branches as much as possible. 
        for (_, g) in m.iter_mut() {
            let (to, from, anns) = g.expire_for_coupling(del.clone());
            println!("efc {:?} // {:?} // {:?}", to, from, anns);

            // Update the leaf set of each branch

            // Keep track of the annotations & gained caps into a new map here? 
        }

        todo!();


        // Ensure the 
        // If a vertex is gained 




        println!("------------------------------------------------------------------------------------------");
        unimplemented!();
    }

    pub(crate) fn add_vertex(&mut self, vertex: Vertex) {
        assert!(self.live_regions.insert(vertex));
    }

    pub(crate) fn include_vertex(&mut self, vertex: Vertex) {
        if !self.live_regions.contains(&vertex) {
            self.live_regions.insert(vertex);
        }
    }

    // Determine if a vertex is a "root": one which is not blocking anything else
    // fn is_root(&self, v: Vertex) -> bool{
    //     self.parents.iter().all(|(_, parents)| !parents.contains(&v))
    // }

    // Determine if a vertex is a "leaf": one which is not blocked by anything
    fn is_leaf(&self, v: Vertex) -> bool {
        self.children.iter().all(|(_, children)| !children.contains(&v))
    }

    fn leaves(&self) -> Vec<&Vertex> {
        self.live_regions.iter().filter(|v| self.is_leaf(**v)).collect::<Vec<_>>()
    }

    /// Search for a vertex which is a dead leaf
    fn try_find_dead_leaf(&mut self) -> Option<Vertex> {
        self.live_regions.iter().cloned().find(|v1| self.is_leaf(*v1) && v1.tag.is_some())
    }

    /// Search for a group whose leaves are all dead or contained inside some allowed set 
    fn try_find_dead_group(&mut self, allowed : &FxHashSet<Vertex>) -> Option<Group> {
        // How to I fmap
        self.parents.iter().find(|(g, ps)| ps.iter().all(|p| p.is_tagged() || allowed.contains(p))).map(|x| *x.0)
    }

    fn tag_live_vertex(&mut self, v: RegionVid, location: Location) {
        for (_, parents) in self.parents.iter_mut() {
            // FIXME probably not a good idea to use a HashSet
            *parents = parents.iter().cloned().map(|mut p| {
                if v == p.region  { p.tag_safe(location) }
                p }).collect();
        }
        for (_, children) in self.children.iter_mut() {
            // FIXME probably not a good idea to use a HashSet
            *children = children.iter().cloned().map(|mut c| {
                if v == c.region  { c.tag_safe(location) }
                c }).collect();
        }
        for (_, groupdata) in self.annotations.iter_mut() {
            groupdata.tag(v, location);
        }
        if self.live_regions.contains(&Vertex::untagged(v)) {
            self.live_regions.remove(&Vertex::untagged(v));
            self.live_regions.insert(Vertex {region: v, tag: Some(location)});
        }
    }


    pub(crate) fn directly_blocked(&self) -> FxHashSet<Vertex> {
        let mut working_set = self.leaves().into_iter().cloned().collect::<FxHashSet<Vertex>>(); 
        // If there's an edge A->B, where
        //  A is contained in the working set
        //  every element is a leaf, or dead,
        //  then add B to the set and continue 
        let mut done = false;
        'outer: while !done {
            for (g, ps) in self.parents.iter() {
                if ps.iter().all(|p| working_set.contains(p) && (p.is_tagged() || self.is_leaf(*p))) && (!self.children.get(g).unwrap().iter().all(|c| working_set.contains(c))){
                    for c in self.children.get(g).unwrap() {
                        working_set.insert(c.clone());
                    }
                    continue 'outer;
                } 
            }
            done = true;
        }
        return working_set;
    }

    pub(crate) fn expire_except(&mut self, location: Location, to_retain: Vec<RegionVid>) {
        // Figure out which lifetimes need to get expired
        let mut to_tag = self.live_regions.iter().cloned().filter(|v| v.tag.is_none() && !to_retain.contains(&v.region)).map(|v| v.region).collect::<Vec<_>>();

        // Every expiry should remove at least one edge from some expiry group
        // If that edge is the last in the expire group, that group "expires"

        // step 1: tag all of the vertices that aren't live in the graph

        for e in to_tag.iter() {
            println!("\t\t\t------------------------------------------------------------ EMIT: rename lifetime {:?} as {:?}@{:?} ...", e, e, location);
            self.tag_live_vertex(*e, location)
        }

        // step 2: repeatedly expire groups whose LHS are dead leaves (steps 2 and 3 could probably be combined if we cange around the order)
        while let Some(dead_leaf) = self.try_find_dead_leaf() {
            // Remove the dead leaf vertex, and all edges it is a parent of (we do not need to look for it's parents)
            // println!("\t\t\t------------------------------------------------------------ EMIT: obtain permissions for {:?}", dead_leaf);
            self.live_regions.remove(&dead_leaf);

            for (_, parents) in self.parents.iter_mut() {
                parents.remove(&dead_leaf);
            }

            // When all parents of a group are removed, we remove that group 
            let mut groups_to_expire = vec![];
            for (group, parents) in self.parents.iter() {
                if parents.len() == 0 {
                    groups_to_expire.push(group.clone());
                }
            }
            for g in groups_to_expire.into_iter() {
                println!("\t\t\t------------------------------------------------------------ EMIT: apply to DAG {:?}", self.annotations.get(&g).unwrap().annotations);
                self.annotations.remove(&g);
                self.children.remove(&g);
                self.parents.remove(&g);
            }
        }
    }


}


/// Pretty printing 
impl Eg { 
    pub fn pretty(&self) -> String {

        // Print the groups
        format!("| V: {:?} \n\
                 | E: {:?} \n\
                 {}", 
            self.live_regions.iter().collect::<Vec<_>>(),
            self.annotations.keys().collect::<Vec<_>>(),
            self.annotations
                .iter()
                .fold("".to_string(), |mut e, (k, v)| 
                    { for p in self.parents.get(k).unwrap().iter() {
                        e = format!("{}| {:?} ({:?} -> {:?}): {:?}\n", e, k, p, self.children.get(k).unwrap(), v.annotations);
                        }
                      e 
                    }))
    }
}