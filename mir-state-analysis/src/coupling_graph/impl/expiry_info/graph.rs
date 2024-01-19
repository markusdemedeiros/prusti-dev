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

    pub(crate) fn couple(v: Vec<(ControlFlowFlag, Self)>) -> Self {
        todo!();
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

    /// Search for a vertex which is a dead leaf
    fn try_find_dead_leaf(&mut self) -> Option<Vertex> {
        self.live_regions.iter().cloned().find(|v1| self.is_leaf(*v1) && v1.tag.is_some())
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


    pub(crate) fn expire_except(&mut self, location: Location, to_retain: Vec<RegionVid>) {
        // Figure out which lifetimes need to get expired
        let mut to_tag = self.live_regions.iter().cloned().filter(|v| v.tag.is_none() && !to_retain.contains(&v.region)).map(|v| v.region).collect::<Vec<_>>();

        // Every expiry should remove at least one edge from some expiry group
        // If that edge is the last in the expire group, that group "expires"



        // emitting a "freeze" instruction and putting a "thaw" instruction into the expiry group
        // if it's a leaf, emit the "freeze" instruction. if not, place it at the end of any sequences it's the parent of.
        // then tag it in the graph


        // step 1: tag all of the vertices that aren't live in the graph

        for e in to_tag.iter() {
            println!("\t\t\t------------------------------------------------------------ EMIT: rename lifetime {:?} as {:?}@{:?} ...", e, e, location);
            self.tag_live_vertex(*e, location)
        }

        // step 2: repeatedly expire groups whose LHS are dead leaves 
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