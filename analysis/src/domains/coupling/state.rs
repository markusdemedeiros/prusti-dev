// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// use log::info;

use crate::{
    abstract_interpretation::{AbstractState, AnalysisResult},
    mir_utils::{is_prefix, Place},
};
use itertools::Itertools;
use prusti_rustc_interface::{
    borrowck::{consumers::RustcFacts, BodyWithBorrowckFacts},
    middle::{
        mir,
        mir::{BasicBlock, Location},
    },
    polonius_engine::FactTypes,
};
use serde::{
    ser::{SerializeMap, SerializeStruct},
    Serialize, Serializer,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    sync::Arc,
};

use super::{btree_replace, FactTable, IntroStatement, OriginLHS};

// These types are stolen from Prusti interface
pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;

#[derive(PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub struct Tagged<Data, Tag> {
    pub data: Data,
    pub tag: Option<Tag>,
}

impl<Data, Tag> Tagged<Data, Tag> {
    // Tag a place if it is not already tagged
    fn tag(&mut self, t: Tag) {
        if self.tag.is_none() {
            self.tag = Some(t);
        }
    }

    fn untagged(data: Data) -> Self {
        Self { data, tag: None }
    }

    fn tagged(data: Data, tag: Tag) -> Self {
        Self {
            data,
            tag: Some(tag),
        }
    }

    pub fn is_tagged(&self) -> bool {
        self.tag.is_some()
    }
}

impl<Data: fmt::Debug, Tag: fmt::Debug> fmt::Debug for Tagged<Data, Tag> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.tag {
            Some(t) => write!(f, "{:?}@{:?}", self.data, t),
            None => write!(f, "{:?}", self.data),
        }
    }
}

/// A CDGNode represents a permission (a node in the coupling graph)
/// A CDGNode is one of
///     - A Place: a mir_utils::Place, tagged by a point
///     - A Borrow: a Loan, tagged by a point
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum CDGNode<'tcx> {
    Place(Tagged<Place<'tcx>, Location>),
    Borrow(Tagged<Loan, Location>),
}

impl<'tcx> CDGNode<'tcx> {
    /// Tags a node at a point, if it isn't already untagged
    pub fn kill(mut self, l: &Location) -> Self {
        match &mut self {
            CDGNode::Place(p) => p.tag(*l),
            CDGNode::Borrow(b) => b.tag(*l),
        }
        self
    }

    /// Determine if a kill should tag the current place:
    ///     - A borrow should be tagged only if it is untagged, and equal to to_kill
    ///     - A place should be tagged only if it is untagged, and to_kill is its prefix
    pub fn should_tag(&self, to_kill: &CDGNode<'tcx>) -> bool {
        match (self, to_kill) {
            (CDGNode::Place(p_self), CDGNode::Place(p_kill)) => {
                p_self.tag.is_none() && p_kill.tag.is_none() && is_prefix(p_self.data, p_kill.data)
            }
            (l0 @ CDGNode::Borrow(_), l1 @ CDGNode::Borrow(_)) => l0 == l1,
            _ => false,
        }
    }

    pub fn is_tagged(&self) -> bool {
        match self {
            CDGNode::Place(x) => x.is_tagged(),
            CDGNode::Borrow(x) => x.is_tagged(),
        }
    }
}

impl<'tcx> Into<CDGNode<'tcx>> for OriginLHS<'tcx> {
    /// Turn an OriginLHS into a CDGNode by creating a new untagged node
    fn into(self) -> CDGNode<'tcx> {
        match self {
            OriginLHS::Place(p) => CDGNode::Place(Tagged::untagged(p)),
            OriginLHS::Loan(l) => CDGNode::Borrow(Tagged::untagged(l)),
        }
    }
}

impl<'tcx> fmt::Debug for CDGNode<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CDGNode::Place(tp) => write!(f, "{:?}", tp),
            CDGNode::Borrow(tb) => write!(f, "{:?}", tb),
        }
    }
}

/// The smallest amount of metadata needed to calculate the coupling graph
#[derive(Clone, PartialEq, Eq)]
pub enum SignatureKind {
    Subgraph(Tagged<Region, Location>),
    // The lowest nodes in the graph are never coupled, so coupled edges are always
    // above some other region.
    // Field 0: The location we are joining into.
    // Field 1: The locations we are joining from
    // Field 2: The set of edges this coupled edge is a parent to
    Coupled(
        BasicBlock,
        BTreeSet<BasicBlock>,
        BTreeSet<Tagged<Region, Location>>,
    ),
    Owned,
}

/// A data structure representing an abstract exchange of capabilities
/// associated to the expiry of an origin.
#[derive(Clone, PartialEq, Eq)]
pub struct OriginSignature<'tcx> {
    leaves: BTreeSet<CDGNode<'tcx>>,
    roots: BTreeSet<CDGNode<'tcx>>,
    kind: SignatureKind,
}

impl<'tcx> OriginSignature<'tcx> {
    /// Tags all untagged places which have to_tag as a prefix in a set of nodes
    fn tag_in_set(set: &mut BTreeSet<CDGNode<'tcx>>, location: &Location, to_tag: &CDGNode<'tcx>) {
        let mut to_replace: Vec<CDGNode<'tcx>> = vec![];
        for node in set.iter() {
            if node.should_tag(to_tag) {
                to_replace.push((*node).clone())
            }
        }
        for node in to_replace.iter() {
            btree_replace(set, node, node.clone().kill(location));
        }
    }

    /// Tags all untagged places which have to_tag as a prefix
    pub fn tag(&mut self, location: &Location, to_tag: &CDGNode<'tcx>) {
        Self::tag_in_set(&mut self.roots, location, to_tag);
        Self::tag_in_set(&mut self.leaves, location, to_tag);
    }
}

impl<'tcx> fmt::Debug for OriginSignature<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?} -[{}]-* {:?}",
            self.leaves.iter().collect::<Vec<_>>(),
            match &self.kind {
                SignatureKind::Subgraph(o) => format!("branch {:?}", o),
                SignatureKind::Coupled(bb_to, bbs_from, parent_to) =>
                    format!("couple {:?}~>{:?}; {:?}", bbs_from, bb_to, parent_to),
                SignatureKind::Owned => format!("owned"),
            },
            self.roots.iter().collect::<Vec<_>>()
        )?;
        Ok(())
    }
}

#[derive(Clone, Default, PartialEq, Eq)]
pub struct OriginMap<'tcx> {
    pub map: BTreeMap<Tagged<Region, Location>, OriginSignature<'tcx>>,
    // leaves: BTreeSet<OriginLHS<'tcx>>,
}

impl<'tcx> fmt::Debug for OriginMap<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (k, v) in self.map.iter() {
            writeln!(f, "{:?}: {:?}", k, v)?;
        }
        Ok(())
    }
}

impl<'tcx> OriginMap<'tcx> {
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    // Add a new borrow root to the tree
    pub fn new_borrow(&mut self, bw_from_place: Place<'tcx>, bw_ix: Loan, bw_origin: &Region) {
        assert!(self.map.get(&Tagged::untagged(*bw_origin)).is_none());
        let sig = OriginSignature {
            leaves: [CDGNode::Borrow(Tagged::untagged(bw_ix))].into(),
            roots: [CDGNode::Place(Tagged::untagged(bw_from_place))].into(),
            kind: SignatureKind::Owned,
        };
        self.map.insert(Tagged::untagged(*bw_origin), sig);
    }

    // Add a new
    pub fn new_shared_subgraph(
        &mut self,
        subgraph_node: CDGNode<'tcx>,
        subgraph_origin: &Region,
        supgraph_node: CDGNode<'tcx>,
        supgraph_origin: &Region,
    ) {
        // For connectivity
        assert!(self.map.get(&Tagged::untagged(*supgraph_origin)).is_none());
        assert!(self.map.get(&Tagged::untagged(*subgraph_origin)).is_some());
        assert!(self
            .map
            .get(&Tagged::untagged(*subgraph_origin))
            .unwrap()
            .leaves
            .contains(&subgraph_node));

        let sig = OriginSignature {
            leaves: [supgraph_node].into(),
            roots: [subgraph_node].into(),
            kind: SignatureKind::Subgraph(Tagged::untagged(*subgraph_origin)),
        };
        self.map.insert(Tagged::untagged(*supgraph_origin), sig);
    }

    pub fn tag_origins(&mut self, location: &Location, origin: Region) {
        // Change the key for this origin to be a tagged version
        if let Some(sig) = self.map.remove(&Tagged::untagged(origin)) {
            // Reinsert the new edge
            self.map
                .insert(Tagged::tagged(origin, *location), sig.clone());

            // I'm not really sure about this to be completely honest
            for cap in sig.leaves.iter() {
                match cap {
                    CDGNode::Place(_) => self.tag_node(location, cap),
                    CDGNode::Borrow(_) => match sig.kind {
                        SignatureKind::Subgraph(_) => self.tag_node(location, cap),
                        SignatureKind::Coupled(_, _, _) => self.tag_node(location, cap),
                        SignatureKind::Owned => (),
                    },
                }
            }
        }

        // Change all subgraphs that refer to this graph to be tagged as well
        for (_, sig) in self.map.iter_mut() {
            if let SignatureKind::Subgraph(sbg) = &(sig.kind) {
                if *sbg == Tagged::untagged(origin) {
                    sig.kind = SignatureKind::Subgraph(Tagged::tagged(origin, *location));
                }
            }
        }
    }

    pub fn tag_node(&mut self, location: &Location, node: &CDGNode<'tcx>) {
        for (_, sig) in self.map.iter_mut() {
            sig.tag(location, node);
        }
    }

    // Get the LHS of all live origins
    pub fn get_live_lhs(&self) -> BTreeSet<CDGNode<'tcx>> {
        let mut ret = BTreeSet::new();
        for (o, sig) in self.map.iter() {
            if !o.is_tagged() {
                for l in sig.leaves.iter() {
                    ret.insert(l.clone());
                }
            }
        }
        return ret;
    }

    // Get the LHS of all origins
    pub fn get_all_lhs(&self) -> BTreeSet<CDGNode<'tcx>> {
        let mut ret = BTreeSet::new();
        for (_, sig) in self.map.iter() {
            for l in sig.leaves.iter() {
                ret.insert(l.clone());
            }
        }
        return ret;
    }

    pub fn get_all_rhs(&self) -> BTreeSet<CDGNode<'tcx>> {
        let mut ret = BTreeSet::new();
        for (_, sig) in self.map.iter() {
            for l in sig.roots.iter() {
                ret.insert(l.clone());
            }
        }
        return ret;
    }

    // Get the roots of the tree
    // Assumes the tree is correctly connected (eg. in the correct packing state)
    // Hoenstly both this and leaves should be precomputed since they rarely change
    // so don't need to always be recomputed
    pub fn get_roots(&self) -> BTreeSet<CDGNode<'tcx>> {
        let mut ret = BTreeSet::new();
        let lr = self.get_all_lhs();
        for (_, sig) in self.map.iter() {
            for r in sig.roots.iter() {
                if !lr.contains(r) {
                    ret.insert(r.clone());
                }
            }
        }
        return ret;
    }

    pub fn get_leaves(&self) -> BTreeSet<CDGNode<'tcx>> {
        let mut ret = BTreeSet::new();
        let rr = self.get_all_rhs();
        for (_, sig) in self.map.iter() {
            for r in sig.leaves.iter() {
                if !rr.contains(r) {
                    ret.insert(r.clone());
                }
            }
        }
        return ret;
    }

    // A _parent_ is a live place node that is blocking another node, with no live
    // nodes in between. Eg.
    //
    //  x --> y --> w@bb1[2] --> z
    //
    // y is a parent of z. w@bb1[2] is not a parent of z because it is not live,
    // and x is not a parent of z because of y. At a join in the coupling graph,
    // parents are preserved between branches. That is,
    //
    //    a --> b --> x    join    b --> a --> x
    //
    // is impossible (due to the eager kills of origins in Polonius).
    //
    // Parents are supposed to represent the finest possible subgraphs that
    // we can couple. A node can have any number of parents. For example,
    // in the graph
    //
    //    x --coupled--> {y, z}
    //    w --coupled--> {y, z}
    //
    // both x and w are parents of y. An invariant of the coupling graph is that
    // all possible parents must expire before a resource can be regained. As such,
    // if we consider coupled edges to be equal, the coupling graph should form a
    // directed hypertree where the edges are parent-child relationships*. The
    // process of coupling amounts to abstracting over all of the possible parents
    // across several branches so that this invariant is maintained.
    //
    //
    // *in the case of exlusive capabilities, anyways.

    // if root is a root, there should be exactly one edge in the coupling graph that directly blocks it.
    // fixme: this needs to ger refactored to return many possible parents! (a coupled parent)
    fn get_direct_parent(
        &self,
        root: &CDGNode<'tcx>,
    ) -> Vec<(Tagged<Region, Location>, OriginSignature<'tcx>)> {
        self.map
            .iter()
            .filter(|(_, sig)| sig.roots.contains(root))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect::<Vec<_>>()

        // if let [(k, v)] = possible_parents[..] {
        //     return (k.clone(), v.clone());
        // } else {
        //     panic!("excess parents: {:?}", possible_parents);
        // }
    }

    // Get a list of origins to expire in order to end up at a root
    // Returns
    //  - a list of origins to expire
    //  - the leaves of that set of origins
    //  - the roots of that set of origins, which is a superset of the ``root``
    pub fn get_parent(
        &self,
        roots: BTreeSet<CDGNode<'tcx>>,
    ) -> (
        Vec<Tagged<Region, Location>>,
        BTreeSet<CDGNode<'tcx>>,
        BTreeSet<CDGNode<'tcx>>,
    ) {
        let mut ret_origins: Vec<_> = Vec::new();
        let mut ret_roots: BTreeSet<CDGNode<'tcx>> = roots.clone();
        let mut ret_leaves: BTreeSet<CDGNode<'tcx>> = BTreeSet::new();

        let graph_leaves = self.get_leaves();

        let mut roots_todo = roots.clone();
        // Traverse the graph until working_roots are all
        //  - not in roots
        //  - is a leaf; or is untagged.
        loop {
            // Move out all of the done nodes
            for node in roots_todo.iter() {
                if !roots.contains(node) && (graph_leaves.contains(node) || !node.is_tagged()) {
                    ret_leaves.insert(node.clone());
                }
            }
            roots_todo.retain(|node| {
                !(!roots.contains(node) && (graph_leaves.contains(node) || !node.is_tagged()))
            });

            // Check to see if we're done
            if roots_todo.is_empty() {
                break;
            }

            // If we're not done, get the edge's direct parent.
            let goal_working = roots_todo.pop_first().unwrap();
            for (tagged_region, sig) in self.get_direct_parent(&goal_working).iter() {
                // For all the roots of this edge, either remove a goal (if it can) or add it to the global effect
                for r in sig
                    .roots
                    .iter()
                    .filter(|n| !roots_todo.contains(n) && **n != goal_working)
                {
                    ret_roots.insert(r.clone());
                }
                roots_todo.retain(|n| !sig.roots.contains(n));

                // Add all new goals for this edge
                roots_todo = roots_todo.union(&sig.leaves).cloned().collect();

                // Record this expiry.
                ret_origins.push(tagged_region.clone());

                // remove all roots of this edge from the total effect
                for l in sig.roots.iter() {
                    ret_leaves.remove(l);
                }
            }
        }
        return (ret_origins, ret_roots, ret_leaves);
    }
}

// A coupling graph
#[derive(Clone, Default, PartialEq, Eq, Debug)]
pub struct CDG<'tcx> {
    pub origins: OriginMap<'tcx>,
    // Also include: a structure that translates CoupledBrorrowIndicies
    pub origin_contains_loan_at_invariant: bool,
}

impl<'tcx> CDG<'tcx> {
    // pub fn get_roots(&self) -> BTreeSet<
}

/// Extra data to add to a state to make joins location-depdent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StateLocation {
    BeforeProgram,
    Joining(BasicBlock, BasicBlock),
    InsideBB(BasicBlock),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ElimCommand<'tcx> {
    // Take a place from the free PCS (and kill it in the graph)
    Consume(CDGNode<'tcx>),
    // apply all annotations associated to a region, except possibly coupled edges
    // if there are other coupled still live. Regains a set of nodes in the
    // free PCS
    Expire(Tagged<Region, Location>, BTreeSet<CDGNode<'tcx>>),
}

/// CouplingState consists of
///     - A CouplingGraph, representing the current
///     - References to the context mir and fact_table
#[derive(Clone)]
pub struct CouplingState<'facts, 'mir: 'facts, 'tcx: 'mir> {
    pub coupling_graph: CDG<'tcx>,
    // Location this state applies to (possibly in-between basic blocks)
    pub loc: StateLocation,

    /// Coupling commands:
    ///  indexed by to-bb, from-bb, and the coupled edge to create (identified by the set it blocks)
    ///  the RB DAG must abstract over the specified origins
    pub coupling_commands:
        BTreeMap<(BasicBlock, BasicBlock, BTreeSet<CDGNode<'tcx>>), Vec<Tagged<Region, Location>>>,

    pub elim_commands: Vec<ElimCommand<'tcx>>,

    // also include: annotations at this location:
    // Also include: invariant checks?
    pub(crate) mir: &'mir BodyWithBorrowckFacts<'tcx>,
    pub(crate) fact_table: &'facts FactTable<'tcx>,
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> CouplingState<'facts, 'mir, 'tcx> {
    pub(crate) fn new_empty(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        fact_table: &'facts FactTable<'tcx>,
    ) -> Self {
        Self {
            coupling_graph: Default::default(),
            loc: StateLocation::BeforeProgram,
            coupling_commands: BTreeMap::new(),
            elim_commands: Vec::new(),
            fact_table,
            mir,
        }
    }

    pub(crate) fn new_bottom(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        fact_table: &'facts FactTable<'tcx>,
    ) -> Self {
        Self {
            coupling_graph: Default::default(),
            loc: StateLocation::BeforeProgram,
            coupling_commands: BTreeMap::new(),
            elim_commands: Vec::new(),
            fact_table,
            mir,
        }
    }
    pub(crate) fn apply_terminator_effect(
        &self,
        location: Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self)>> {
        let mut new_state = self.clone();
        new_state.coupling_commands = Default::default();
        new_state.elim_commands = Default::default();
        new_state.cdg_step(location)?;

        let joining_from = location.block;
        let terminator = self.mir.body[location.block].terminator();
        Ok(terminator
            .successors()
            .into_iter()
            .map(|bb| {
                let mut ns = new_state.clone();
                ns.loc = StateLocation::Joining(joining_from, bb);
                (bb, ns)
            })
            .collect())
    }

    pub(crate) fn apply_statement_effect(&mut self, location: Location) -> AnalysisResult<()> {
        self.coupling_commands = Default::default();
        self.elim_commands = Default::default();
        self.loc = StateLocation::InsideBB(location.block);
        self.cdg_step(location)
    }

    /// The main interpretation of Polonius facts
    fn cdg_step(&mut self, location: Location) -> AnalysisResult<()> {
        // expire any origins which expired after any predecessor
        // we assume if an origin expures at the end of ONE predecessor, it expures at the end of ALL of them.
        // keep in mind, this could be a no-op!
        // (recording the necessary changes in leaves as consume and expire statements)
        self.apply_origins(&location)?;

        println!("(loc: {:?})", self.loc);
        println!(
            "[debug@{:?}]\n{:?}\n",
            location, self.coupling_graph.origins
        );

        // get the preconditions for the change in nodes at the location
        let (pre_leaves, _) = match self.fact_table.delta_leaves.get(&location) {
            Some(x) => x.clone(),
            None => (Vec::new(), Vec::new()),
        };

        // add repack edges to ensure thre preconditions are met
        self.ensure_contains_leaves_for(&pre_leaves);

        // apply the rewrite steps to the coupling graph
        self.apply_rewrite(&location);

        Ok(())
    }

    // fixme: For now we're just going to assume we never get contradictory packing requirements, and won't check that.
    fn ensure_contains_leaves_for(&mut self, to_ensure: &Vec<OriginLHS<'tcx>>) {
        for req in to_ensure.iter() {
            let matching_origin = self
                .fact_table
                .origins
                .get_origin(&self.mir.body, req.clone());
            if matching_origin == None {
                // stupid hack. This is for borrows of owned data.
                continue;
            }
            let matching_origin = matching_origin.unwrap();
            let matching_leaves = self
                .coupling_graph
                .origins
                .map
                .get(&Tagged::untagged(matching_origin))
                .unwrap()
                .leaves
                .clone();

            // I'm also going to leave actual unpacking completely unimplemented (lol).
            // Check that the corresponding CDGNode associate to req is contained in the matching_leaves.
            if !matching_leaves.contains(&Into::<CDGNode<'tcx>>::into(req.clone())) {
                println!("need to repack! matching_leaves:");
                println!("{:?}", matching_leaves);
                println!("req: {:?}", req);
                panic!();
            }
        }
    }

    // As long as we don't need intermediate repacks between these operations (or they are
    // written down beforehand) we can always assume that the appropriate nodes are in
    // the graph(s).
    fn apply_rewrite(&mut self, location: &Location) {
        for x in self.fact_table.graph_operations.get(location).iter() {
            for s in x.iter() {
                match s {
                    IntroStatement::Kill(node) => {
                        self.coupling_graph
                            .origins
                            .tag_node(location, &((*node).clone().into()));
                    }
                    IntroStatement::Assign(asgn_from_node, asgn_to_node) => {
                        let asgn_from_origin = self
                            .fact_table
                            .origins
                            .get_origin(&self.mir.body, (*asgn_from_node).clone())
                            .unwrap();
                        let asgn_to_origin = self
                            .fact_table
                            .origins
                            .get_origin(&self.mir.body, OriginLHS::Place(*asgn_to_node))
                            .unwrap();
                        if asgn_from_origin == asgn_to_origin {
                            // This should rewrite the LHS of a place.
                            // I'm not sure if it ever comes up, though...
                            //    x=&mut x?
                            //    x.f=&mut x?
                            //    Maybe something w/ coupling?
                            unimplemented!("assignment to self places not implemented yet");
                        } else {
                            self.coupling_graph.origins.new_shared_subgraph(
                                (*asgn_from_node).clone().into(),
                                &asgn_from_origin,
                                CDGNode::Place(Tagged::untagged(*asgn_to_node)),
                                &asgn_to_origin,
                            );
                        }
                    }
                    IntroStatement::Reborrow(rb_from_place, bw_ix, rb_from_origin) => {
                        let rb_into_origin = self
                            .fact_table
                            .origins
                            .get_origin(&self.mir.body, OriginLHS::Loan(*bw_ix))
                            .unwrap();
                        assert!(self
                            .coupling_graph
                            .origins
                            .map
                            .get(&Tagged::untagged(rb_into_origin))
                            .is_none());
                        // Rewrite the graph to internally repack it here, if that's needed

                        self.coupling_graph.origins.new_shared_subgraph(
                            CDGNode::Place(Tagged::untagged(*rb_from_place)),
                            rb_from_origin,
                            CDGNode::Borrow(Tagged::untagged(*bw_ix)),
                            &rb_into_origin,
                        );
                    }
                    IntroStatement::Borrow(bw_from_place, bw_ix) => {
                        let bw_into_origin = self
                            .fact_table
                            .origins
                            .get_origin(&self.mir.body, OriginLHS::Loan(*bw_ix))
                            .unwrap();
                        self.coupling_graph.origins.new_borrow(
                            *bw_from_place,
                            *bw_ix,
                            &bw_into_origin,
                        );
                    }
                }
            }
        }
    }

    /// Expire non-live origins, and add new live origins
    fn apply_origins(&mut self, location: &Location) -> AnalysisResult<()> {
        // Get the set of origins at a point from the origin_contains_loan_at fact
        if let Some(ogs) = self.fact_table.origin_expires_before.get(location).clone() {
            let mut done = ogs.is_empty();
            while !done {
                // 1. We need an order in which to expiure these origins. This didn't matter in the last
                // formulation of the coupling graph, but it does in this one.
                // We assert that the coupling graph is tree-structured, and that tree leaves expire first
                //    (the exceptions to this rule become coupled)

                // An origin x is a tree-leaf when no other branch is SharedSubgraph(x)?
                // fixme: do coupled edges abstract over ALL origins below them? If not, change this match.
                match self
                    .coupling_graph
                    .origins
                    .map
                    .keys()
                    // Find all tree-leaves
                    .filter(|x| {
                        self.coupling_graph
                            .origins
                            .map
                            .iter()
                            .all(|(_, sig)| match &sig.kind {
                                SignatureKind::Subgraph(y) => y != *x,
                                SignatureKind::Coupled(_, _, children) => !children.contains(x),
                                SignatureKind::Owned => true,
                            })
                    })
                    // We are allowed to expire the tree-leaves that are tagged OR are in OGS.
                    .filter(|x| x.tag.is_some() || ogs.contains(&x.data))
                    .cloned()
                    .next()
                {
                    Some(tree_leaf) => {
                        println!("expiring the origin: {:?}", tree_leaf);
                        // fixme: emit consume and expire statements for that edge here.
                        // Coupled edges don't get expired until all couped edges do... but they can get removed!
                        // remove from ogs.
                        let leaf_sig = self.coupling_graph.origins.map.remove(&tree_leaf).unwrap();
                        for l in leaf_sig.leaves.iter() {
                            if !l.is_tagged() {
                                self.elim_commands.push(ElimCommand::Consume(l.clone()))
                            }
                        }
                        match &leaf_sig.kind {
                            SignatureKind::Subgraph(_) | SignatureKind::Owned => {
                                self.elim_commands.push(ElimCommand::Expire(
                                    tree_leaf.clone(),
                                    leaf_sig.roots.clone(),
                                ))
                            }
                            SignatureKind::Coupled(leaf_froms, leaf_to, _) => {
                                // Push the expiry of the coupled edge. Only regain capability if it's the last
                                // coupled edge.
                                match self
                                    .coupling_graph
                                    .origins
                                    .map
                                    .values()
                                    .filter(|sig| match &sig.kind {
                                        SignatureKind::Coupled(froms, to, _) => {
                                            froms == leaf_froms
                                                && to == leaf_to
                                                && leaf_sig.roots == sig.roots
                                        }
                                        _ => false,
                                    })
                                    .next()
                                {
                                    Some(_) => {
                                        // Expiry should not get anything back while other couple is live
                                        self.elim_commands.push(ElimCommand::Expire(
                                            tree_leaf.clone(),
                                            BTreeSet::new(),
                                        ))
                                    }
                                    None => self.elim_commands.push(ElimCommand::Expire(
                                        tree_leaf.clone(),
                                        leaf_sig.roots,
                                    )),
                                }
                            }
                        }
                        done = ogs.is_empty();
                    }
                    None => {
                        // The rest of ogs are internal, so get tagged.
                        for x in ogs.into_iter() {
                            println!("tagging the internal origin: {:?}", ogs);
                            self.coupling_graph.origins.tag_origins(location, *x);
                        }
                        done = true;
                    }
                }
            }
        }
        Ok(())
    }
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> Serialize for CouplingState<'facts, 'mir, 'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut s = serializer.serialize_struct("[coupling state]", 2)?;
        s.serialize_field("[cdg]", &self.coupling_graph)?;
        s.end()
    }
}

impl<'tcx> Serialize for CDG<'tcx> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let map = serializer.serialize_map(None)?;
        // fixme: stub
        map.end()
    }
}

impl fmt::Debug for CouplingState<'_, '_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "[cdg] {:#?}", self.coupling_graph)?;
        writeln!(f, "[loc] {:#?}", self.loc)?;
        writeln!(f, "[cpl] {:#?}", self.coupling_commands)?;
        writeln!(f, "[elm] {:#?}", self.elim_commands)
    }
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> PartialEq for CouplingState<'facts, 'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.coupling_graph == other.coupling_graph
            && self.loc == other.loc
            && self.coupling_commands == other.coupling_commands
    }
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> Eq for CouplingState<'facts, 'mir, 'tcx> {}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> AbstractState for CouplingState<'facts, 'mir, 'tcx> {
    fn is_bottom(&self) -> bool {
        self.coupling_graph.origins.map.is_empty() && self.loc == StateLocation::BeforeProgram
    }

    // Invariant: bottom join X is X
    // fixme: is it possible to join in several different ways?
    //  eg. (bb1 join bb2) join bb3   vs    bb1 join k(bb2 join bb3)?
    // If so, we might no reach a fixed point with how we're recording data here, since
    // the coupling state will not be equal between these two paths (for the def'n of
    // equality currently implemented, anyways).
    fn join(&mut self, other: &Self) {
        // Generalize to n-ary joins.
        let mut states_to_join = vec![self.clone(), other.clone()];

        // Filter out trivial cases (this is a substantial number of the joins in MIR).
        states_to_join = states_to_join
            .into_iter()
            .filter(|st| !st.is_bottom())
            .collect();
        match &states_to_join[..] {
            [] => (),
            [z] => *self = (*z).clone(),
            _ => (),
        };

        // debug
        println!("(JOIN 1 loc: {:?})", self.loc);
        println!("JOIN 1: {:?}\n", self.coupling_graph);
        println!("(JOIN 2 loc: {:?})", other.loc);
        println!("JOIN 2: {:?}\n", other.coupling_graph);

        // Begin the construction of a new coupling graph.
        let mut working_graph: OriginMap = Default::default();

        // // Make the LHS of the origins coherent (kill leaves that are in one branch but not the other)
        // let lhs = self.coupling_graph.origins.get_live_lhs();
        // if lhs != other.coupling_graph.origins.get_live_lhs() {
        //     unimplemented!("kill dead lhs in live origins");
        // }

        // Repack and kill the LHS to be coherent b
        let reference_packing_state = states_to_join[0].coupling_graph.origins.get_live_lhs();
        let reference_packing_leaves = states_to_join[0].coupling_graph.origins.get_leaves();
        assert!(
            states_to_join
                .iter()
                .all(|st| st.coupling_graph.origins.get_live_lhs() == reference_packing_state),
            "unimplemented: correctly killing LHS at join points"
        );
        assert!(
            states_to_join
                .iter()
                .all(|st| st.coupling_graph.origins.get_leaves() == reference_packing_leaves),
            "unimplemented: correctly repacking LHS's at join points"
        );

        // Save a vector of roots and leaves for later and for debugging
        let all_roots = states_to_join
            .iter()
            .map(|st| st.coupling_graph.origins.get_roots())
            .collect::<BTreeSet<_>>();
        let all_leaves = states_to_join
            .iter()
            .map(|st| st.coupling_graph.origins.get_leaves())
            .collect::<BTreeSet<_>>();

        // alt. design: we could repack _all_ LHS's to be the same here (not just leaves)
        // by adding internal pack/unpack pairs. that would simplify the analysis
        // later, at the cost some redundant repacks (possible nontermination?)

        // Save the leaves that are definitely in the PCS at this point
        // fixme: too many clones here
        let def_accessible_leaves = all_leaves
            .clone()
            .into_iter()
            .reduce(|acc, goal_set| acc.into_iter().filter(|x| goal_set.contains(x)).collect())
            .unwrap();

        // debug
        println!("roots are: {:?} ", all_roots);
        println!("leaves are: {:?} ", reference_packing_leaves);

        // The main iteration reduces a set of "goals" into capabilities we can freely apply.
        // The goals start off with the roots.
        let mut goals = states_to_join
            .iter()
            .map(|st| (st, st.coupling_graph.origins.get_roots()))
            .collect::<Vec<_>>();

        fn goal_is_done<'tcx>(
            def_accessible_leaves: &BTreeSet<CDGNode<'tcx>>,
            n: &CDGNode<'tcx>,
        ) -> bool {
            def_accessible_leaves.contains(n) || n.is_tagged()
        }

        loop {
            // filter out all of the completed goals.
            for goal_set in goals.iter_mut() {
                goal_set.1 = goal_set
                    .1
                    .iter()
                    .filter(|goal| !goal_is_done(&def_accessible_leaves, goal))
                    .cloned()
                    .collect();
            }

            // Exit condition: if we have no more goals, we are done.
            if goals.iter().all(|goal_set| goal_set.1.is_empty()) {
                break;
            }

            // Figure out the ways each goal can be directly satisfied in each graph
            // fixme: this calculation is redundant to do at each step

            let mut goal_parents: Vec<(&Self, BTreeMap<CDGNode<'tcx>, (Vec<_>, _, _)>)> =
                Default::default();
            for (couplingstate, goal_set) in goals.iter() {
                let mut ret_map = BTreeMap::default();
                for goal in goal_set.iter() {
                    ret_map.insert(
                        (*goal).clone(),
                        couplingstate
                            .coupling_graph
                            .origins
                            .get_parent([goal.clone()].into()),
                    );
                }
                goal_parents.push((couplingstate, ret_map.clone()));
            }

            // Find goals that we can complete
            // Case 1: the goals, and their parents, are identical
            //   (they were generated before the control flow split off, and were not changed).
            if let Some(same_in_all_goal) = goals
                .iter()
                .map(|x| &(x.1))
                .flatten()
                .filter(|goal| {
                    // Search for any goal whose parent is the same in all origins, by
                    // comparing to a fixed element.
                    let goal_parent_ref = goal_parents.iter().next().unwrap().1.clone();
                    goal_parents
                        .iter()
                        .all(|(_, parents_map)| parents_map.get(goal) == goal_parent_ref.get(goal))
                })
                .next()
            {
                // some parent is the same in all branches.
                println!("implement: found a match! {:?}", same_in_all_goal);

                // determine the change in goals
                let (smp_branch, smp_parents_map) = goal_parents.iter().next().unwrap();
                let (edges, goals_to_remove, goals_to_add) =
                    smp_parents_map.get(&same_in_all_goal).unwrap();

                for region in edges.into_iter() {
                    working_graph.map.insert(
                        region.clone(),
                        smp_branch
                            .coupling_graph
                            .origins
                            .map
                            .get(region)
                            .unwrap()
                            .clone(),
                    );
                }

                // Since the origins signatures are literally the same (am I checking this?) all
                // goals include all of the path's removed goals. Therefore we can remove them all.
                // Some of these assertions will fail in the case of shared borrows. Revisit it.
                for (_, goal_set) in goals.iter_mut() {
                    for completed_goal in goals_to_remove.iter() {
                        assert!(
                            goal_set.remove(completed_goal),
                            "tried to complete a goal that didn't exist"
                        );
                    }

                    for new_goal in goals_to_add.iter() {
                        assert!(
                            goal_set.insert(new_goal.clone()),
                            "tried to insert a goal that already exist"
                        );
                    }
                }

                println!(
                    "new goals: {:?} ",
                    goals.iter().map(|x| &(x.1)).collect::<Vec<_>>()
                );
            } else {
                // no match
                todo!("no match");
            }
        }

        println!("final graph:\n{:?}", working_graph);
        self.coupling_graph.origins = working_graph;

        // goal_parents is a map from a goal to (...).coupling_graph.origins.get_parent([g.clone()].into()),
        // if branch:
        //     // fixme: look for origins that
        //     //    - meet the goal
        //     //    - are the same in both
        //     //    - are the _only_ edge that meets the goal

        // else branch

        //         // No match.
        //         // Create a partition of (input/ouput)
        //         println!("no match\ngoals: {:?}", goal_parents);

        //         // Partition the set of goals using goal parents:
        //         // Elements in teh partition must be satuated wrt expiring edges

        //         // goals_preimage: map from goal to a set of resources that we can expire to get it back
        //         let mut goals_preimage: BTreeMap<CDGNode<'tcx>, BTreeSet<CDGNode<'tcx>>> =
        //             BTreeMap::default();

        //         for (_, (vs, vo)) in goal_parents.iter() {
        //             for goal in vs.1.iter() {
        //                 let pre_entry = goals_preimage.entry(goal.clone()).or_default();
        //                 for consume in vs.2.iter() {
        //                     pre_entry.insert(consume.clone());
        //                 }
        //             }
        //             for goal in vo.1.iter() {
        //                 let pre_entry = goals_preimage.entry(goal.clone()).or_default();
        //                 for consume in vo.2.iter() {
        //                     pre_entry.insert(consume.clone());
        //                 }
        //             }
        //         }

        //         println!("pre {:?}", goals_preimage);

        //         // Pick one to couple.
        //         let coupled_leaves = goals_preimage.pop_first().unwrap().1;

        //         println!("consume {:?}", coupled_leaves);

        //         // fixme: here, we should check to see if it's already a coupled edge.

        //         // collect all edges and goals that this consumption gives us back
        //         let mut expires_from_self = Vec::default();
        //         let mut expires_from_other = Vec::default();
        //         let mut coupled_root_self = BTreeSet::default();
        //         let mut coupled_root_other = BTreeSet::default();
        //         for (_, ((vs_origins, vs_goals, vs_leaves), (vo_origins, vo_goals, vo_leaves))) in
        //             goal_parents.iter_mut()
        //         {
        //             if vs_leaves.is_subset(&coupled_leaves) {
        //                 vs_origins.reverse();
        //                 for v in vs_origins.iter() {
        //                   if !expires_from_self.contains(v) {
        //                     expires_from_self.push(v.clone());
        //                   }
        //                 }
        //                 for rs in vs_goals.iter() {
        //                     coupled_root_self.insert(rs.clone());
        //                 }
        //             }
        //             if vo_leaves.is_subset(&coupled_leaves) {
        //                 vo_origins.reverse();
        //                 for v in vo_origins.iter() {
        //                   if !expires_from_other.contains(v) {
        //                     expires_from_other.push(v.clone());
        //                   }
        //                 }
        //                 for rs in vo_goals.iter() {
        //                     coupled_root_other.insert(rs.clone());
        //                 }
        //             }
        //         }

        //         // assert!(coupled_root_self == coupled_root_other);

        //         println!("coupling:");
        //         println!("{:?} ", coupled_leaves);
        //         println!("{:?} // {:?}", expires_from_self, expires_from_other);
        //         println!("{:?} // {:?}", coupled_root_self, coupled_root_other);

        //         // insert the edge into the new graph
        //         // - what edges is it above?
        //         let mut above_origins = BTreeSet::new();
        //         for g in coupled_root_self.iter() {
        //             match working_graph
        //                 .map
        //                 .iter()
        //                 .filter(|s| s.1.leaves.contains(g))
        //                 .collect::<Vec<_>>()[..]
        //             {
        //                 [] => unreachable!("coupled edges must always be above another edge"),
        //                 [g_origin] => above_origins.insert(g_origin.0.clone()),
        //                 _ => {
        //                     unimplemented!("unsure how to model ambiguous blocks. revisit me. ")
        //                 }
        //             };
        //         }
        //         println!("above origins {:?}", above_origins);

        //         // - which origins get a coupled edge? This should be recorded from earlier but I recalculate here.
        //         let origins_that_get_a_copy = expires_from_self
        //             .iter()
        //             .cloned()
        //             .filter(|x| !x.is_tagged())
        //             .collect::<BTreeSet<_>>();
        //         assert!(
        //             origins_that_get_a_copy
        //                 == expires_from_other
        //                     .iter()
        //                     .cloned()
        //                     .filter(|x| !x.is_tagged())
        //                     .collect::<BTreeSet<_>>()
        //         );

        //         // Add the current LHS to the origins_that_get_a_copy list.
        //         // This should be done earlier.
        //         let origins_that_get_a_copy = origins_that_get_a_copy
        //             .into_iter()
        //             .map(|o| {
        //                 (
        //                     o.clone(),
        //                     self.coupling_graph
        //                         .origins
        //                         .map
        //                         .get(&o)
        //                         .unwrap()
        //                         .leaves
        //                         .clone(),
        //                 )
        //             })
        //             .collect::<BTreeSet<_>>();
        //         println!("origins that get a copy: {:?}", origins_that_get_a_copy);

        //         // - which edges to expire under which bb?
        //         // - which bb are we coming from?
        //         //    - add latest_bb to the state
        //         let ((from_s, to_s), (from_o, to_o)) = match (self.loc.clone(), other.loc.clone()) {
        //             (StateLocation::Joining(x, y), StateLocation::Joining(w, z)) => {
        //                 ((x, y), (w, z))
        //             }
        //             // To implement this, I need to reimplement join to be associative. IE, for coupled edges
        //             // to get coupled again. It also should be commutative, to ensure we terminate.
        //             (x, y) => unimplemented!("unimplemented join kind: {:?}", (x, y)),
        //         };
        //         println!("from {:?}", (from_s, from_o));
        //         println!("to {:?}", (to_s, to_o));
        //         assert!(to_s == to_o);

        //         //  - Issue commands to expire these coupled edges.
        //         //  "at the join (bb1, bb2), to create the coupled borrow with roots {...},  if coming from bb1, use annotations from the following origins in order: [...]"
        //         self.coupling_commands
        //             .insert((to_s, from_s, coupled_root_self.clone()), expires_from_self);
        //         self.coupling_commands.insert(
        //             (to_s, from_o, coupled_root_self.clone()),
        //             expires_from_other,
        //         );

        //         // Add the edges to the new graph
        //         for (o, lhs) in origins_that_get_a_copy.into_iter() {
        //             println!("inserting into {:?}", o);
        //             let sig = OriginSignature {
        //                 leaves: lhs,
        //                 roots: coupled_root_self.clone(),
        //                 kind: SignatureKind::Coupled(
        //                     to_s,
        //                     [from_s, from_o].into(),
        //                     above_origins.clone(),
        //                 ),
        //             };
        //             working_graph.map.insert(o.clone(), sig);
        //         }
        //         println!("done inserting, graph is\n{:#?}", working_graph);

        //         // Update the set of goals
        //         for g in coupled_root_self.iter() {
        //             goals.remove(g);
        //         }
        //         for g in coupled_leaves.iter() {
        //             goals.insert(g.clone());
        //         }
        //     }
        // }
        // println!("final graph:\n{:?}", working_graph);

        // self.coupling_graph.origins = working_graph;
    }

    fn widen(&mut self, _: &Self) {
        unreachable!("widening is not possible in this model")
    }
}
