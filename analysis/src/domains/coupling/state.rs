// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// use log::info;

use crate::{
    abstract_interpretation::{AbstractState, AnalysisResult},
    mir_utils::{self, expand, expand_struct_place, is_prefix, Place},
};
use itertools::Itertools;
use prusti_rustc_interface::{
    borrowck::{consumers::RustcFacts, BodyWithBorrowckFacts},
    middle::{
        mir,
        mir::{BasicBlock, Location},
        ty::TyCtxt,
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
};

use super::{btree_replace, FactTable, IntroStatement, OriginLHS};

// These types are stolen from Prusti interface
pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;
pub type PointIndex = <RustcFacts as FactTypes>::Point;
pub type Variable = <RustcFacts as FactTypes>::Variable;
pub type Path = <RustcFacts as FactTypes>::Path;

/// Index into arena-allocated coupled borrows.
/// Coupled borrows are uniquely identified by the join that defined them.
/// bbfrom1 bbfrom2 bbto
pub type CoupledBorrowIndex = (BasicBlock, BasicBlock, BasicBlock);

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
    Coupled(CoupledBorrowIndex),
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
    pub fn add_edge(
        &mut self,
        remove_leaves: BTreeSet<CDGNode<'tcx>>,
        add_leaves: BTreeSet<CDGNode<'tcx>>,
    ) {
        // Possibly repack an edge to change its signature.
        // (since we want the leaves and roots to be disjoint)
        // Only ever do repacks to add to a single edge. We don't care about matching repacks between edges.
        todo!("add edge");
    }

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
            "{:?} -{}-* {:?}",
            self.leaves.iter().collect::<Vec<_>>(),
            match &self.kind {
                SignatureKind::Subgraph(o) => format!("shared {:?}", o),
                SignatureKind::Coupled(x) => format!("coupled {:?}", x),
                SignatureKind::Owned => format!("owned"),
            },
            self.roots.iter().collect::<Vec<_>>()
        )?;
        Ok(())
    }
}

#[derive(Clone, Default, PartialEq, Eq)]
pub struct OriginMap<'tcx> {
    map: BTreeMap<Tagged<Region, Location>, OriginSignature<'tcx>>,
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
        if let Some(sig) = self.map.remove(&Tagged::untagged(origin)) {
            self.map.insert(Tagged::tagged(origin, *location), sig);
        }

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
        for (o, sig) in self.map.iter() {
            for l in sig.leaves.iter() {
                ret.insert(l.clone());
            }
        }
        return ret;
    }

    pub fn get_all_rhs(&self) -> BTreeSet<CDGNode<'tcx>> {
        let mut ret = BTreeSet::new();
        for (o, sig) in self.map.iter() {
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
        for (o, sig) in self.map.iter() {
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
        for (o, sig) in self.map.iter() {
            for r in sig.leaves.iter() {
                if !rr.contains(r) {
                    ret.insert(r.clone());
                }
            }
        }
        return ret;
    }

    // if root is a root, there should be exactly one edge in the coupling graph that directly blocks it.
    fn get_direct_parent(
        &self,
        root: &CDGNode<'tcx>,
    ) -> (Tagged<Region, Location>, OriginSignature<'tcx>) {
        match self
            .map
            .iter()
            .filter(|(_, sig)| sig.roots.contains(root))
            .collect::<Vec<_>>()[..]
        {
            [(k, v)] => (k.clone(), v.clone()),
            _ => unreachable!("excess parents"),
        }
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
            let (tagged_region, sig) = self.get_direct_parent(&goal_working);
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
            ret_origins.push(tagged_region);

            // remove all roots of this edge from the total effect
            for l in sig.roots.iter() {
                ret_leaves.remove(l);
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

/// CouplingState consists of
///     - A CouplingGraph, representing the current
///     - References to the context mir and fact_table
#[derive(Clone)]
pub struct CouplingState<'facts, 'mir: 'facts, 'tcx: 'mir> {
    pub coupling_graph: CDG<'tcx>,
    // Coupled borrows are unqiuely identified by the join that produced them.
    pub couples: BTreeMap<CoupledBorrowIndex, usize>,
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
            couples: Default::default(),
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
            couples: Default::default(),
            fact_table,
            mir,
        }
    }
    pub(crate) fn apply_terminator_effect(
        &self,
        location: Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self)>> {
        let mut new_state = self.clone();
        new_state.cdg_step(location)?;
        let terminator = self.mir.body[location.block].terminator();
        Ok(terminator
            .successors()
            .into_iter()
            .map(|bb| (bb, new_state.clone()))
            .collect())
    }

    pub(crate) fn apply_statement_effect(&mut self, location: Location) -> AnalysisResult<()> {
        self.cdg_step(location)
    }

    /// The main interpretation of Polonius facts
    fn cdg_step(&mut self, location: Location) -> AnalysisResult<()> {
        // expire any origins which expired after any predecessor
        // we assume if an origin expures at the end of ONE predecessor, it expures at the end of ALL of them.
        // keep in mind, this could be a no-op!
        // (recording the necessary changes in leaves as consume and expire statements)
        self.apply_origins(&location)?;

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
        if let Some(mut ogs) = self.fact_table.origin_expires_before.get(location).clone() {
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
                                SignatureKind::Coupled(_) => true,
                                SignatureKind::Owned => true,
                            })
                    })
                    // We are allowed to expire the tree-leaves that are tagged OR are in OGS.
                    .filter(|x| x.tag.is_some() || ogs.contains(&x.data))
                    .next()
                {
                    Some(tree_leaf) => {
                        println!("Found tree leaf: {:?}", tree_leaf);
                        // todo: emit consume and expire statements for that edge.
                        // Coupled edges don't get expired until all couped edges do... but they can get removed!
                        // remove from ogs.
                        done = ogs.is_empty();
                        panic!();
                    }
                    None => {
                        // The rest of ogs are internal, so get tagged.
                        // fixme: Do we also need to tag the LHS of that origin? Probably doens't matter.
                        for x in ogs.into_iter() {
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
        let mut s = serializer.serialize_struct("[coupling state]", 1)?;
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
        write!(
            f,
            "[coupling state] {}",
            serde_json::to_string_pretty(&self).unwrap()
        )
    }
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> PartialEq for CouplingState<'facts, 'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.coupling_graph == other.coupling_graph
    }
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> Eq for CouplingState<'facts, 'mir, 'tcx> {}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> AbstractState for CouplingState<'facts, 'mir, 'tcx> {
    fn is_bottom(&self) -> bool {
        self.coupling_graph.origins.map.is_empty()
    }

    // Invariant: bottom join X is X
    // fixme: is it possible to join in several different ways?
    //  eg. (bb1 join bb2) join bb3   vs    bb1 join (bb2 join bb3)?
    // If so, we might no reach a fixed point with how we're recording data here, since
    // the coupling state will not be equal between these two paths (for the def'n of
    // equality currently implemented, anyways).
    fn join(&mut self, other: &Self) {
        // Check for the trivial cases (join to bottom)
        if other.coupling_graph.origins.map.is_empty() {
            return;
        } else if self.coupling_graph.origins.map.is_empty() {
            self.coupling_graph = other.coupling_graph.clone();
            return;
        }

        let mut working_graph: OriginMap = Default::default();

        println!("JOIN 1: {:?}\n", self.coupling_graph);
        println!("JOIN 2: {:?}\n", other.coupling_graph);

        // Make the LHS of the origins coherent (kill leaves that are in one branch but not the other)
        let lhs = self.coupling_graph.origins.get_live_lhs();
        if lhs != other.coupling_graph.origins.get_live_lhs() {
            unimplemented!("kill dead lhs in live origins");
        }

        let roots = self.coupling_graph.origins.get_roots();
        if roots != other.coupling_graph.origins.get_roots() {
            unreachable!("internal error. roots must be the same between branches.");
        }
        let leaves = self.coupling_graph.origins.get_leaves();
        if leaves != other.coupling_graph.origins.get_leaves() {
            println!("{:?}", leaves);
            println!("{:?}", other.coupling_graph.origins.get_leaves());
            unreachable!("internal error. leaves must be the same between branches by this step");
        }

        println!("roots are: {:?} ", roots);
        println!("leaves are: {:?} ", leaves);

        let mut goals = roots.clone();

        loop {
            // filter out any goals which are totally done.
            goals.retain(|n| !leaves.contains(n) && !n.is_tagged());

            if goals.len() == 0 {
                break;
            }

            println!("goals: {:?}", goals);
            // fixme: There is no reason on earth to recompute this entire thing at every loop iteration
            let mut goal_parents = BTreeMap::new();
            for g in goals.iter().cloned() {
                goal_parents.insert(
                    g.clone(),
                    (
                        self.coupling_graph.origins.get_parent([g.clone()].into()),
                        other.coupling_graph.origins.get_parent([g.clone()].into()),
                    ),
                );
            }

            // If any of these match, they necessarily contain the same edges (right?)
            if let Some((r, (vs, vo))) = goal_parents.iter().filter(|(_, (vs, vo))| vs == vo).next()
            {
                println!("{:?}: {:?} // {:?}", r, vs, vo);

                // Both graphs do the same kinds of capability exchanges. If their edges are identical, move them.
                // If their edges are not identical, add a coupled edge for this exchange.
                println!("match! moving the origins {:?} to the complete graph", vs.0);
                for o in vs.0.iter() {
                    working_graph.map.insert(
                        o.clone(),
                        self.coupling_graph.origins.map.get(o).unwrap().clone(),
                    );
                }
                for completed_goal in vs.1.iter() {
                    goals.remove(completed_goal);
                }
                for new_goal in vs.2.iter().cloned() {
                    goals.insert(new_goal);
                }
                println!("new goals: {:?}", goals);
            } else {
                // No match.
                // Create a partition of (input/ouput)
                println!("no match\ngoals: {:?}", goal_parents);

                // Partition the set of goals using goal parents:
                // Elements in teh partition must be satuated wrt expiring edges

                // goals_preimage: map from goal to a set of resources that we can expire to get it back
                let mut goals_preimage: BTreeMap<CDGNode<'tcx>, BTreeSet<CDGNode<'tcx>>> =
                    BTreeMap::default();

                for (_, (vs, vo)) in goal_parents.iter() {
                    for goal in vs.1.iter() {
                        let pre_entry = goals_preimage.entry(goal.clone()).or_default();
                        for consume in vs.2.iter() {
                            pre_entry.insert(consume.clone());
                        }
                    }
                    for goal in vo.1.iter() {
                        let pre_entry = goals_preimage.entry(goal.clone()).or_default();
                        for consume in vo.2.iter() {
                            pre_entry.insert(consume.clone());
                        }
                    }
                }

                println!("pre {:?}", goals_preimage);

                // Pick one to couple.
                let coupled_leaves = goals_preimage.pop_first().unwrap().1;

                println!("consume {:?}", coupled_leaves);

                // collect all edges and goals that this consumption gives us back
                let mut expires_from_self = Vec::default();
                let mut expires_from_other = Vec::default();
                let mut coupled_root_self = BTreeSet::default();
                let mut coupled_root_other = BTreeSet::default();
                for (_, ((vs_origins, vs_goals, vs_leaves), (vo_origins, vo_goals, vo_leaves))) in
                    goal_parents.iter_mut()
                {
                    if vs_leaves.is_subset(&coupled_leaves) {
                        vs_origins.reverse();
                        expires_from_self.append(vs_origins);
                        for rs in vs_goals.iter() {
                            coupled_root_self.insert(rs.clone());
                        }
                    }
                    if vo_leaves.is_subset(&coupled_leaves) {
                        vo_origins.reverse();
                        expires_from_other.append(vo_origins);
                        for rs in vo_goals.iter() {
                            coupled_root_other.insert(rs.clone());
                        }
                    }
                }

                assert!(coupled_root_self == coupled_root_other);

                println!("coupling:");
                println!("{:?} ", coupled_leaves);
                println!("{:?} // {:?}", expires_from_self, expires_from_other);
                println!("{:?} // {:?}", coupled_root_self, coupled_root_other);

                // Update the set of goals
                for g in coupled_root_self.iter() {
                    goals.remove(g);
                }
                for g in coupled_leaves.iter() {
                    goals.insert(g.clone());
                }
            }
        }

        todo!("implement joins exited its loop");
    }

    fn widen(&mut self, _: &Self) {
        unreachable!("widening is not possible in this model")
    }
}
