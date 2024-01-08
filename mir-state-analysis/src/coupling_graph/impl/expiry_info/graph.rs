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

type VertexTag = usize; 

#[derive(PartialEq, Eq, Debug, Hash, Clone, Copy)]
pub(crate) struct Vertex {
    region: RegionVid,
    tag: Option<VertexTag>,
}

impl Vertex {
    /// Tags a vertex only if it is untagged
    pub(crate) fn tag_safe(&mut self, tag: VertexTag) {
        self.tag = self.tag.or_else(|| Some(tag));
    }
}

type Group = usize;

/// DSL for the actions an exiry may require from the lower passes
/// These make up the annotations on each group
#[derive(PartialEq, Eq, Debug, Hash, Clone)]
pub(crate) enum Annotation {
    /// Base-level expiry associated to the loan Vertex
    BasicExpiry(Vertex),
    Freeze(Vertex),
    Thaw(Vertex),
    Branch(Vec<(ControlFlowFlag, Vec<Annotation>)>),
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
}


#[derive(Debug, Clone)]
pub(crate) struct Eg { 
    /// Edge structure of the groups 
    parents : FxHashMap<Group, FxHashSet<Vertex>>,
    children : FxHashMap<Group, FxHashSet<Vertex>>,

    /// Set of vertices in the graph
    live_regions : FxHashMap<Vertex, Group>,

    /// Edges of the graph, plus their annotations
    annotations : FxHashMap<Group, GroupData>,

    /// Next fresh group
    /// INVARIANT any group >= fresh_group is fresh
    fresh_group : Group, 

    /// Next fresh tag
    fresh_tag : VertexTag,
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
            fresh_tag: 0 
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
    ///  to the graph. X must not exist in the graph already. 
    fn issue_group(self: &mut Self, vertex: Vertex, children: FxHashSet<Vertex>) -> Group {
        assert!(!self.live_regions.contains_key(&vertex));
        let group = self.gen_fresh_group();
        assert!(self.annotations.insert(group, GroupData::basic_data(vertex)).is_some());
        assert!(self.children.insert(group, children).is_some());
        assert!(self.parents.insert(group, [vertex].into_iter().collect::<_>()).is_some()); 
        return group;
    }

    /// Bottom graph
    pub(crate) fn bottom() -> Self  { 
        Self::default()
    }

    pub(crate) fn couple(v: Vec<(ControlFlowFlag, Self)>) -> Self {
        todo!();
    }

}
