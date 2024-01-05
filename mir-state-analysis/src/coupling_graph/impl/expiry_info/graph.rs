// © 2024, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

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

use prusti_rustc_interface::{
    data_structures::fx::FxHashMap,
}; 

use crate::coupling_graph::CgContext;

type Node = RegionVid;

type Group = usize;

#[derive(PartialEq, Eq)]
pub(crate) enum Annotation {
    ExpireLifetime(Node),
}


// Directed Hypergraph of expiry groups with coupled hyperedges
// Nodes are RegionVid's (interp. the respective resource)
// Edges are annotated with GroupID's, each may have many parents and many children
#[derive(Default)]
struct Eg { 
    parents : FxHashMap<Group, FxHashSet<Node>>,
    children : FxHashMap<Group, FxHashSet<Node>>,
    live_regions : FxHashMap<RegionVid, Group>,
    live_groups : FxHashSet<Group>,
    annotations : FxHashMap<Group, Vec<Annotation>>,
    fresh_group : Group, 
}

impl PartialEq for Eg {
    fn eq(&self, other: &Self) -> bool {
        self.parents == other.parents && 
        self.children == other.children && 
        self.live_regions == other.live_regions && 
        self.live_groups == other.live_groups && 
        self.annotations == other.annotations 
    }
}

impl Eq for Eg {}

impl Eg {
    fn gen_fresh_group (self: &mut Self) -> Group {
        let r = self.fresh_group;
        self.fresh_group += 1;
        return r;
    }
}
