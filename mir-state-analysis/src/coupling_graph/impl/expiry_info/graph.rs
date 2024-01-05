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


/// Represents the last path an execution took through the to- block.
#[derive(PartialEq, Eq, Debug)]
struct DataflowFlag {
    from : BasicBlock,
    to : BasicBlock
}

/// Infrormation for using DataFlowFlags 
pub(crate) struct DataflowInfo<'a, 'tcx> { 
    pub(crate) cgx: &'a CgContext<'a, 'tcx>,
}

impl<'a, 'tcx> DataflowInfo<'a, 'tcx> {
    /// interp. 
    /// DataflowFlag is possible to set 
    pub fn is_valid(f: &DataflowFlag) -> bool {
        todo!()
    }

    /// interp. 
    /// Exactly one sibling should be set if some execution path goes through the to-block
    /// No siblings should be set if no execution path goes through the to-block
    pub fn siblings(f: &DataflowFlag) -> FxHashSet<DataflowFlag> {
        todo!()
    }
}


/// DSL for high-level actions on the reborrowing DAG/PCS
#[derive(PartialEq, Eq)]
pub(crate) enum Annotation {
    Insert(Node),
    Freeze(Node),
    Thaw(Node),
}


// Directed Hypergraph of expiry groups with coupled hyperedges
// Nodes are RegionVid's (interp. the respective resource)
// Edges are annotated with GroupID's, each may have many parents and many children
#[derive(Default)]
struct Eg { 
    parents : FxHashMap<Group, FxHashSet<Node>>,
    children : FxHashMap<Group, FxHashSet<Node>>,
    live_regions : FxHashMap<Node, Group>,
    live_groups : FxHashSet<Group>,
    annotations : FxHashMap<Group, Vec<Annotation>>,
    fresh_group : Group, 
}

impl PartialEq for Eg {
    fn eq(&self, other: &Self) -> bool {
        /* FIXME: this is wrong: check should see if they're the same graph mod group annotations */
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
        assert!(self.live_groups.insert(r));
        return r;
    }

    /// Given a node X and children C, add the shape
    ///     X --[expire X]--> C
    ///  to the graph
    fn issue_group(self: &mut Self, node: Node, children: FxHashSet<Node>) -> Group {
        assert!(!self.live_regions.contains_key(&node));
        let group = self.gen_fresh_group();
        assert!(self.annotations.insert(group, vec![Annotation::Insert(node)]).is_some());
        assert!(self.children.insert(group, children).is_some());
        assert!(self.parents.insert(group, [node].iter().cloned().collect::<_>()).is_some()); /* FIXME */
        return group;
    }

    /// Get the sequence of annotations we would insert if we were to expire a node right now 
    /// returns None if that expiry is not possible 
    pub fn query_expiry(self: & Self, node: Node) -> Option<Vec<Annotation>> {
        todo!();
    }
}
