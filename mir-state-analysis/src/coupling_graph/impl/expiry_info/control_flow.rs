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

use crate::coupling_graph::CgContext;

/// Representation of control flow at Runtime
/// Two ControlFlowFlags are siblings when they have the same `to` block
/// INVARIANT: If the `to` block is a predecessor in the control flow graph, 
/// exactly one sibling flag should be set at runtime. Otherwise, none should
/// be set. 
#[derive(PartialEq, Eq, Debug, Hash, Clone, PartialOrd, Ord)]
pub(crate) struct ControlFlowFlag {
    from : BasicBlock,
    to : BasicBlock
}

impl ControlFlowFlag {
    /// Decide if a control flow flag is legal in a given MIR body
    pub fn valid<'a, 'tcx>(&self, cgx: &'a CgContext<'a, 'tcx>) -> bool {
        todo!()
    }

    pub fn is_sibling(&self, other: &Self) -> bool {
        self.to == other.to
    }

    fn num_siblings(&self, other: &Self) -> usize {
        todo!();
    }

    pub fn join_is_complete<'a, 'tcx>(v: Vec<&Self>, cgx: &'a CgContext<'a, 'tcx>) -> bool {
        // All flags must be valid
        // All to-blocks must be the same
        // Must contain all prececessor blocks to the to-block
        // Must not contain anything else (length equals num_siblings)
        todo!()
    }

}