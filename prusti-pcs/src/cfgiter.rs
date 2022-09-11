// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]
use crate::model::PCSState;
use core::cell::*;
use itertools::{
    Either::{Left, Right},
    Itertools,
};
use prusti_interface::{
    environment::{
        borrowck::facts::{BorrowckFacts, Loan, PointType},
        mir_analyses::{
            allocation::{compute_definitely_allocated, DefinitelyAllocatedAnalysisResult},
            initialization::{compute_definitely_initialized, DefinitelyInitializedAnalysisResult},
        },
        mir_body::borrowck::facts::{
            LocationTable,
            RichLocation::{Mid, Start},
        },
        polonius_info::PoloniusInfo,
        Environment, Procedure,
    },
    utils::{expand_one_level, is_prefix},
    PrustiError,
};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{
        mir,
        mir::{
            AggregateKind::*, Operand, Operand::*, Rvalue::*, StatementKind::*, Terminator,
            TerminatorKind, TerminatorKind::*,
        },
        ty::TyCtxt,
    },
};
use std::fmt::Debug;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// CFG Iterator

pub struct PCSIter<'mir, 'tcx: 'mir> {
    mir: &'mir mir::Body<'tcx>,
    pub dirty_blocks: Vec<DirtyBlock<'tcx>>,
    pub next_blocks: Vec<DirtyBlock<'tcx>>,
    pub done_blocks: Vec<mir::BasicBlock>,
}

impl<'mir, 'tcx: 'mir> PCSIter<'mir, 'tcx> {
    pub fn new(mir: &'mir mir::Body<'tcx>, initial: DirtyBlock<'tcx>) -> Self {
        PCSIter {
            mir,
            dirty_blocks: vec![],
            next_blocks: vec![initial],
            done_blocks: vec![],
        }
    }

    pub fn is_done(&self) -> bool {
        self.next_blocks.is_empty() && self.dirty_blocks.is_empty()
    }

    // Greedily pick blocks with complete in-degree
    pub fn next(&mut self) -> Option<(DirtyBlock<'tcx>, FlowExclusion)> {
        // If there's a block with full in-degree,
        if let Some(ret) = self.next_blocks.pop() {
            return Some((ret.clone(), self.compute_flow_exclusion(ret)));
        }

        // TODO: This is inefficient
        // Update the dirty_blocks to see if any of them are full in-degree (inefficient,
        //  but only loop heads should be in here)
        let mut dirty_blocks1 = vec![];
        while let Some(d) = self.dirty_blocks.pop() {
            if self.mir.predecessors()[*d.block()]
                .iter()
                .all(|suc| self.done_blocks.contains(suc))
            {
                self.next_blocks.push(d);
            } else {
                dirty_blocks1.push(d);
            }
        }
        self.dirty_blocks = dirty_blocks1;

        // Pick from next_blocks, then dirty_blocks, then fail.
        // TODO: refactor to or_else
        if let Some(ret) = self.next_blocks.pop() {
            return Some((ret.clone(), self.compute_flow_exclusion(ret)));
        } else if let Some(ret) = self.dirty_blocks.pop() {
            return Some((ret.clone(), self.compute_flow_exclusion(ret)));
        } else {
            return None;
        }
    }

    pub fn compute_flow_exclusion(&self, d: DirtyBlock<'tcx>) -> FlowExclusion {
        self.mir.predecessors()[*d.block()]
            .iter()
            .map(|pred| (pred.clone(), self.done_blocks.contains(pred)))
            .collect()
    }

    pub fn push(&mut self, dirty: DirtyBlock<'tcx>) {
        if !self.done_blocks.contains(dirty.block())
            && !self.next_blocks.iter().any(|d| d.block() == dirty.block())
            && !self.dirty_blocks.iter().any(|d| d.block() == dirty.block())
        {
            self.dirty_blocks.push(dirty);
        }
    }

    pub fn finish(&mut self, done: mir::BasicBlock) {
        //  TODO: Runtime check that the key isn't already in there?
        self.done_blocks.push(done);
    }
}

#[derive(Clone)]
pub struct DirtyBlock<'tcx>(PCSState<'tcx>, mir::BasicBlock);

impl<'tcx> DirtyBlock<'tcx> {
    pub fn new(state: PCSState<'tcx>, block: mir::BasicBlock) -> Self {
        DirtyBlock { 0: state, 1: block }
    }

    pub fn block(&self) -> &mir::BasicBlock {
        &self.1
    }
}

type FlowExclusion = Vec<(mir::BasicBlock, bool)>;
// interp true iff basic block is previously computed.
