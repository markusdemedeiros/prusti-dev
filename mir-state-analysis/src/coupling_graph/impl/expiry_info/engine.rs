// © 2024, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.


use std::cell::Cell;

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
use prusti_rustc_interface::{dataflow::JoinSemiLattice};

use crate::coupling_graph::CgContext;

pub(crate) struct ExpiryInfo<'a, 'tcx> {
    pub(crate) cgx: &'a CgContext<'a, 'tcx>,
    bb_index: Cell<BasicBlock>,
    top_crates: bool,
}

impl<'a, 'tcx> ExpiryInfo<'a, 'tcx> {
    pub(crate) fn new(cgx: &'a CgContext<'a, 'tcx>, top_crates: bool) -> Self {
        Self { cgx, bb_index: Cell::new(START_BLOCK), top_crates }
    }
}

#[derive(Clone)]
pub(crate) struct Exg<'a, 'tcx> {
    pub cgx: &'a CgContext<'a, 'tcx>,

    pub graph: (),

    // expiry instructions at this point 
    pub instructions: (),
    // live groups
    pub active_groups: (), 
}

impl PartialEq for Exg<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.graph == other.graph
    }
}

impl Eq for Exg<'_, '_> {}

impl <'a, 'tcx> Exg <'a, 'tcx> {}

impl<'a, 'tcx> JoinSemiLattice for Exg<'a, 'tcx> {
    fn join(&mut self, other: &Self) -> bool {
        todo!()
    }
}

impl<'a, 'tcx> AnalysisDomain<'tcx> for ExpiryInfo<'a, 'tcx> {
    type Domain = Exg<'a, 'tcx>;
    const NAME: &'static str = "expiry_graph";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        /*
        let block = self.bb_index.get();
        self.bb_index.set(block.plus(1));
        Cg::new(
            self.cgx,
            self.top_crates,
            Location {
                block,
                statement_index: 0,
            },
        )
        */
        todo!();
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        /*
        self.bb_index.set(START_BLOCK);
        state.initialize_start_block()
         */
        todo!();
    }
}

impl<'a, 'tcx> Analysis<'tcx> for ExpiryInfo<'a, 'tcx> {
    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        /*
        state.location = location;
        state.reset_ops();

        if location.statement_index == 0 {
            state.is_pre = false;
            // println!("\nblock: {:?}", location.block);
            let l = format!("{location:?}").replace('[', "_").replace(']', "");
            state.output_to_dot(
                format!(
                    "log/coupling/individual/{l}_v{}_start.dot",
                    state.sum_version()
                ),
                false,
            );
            self.flow_borrows
                .borrow_mut()
                .seek_to_block_start(location.block);
            state.live = self.flow_borrows.borrow().get().clone();
        }
        self.flow_borrows
            .borrow_mut()
            .seek_after_primary_effect(location);
        let other = self.flow_borrows.borrow().get().clone();
        let delta = calculate_diff(&other, &state.live);
        state.live = other;

        let oos = self.out_of_scope.get(&location);
        state.handle_kills(&delta, oos, location);
         */
        todo!();
    }

    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        /*
        state.reset_ops();
        state.handle_outlives(location, statement.kind.assigns_to());
        state.visit_statement(statement, location);

        let l = format!("{location:?}").replace('[', "_").replace(']', "");
        state.output_to_dot(
            format!("log/coupling/individual/{l}_v{}.dot", state.sum_version()),
            false,
        );
        */
        todo!();
    }

    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        /*
        // println!("Location: {l}");
        state.location = location;
        state.reset_ops();

        if location.statement_index == 0 {
            state.is_pre = false;
            // println!("\nblock: {:?}", location.block);
            let l = format!("{location:?}").replace('[', "_").replace(']', "");
            state.output_to_dot(
                format!(
                    "log/coupling/individual/{l}_v{}_start.dot",
                    state.sum_version()
                ),
                false,
            );
            self.flow_borrows
                .borrow_mut()
                .seek_to_block_start(location.block);
            state.live = self.flow_borrows.borrow().get().clone();
        }
        self.flow_borrows
            .borrow_mut()
            .seek_after_primary_effect(location);
        let other = self.flow_borrows.borrow().get().clone();

        let delta = calculate_diff(&other, &state.live);
        state.live = other;

        let oos = self.out_of_scope.get(&location);
        state.handle_kills(&delta, oos, location);
         */
        todo!();
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        /*
        state.reset_ops();
        state.handle_outlives(location, terminator.kind.assigns_to());
        state.visit_terminator(terminator, location);

        match &terminator.kind {
            TerminatorKind::Return => {
                let l = format!("{location:?}").replace('[', "_").replace(']', "");
                state.output_to_dot(
                    format!(
                        "log/coupling/individual/{l}_v{}_pre.dot",
                        state.sum_version()
                    ),
                    false,
                );
                // Pretend we have a storage dead for all `always_live_locals` other than the args/return
                for l in self.cgx.rp.always_live_locals_non_args().iter() {
                    state.kill_shared_borrows_on_place(Some(location), l.into());
                }
                // Kill all the intermediate borrows, i.e. turn `return -> x.0 -> x` into `return -> x`
                for r in self
                    .cgx
                    .facts2
                    .borrow_set
                    .location_map
                    .values()
                    .chain(self.cgx.sbs.location_map.values())
                {
                    state.remove(r.region, Some(location));
                }

                state.merge_for_return(location);
            }
            _ => (),
        };

        let l = format!("{:?}", location).replace('[', "_").replace(']', "");
        state.output_to_dot(
            format!("log/coupling/individual/{l}_v{}.dot", state.sum_version()),
            false,
        );
        terminator.edges()
      */
      todo!();
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // Nothing to do here
        todo!();
    }
}

