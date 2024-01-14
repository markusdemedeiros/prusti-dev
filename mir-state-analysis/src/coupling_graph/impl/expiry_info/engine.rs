// © 2024, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.


#![allow(unused_imports)]

use std::cell::RefCell;
use std::rc::Rc;
use std::{cell::Cell, collections::BTreeSet};
use std::fmt::Formatter;

use prusti_interface::environment::borrowck::facts::{BorrowckFacts, AllOutputFacts};
use prusti_interface::environment::mir_body::borrowck::facts::LocationTable;
use prusti_interface::environment::mir_body::borrowck::lifetimes::Lifetimes;
use prusti_interface::environment::mir_utils::MirPlace;
use prusti_rustc_interface::{
    borrowck::{
        borrow_set::{BorrowData, TwoPhaseActivation},
        consumers::{
            calculate_borrows_out_of_scope_at_location, places_conflict, BorrowIndex, Borrows,
            OutlivesConstraint, PlaceConflictBias, RichLocation,
        },
    },
    data_structures::fx::{FxHashSet, FxIndexMap},
    dataflow::{Analysis, AnalysisDomain, ResultsCursor, fmt::DebugWithContext},
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
use prusti_rustc_interface::dataflow::JoinSemiLattice;


use crate::coupling_graph::CgContext;
use crate::coupling_graph::outlives_info::AssignsToPlace;

use super::{graph::Eg, control_flow::ControlFlowFlag};

pub(crate) struct ExpiryInfo<'a, 'tcx> {
    pub(crate) cgx: &'a CgContext<'a, 'tcx>,
    flow_borrows : RefCell<ResultsCursor<'a, 'tcx, Borrows<'a, 'tcx>>>,
    /* really we should be able to populate cgx with this. why is it not doing borrow checking on it's own? */
    output_facts: prusti_rustc_interface::borrowck::consumers::PoloniusOutput,
    bb_index: Cell<BasicBlock>,
    top_crates: bool,
}

impl<'a, 'tcx> ExpiryInfo<'a, 'tcx> {
    pub(crate) fn new(cgx: &'a CgContext<'a, 'tcx>, top_crates: bool) -> Self {
        let input_facts = cgx.facts.input_facts.borrow().as_ref().unwrap().clone();
        let location_table1 = cgx.facts.location_table.borrow().as_ref().unwrap();
        let output_facts = prusti_rustc_interface::polonius_engine::Output::compute(
            &input_facts,
            prusti_rustc_interface::polonius_engine::Algorithm::Naive,
            true,
        );

        // FIXME: can we reuse the other anaylsis without screwing up the other state?
        let borrow_set = &cgx.facts2.borrow_set;
        let regioncx = &*cgx.facts2.region_inference_context;
        let flow_borrows = Borrows::new(cgx.rp.tcx(), cgx.rp.body(), regioncx, borrow_set)
            .into_engine(cgx.rp.tcx(), cgx.rp.body())
            .pass_name("borrowck")
            .iterate_to_fixpoint()
            .into_results_cursor(cgx.rp.body());

        Self { cgx, bb_index: Cell::new(START_BLOCK), flow_borrows: RefCell::new(flow_borrows), output_facts, top_crates }
    }

}

/// Helper Struct: Used to represent a one-shot lazy join of graphs
/// This way we can avoid associativity issues by just waiting until we have 
/// all the branches to be coupled.
#[derive(Debug, Clone, Eq)]
pub(crate) enum LazyCoupling {
    Done(Eg),
    Lazy(Vec<(ControlFlowFlag, Eg)>)
}

impl PartialEq for LazyCoupling {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Done(l), Self::Done(r)) => l == r,
            (Self::Lazy(l), Self::Lazy(r)) => {
                l.iter().all(|v| r.contains(v)) &&
                r.iter().all(|v| l.contains(v)) 
            }
            _ => false,
        }
    }
}

impl LazyCoupling {
    /// Lazily join two LazyCouplings together,
    /// The coupling must not be shot yet
    pub(crate) fn append(&mut self, mut other: Self) {
        match (self, other) {
            (Self::Lazy(l), Self::Lazy(mut r)) => {
                todo!(); // Check to see if there's a lazy case already?
                // l.append(&mut r)
            }
            _ => {
                panic!("one-shot lazy join given Done value");
            }
        }
    }

    /// Lazily add a single branch to a LazyCoupling
    pub(crate) fn add_case(&mut self, mut other: (ControlFlowFlag, Eg)) {
        self.append(LazyCoupling::Lazy(vec![other]));
    }

    /// Identity for join 
    pub(crate) fn empty() -> Self {
        Self::Lazy(vec![])
    }

    /// Ensure that the lazy join is completed, or attempt to complete it
    /// Calling this asserts that nothing else will be added to this join point afterwards, which should be the case
    /// if we are correcrtly combining state together (never joining with prior work)
    pub(crate) fn shoot<'a, 'tcx>(&mut self, cgx: &'a CgContext<'a, 'tcx>) {
        if let (Self::Lazy(v)) = self {
            let v = std::mem::take(v);
            assert!(ControlFlowFlag::join_is_complete(v.iter().map(|x| &x.0).collect::<_>(), cgx));
            assert!(v.len() > 0);
            *self = Self::Done(Eg::couple(v));

        }
    }

    /// Ensures we only ever read shot values
    pub(crate) fn read(&mut self) -> &mut Eg {
        match self {
            Self::Lazy(_) => panic!("tried to read an unevaluated lazy coupling"),
            Self::Done(v) => &mut (*v)
        }

    }
}


#[derive(Clone)]
pub(crate) struct Exg<'a, 'tcx> {
    pub cgx: &'a CgContext<'a, 'tcx>,

    pub graph: LazyCoupling,

    pub location: Location,

    // expiry instructions at this point 
    // pub instructions: (),

    // live groups 
    // pub active_groups: (), 
}

impl PartialEq for Exg<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.graph == other.graph
    }
}

impl Eq for Exg<'_, '_> {}

impl <'a, 'tcx> Exg <'a, 'tcx> {

    pub(crate) fn initialize_start_block(&mut self) {
        /* nothing special for now, put universal origin stuff here? 
           not even sure I understand what Jonas' implementation is doing 
        */
    }

    pub(crate) fn reset_ops(&mut self) {
        /* FIXME: implemenet ops */
    }

    pub fn handle_outlives(&mut self, location: Location, assigns_to: Option<MirPlace<'tcx>>) {
        let local = assigns_to.clone().map(|a| a.local);
        for &c in self
            .cgx
            .outlives_info
            .pre_constraints(location, local, &self.cgx.region_info)
        {
            println!("  - outlives(pre):  {:?}", c);
            /* self.outlives(c) */
        }
        if let Some(place) = assigns_to {
            println!("  - kills: {:?}", place);
            /* self.kill_shared_borrows_on_place(Some(location), place); */
        }
        for &c in self
            .cgx
            .outlives_info
            .post_constraints(location, local, &self.cgx.region_info)
        {
            println!("  - outlives(post): {:?}", c);
            /* self.outlives(c); */
        }
    }
}


impl<'tcx> Visitor<'tcx> for Exg<'_, 'tcx> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        println!("          OP {:?}", operand);
        self.super_operand(operand, location);
        /*
        match operand {
            Operand::Copy(_) => (),
            &Operand::Move(place) => {
                self.kill_shared_borrows_on_place(Some(location), place);
            }
            Operand::Constant(_) => (),
        }
        */
    }

    // when is this acutally called?
    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        println!("          ST {:?}", statement);
        self.super_statement(statement, location);
        /*
        match &statement.kind {
            StatementKind::AscribeUserType(box (p, _), _) => {
                for &c in self
                    .cgx
                    .outlives_info
                    .type_ascription_constraints
                    .iter()
                    .filter(|c| {
                        self.cgx.region_info.map.for_local(c.sup, p.local)
                            || self.cgx.region_info.map.for_local(c.sub, p.local)
                    })
                {
                    self.outlives(c);
                }
            }
            _ => (),
        }
         */
    }
}



impl<'a, 'tcx> JoinSemiLattice for Exg<'a, 'tcx> {
    /// ASSUMES that self.cgx and other.cgx are the same
    fn join(&mut self, other: &Self) -> bool {
        if self.location != other.location {
            panic!("Join of Exg states at different locations ({:?} and {:?})is incomprehensible", 
                self.location, 
                other.location);
        }


        // If one state is newer, use that.
        // If they are the same, we must combine them.

        // When is join called? Is it like the other framework or can it be called arbitrarily?
        todo!()
    }
}

impl<'a, 'tcx> std::fmt::Debug for Exg<'a, 'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<An Exg instance>")
    }
}

impl<'a, 'tcx> DebugWithContext<ExpiryInfo<'a, 'tcx>> for Exg<'a, 'tcx> { }

impl<'a, 'tcx> AnalysisDomain<'tcx> for ExpiryInfo<'a, 'tcx> {
    type Domain = Exg<'a, 'tcx>;
    const NAME: &'static str = "expiry_graph";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        /* ?? */
        let block = self.bb_index.get();
        self.bb_index.set(block.plus(1));

        Exg {
            cgx: self.cgx,
            graph: LazyCoupling::Done(Default::default()),
            location: Location {
                block: START_BLOCK,
                statement_index: 0,
            },
        }
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        self.bb_index.set(START_BLOCK);
        state.initialize_start_block()
    }
}


impl<'a, 'tcx> Analysis<'tcx> for ExpiryInfo<'a, 'tcx> {
    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        println!("[before location:       {:?}]", location);
        state.location = location;
        state.reset_ops();
        if location.statement_index == 0 {
            // FIXME what does state.is_pre do in the other analysis?
            // state.is_pre = false;
            self.flow_borrows
                .borrow_mut()
                .seek_to_block_start(location.block);

            // FIXME it would probably be helpful to track the live borrows in the state?
            // Though we'd really want live lifetimes, not just live borrows. 
        }

        // self.flow_borrows
        //     .borrow_mut()
        //     .seek_before_primary_effect(location);
        // println!("[flow_borrows (pre):  {:?}]", self.flow_borrows.borrow().get().clone());
        // self.flow_borrows
        //     .borrow_mut()
        //     .seek_after_primary_effect(location);
        // println!("[flow_borrows (post): {:?}]", self.flow_borrows.borrow().get().clone());

        // Jonas sets the live borrows to other here... why? Shouldn't we do this in apply_statement_effect?
        
        /*
        FIXME: kills
        let oos = self.out_of_scope.get(&location);
        state.handle_kills(&delta, oos, location);
         */
    }

    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        let point = self.cgx.facts.location_table.borrow().as_ref().unwrap().start_index(location);
        println!("[statement effect:      {:?}/{:?}]", location, point);
        println!(" ** live borrows ** ");
        println!(" ** {:?}", self.output_facts.origin_live_on_entry.get(&point).unwrap());

        // println!(" ** {:?} ", self.lifetimes.get_origin_live_on_entry_start(location));

        // println!(" ** {:?} ", self.lifetimes); // .as_ref().unwrap().as_ref().origin_live_on_entry.get(&point));


        state.reset_ops();
        state.handle_outlives(location, statement.kind.assigns_to().map(|p| p.into()));
        state.visit_statement(statement, location);
    }

    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        // FIXME: same live borrows calculation here 
        println!("APPLY BEFORE TERMINATOR EFFECT");
        // todo!();
        /*
        // println!("Location: {l}");
        state.location = location;
        state.reset_ops();

        self.flow_borrows
            .borrow_mut()
            .seek_after_primary_effect(location);
        let other = self.flow_borrows.borrow().get().clone();

        let delta = calculate_diff(&other, &state.live);
        state.live = other;

        let oos = self.out_of_scope.get(&location);
        state.handle_kills(&delta, oos, location);
         */
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        println!("APPLY TERMINATOR EFFECT");
        terminator.edges()
        // todo!();
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
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // Nothing to do here
    }
}