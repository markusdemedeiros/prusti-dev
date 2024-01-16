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

use super::graph::Vertex;
use super::lazy_coupling::LazyCoupling;
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

    pub(crate) fn get_origin_contains_loan_at(&self, location: Location, start: bool) -> Vec<RegionVid> {
        // FIXME: extremely frusturating: I can't just pass around LocationIndex values because I can't import that type????
        let point = if start {
            self.cgx.facts.location_table.borrow().as_ref().unwrap().start_index(location)
        } else {
            self.cgx.facts.location_table.borrow().as_ref().unwrap().mid_index(location)
        };
        if let Some(m) = self.output_facts.origin_contains_loan_at.get(&point) {
            return m.keys().cloned().collect::<Vec<_>>();
        } else  {
            return vec![];
        }
    }

    pub(crate) fn get_origin_live_on_entry(&self, location: Location, start: bool) -> Vec<RegionVid> {
        // FIXME: extremely frusturating: I can't just pass around LocationIndex values because I can't import that type????
        let point = if start {
            self.cgx.facts.location_table.borrow().as_ref().unwrap().start_index(location)
        } else {
            self.cgx.facts.location_table.borrow().as_ref().unwrap().mid_index(location)
        };
        return self.output_facts.origin_live_on_entry.get(&point).map(|x| x.clone()).unwrap_or_default();
    }

    pub(crate) fn get_universal_origins(&self) -> Vec<RegionVid> {
        let u = self.cgx.facts.input_facts.borrow().clone();
        return u.unwrap().universal_region;
    }
}



#[derive(Clone)]
pub(crate) struct Exg<'a, 'tcx> {
    pub cgx: &'a CgContext<'a, 'tcx>,
    pub output_facts: prusti_rustc_interface::borrowck::consumers::PoloniusOutput,
    pub graph: LazyCoupling,
    pub location: Location,

    // expiry instructions at this point 
    // pub instructions: (),
}

impl PartialEq for Exg<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.graph == other.graph
    }
}

impl Eq for Exg<'_, '_> {}

impl <'a, 'tcx> Exg <'a, 'tcx> {

    pub(crate) fn initialize_start_block(&mut self) {
        let g = self.graph.read();

        // FIXME: there should be a better way to get these? 
        let location = Location { block: START_BLOCK, statement_index: 0 };
        let point = self.cgx.facts.location_table.borrow().as_ref().unwrap().start_index(location);
        for r in self.output_facts.origin_live_on_entry.get(&point).unwrap().iter() {
            g.add_vertex(Vertex::untagged(*r));
        }
        // TODO add universal edges too
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
            graph: LazyCoupling::Done(Eg::default()),
            output_facts: self.output_facts.clone(),
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
        println!("[PRE statement effect:      {:?}]", location);

        // basic steps
        state.location = location;
        state.reset_ops();
        let point = self.cgx.facts.location_table.borrow().as_ref().unwrap().start_index(location);

        // Get a coherent graph 
        if location.statement_index == 0 {
            // FIXME what does state.is_pre mean in the other analysis?
            // state.is_pre = false;
            /* TODO: if Location is 0, shoot the graph */
        }
        let g = state.graph.read();

        let mut to_retain = self.get_universal_origins().into_iter().map(|x| Vertex::untagged(x)).collect::<Vec<_>>();
        for r in self.get_origin_contains_loan_at(location, true) {
            to_retain.push(Vertex::untagged(r));
        }
        g.expire_except(to_retain);


        // update the graph: remove dead vertices
        // this could also be done at the end of the last Mid statement? 
        // for k in self.get_live_borrows_at(location, true) {
        //     g.include_vertex(Vertex::untagged(k));
        // }


        // debug: we should not have any new vertices
        println!("  ** uo :   {:?}", self.get_universal_origins());
        println!("  ** ocla : {:?}", self.get_origin_contains_loan_at(location, true));
        println!("  ** oloe : {:?}", self.get_origin_contains_loan_at(location, true));
        println!("{}\n", state.graph.pretty()); 

        // Jonas sets the live borrows to other here... why? Shouldn't we do this in apply_statement_effect?
        
        /*
        FIXME: kills?
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
        let point = self.cgx.facts.location_table.borrow().as_ref().unwrap().mid_index(location);
        println!("[POST statement effect:      {:?}]", location);
        println!("  ** uo :   {:?}", self.get_universal_origins());
        println!("  ** ocla : {:?}", self.get_origin_contains_loan_at(location, false));
        println!("  ** oloe : {:?}", self.get_origin_contains_loan_at(location, false));


        // Update the graph: remove vertices and edges
        let g = state.graph.read();
        // update the graph: add new live vertices
        for k in self.get_origin_contains_loan_at(location, false).iter() {
            g.include_vertex(Vertex::untagged(*k));
        }

        // update the graph: add edges
        state.handle_outlives(location, statement.kind.assigns_to().map(|p| p.into()));
        state.reset_ops();


        println!("{}\n", state.graph.pretty()); 
    }

    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        let point = self.cgx.facts.location_table.borrow().as_ref().unwrap().start_index(location);
        // FIXME: same live borrows calculation here 
        println!("APPLY BEFORE TERMINATOR EFFECT");
        // println!("  ** live: {:?}", self.get_live_borrows_at(location, true));
        println!("{}\n", state.graph.pretty()); 
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
        let point = self.cgx.facts.location_table.borrow().as_ref().unwrap().mid_index(location);
        println!("APPLY TERMINATOR EFFECT");
        // println!("  ** live: {:?}", self.get_live_borrows_at(location, false));
        println!("{}\n", state.graph.pretty()); 
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
      */

        terminator.edges()
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