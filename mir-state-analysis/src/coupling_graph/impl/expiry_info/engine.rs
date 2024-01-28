// © 2024, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.


#![allow(unused_imports)]

use std::cell::RefCell;
use std::ops::ControlFlow;
use std::rc::Rc;
use std::{cell::Cell, collections::BTreeSet};
use std::fmt::Formatter;

use prusti_interface::environment::borrowck::facts::{BorrowckFacts, AllOutputFacts};
use prusti_interface::environment::mir_body::borrowck::{facts::LocationTable, lifetimes::Lifetimes};
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

use super::expiry_error::{ExpiryError, ExpiryResult};
use super::graph::Vertex;
use super::lazy_coupling::LazyCoupling;
use super::{graph::Eg, control_flow::ControlFlowFlag};

pub(crate) struct ExpiryInfo<'a, 'tcx> {
    pub(crate) cgx: &'a CgContext<'a, 'tcx>,
    // FIXME: This is here because I can't figure out how to populate the cgx output facts
    output_facts: prusti_rustc_interface::borrowck::consumers::PoloniusOutput,
    bb_index: Cell<BasicBlock>,

    #[allow(unused)]
    top_crates: bool,
}

impl<'a, 'tcx> ExpiryInfo<'a, 'tcx> {
    pub(crate) fn new(cgx: &'a CgContext<'a, 'tcx>, top_crates: bool) -> ExpiryResult<Self> {
        // FIXME: can we reuse these facts from somewhere else? 
        let input_facts = cgx.facts.input_facts.borrow().as_ref().unwrap().clone();
        let output_facts = prusti_rustc_interface::polonius_engine::Output::compute(
            &input_facts,
            prusti_rustc_interface::polonius_engine::Algorithm::Naive,
            true,
        );
        Ok(Self { cgx, bb_index: Cell::new(START_BLOCK), output_facts, top_crates })
    }

    pub(crate) fn get_origin_contains_loan_at(&self, location: Location, start: bool) -> Vec<RegionVid> {
        // FIXME: extremely frusturating: I can't just pass around LocationIndex values because I can't import that type????
        // Maybe a macro or something is the more idiomatic solution to this
        let table = self.cgx.facts.location_table.borrow();
        let point = 
            if start { table.as_ref().unwrap().start_index(location) } 
            else { table.as_ref().unwrap().mid_index(location) };
        self.output_facts
            .origin_contains_loan_at
            .get(&point)
            .map(|m| m.keys().cloned().collect::<Vec<_>>())
            .unwrap_or(vec![])
    }

    pub(crate) fn get_universal_origins(&self) -> Vec<RegionVid> {
        self.cgx.facts.input_facts.borrow().clone().unwrap().universal_region
    }
}



#[derive(Clone)]
pub(crate) struct Exg<'a, 'tcx> {
    pub cgx: &'a CgContext<'a, 'tcx>,
    pub output_facts: prusti_rustc_interface::borrowck::consumers::PoloniusOutput,
    pub graph: LazyCoupling,
    pub is_pre : bool, 

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
        let (_, g) = self.graph.read();
        let location = Location { block: START_BLOCK, statement_index: 0 };
        let point = self.cgx.facts.location_table.borrow().as_ref().unwrap().start_index(location);
        for r in self.output_facts.origin_live_on_entry.get(&point).unwrap().iter() {
            g.add_vertex(Vertex::untagged(*r));
        }
        self.graph.set_location(location);
        // TODO: Add universal edges, when they exist
    }

    pub(crate) fn reset_ops(&mut self) {
        // TODO: Implement ops tracking
    }

    pub fn handle_outlives(&mut self, location: Location, assigns_to: Option<MirPlace<'tcx>>) {
        let local = assigns_to.clone().map(|a| a.local);

        // IIUC this avoids susbets due to type ascriptions? 
        for &c in self
            .cgx
            .outlives_info
            .pre_constraints(location, local, &self.cgx.region_info)
        {
            self.outlives(c);
        }

        // No need to handle kills in this analysis 

        for &c in self
            .cgx
            .outlives_info
            .post_constraints(location, local, &self.cgx.region_info)
        {
            self.outlives(c);
        }
    }

    /// Handle a single outlives constraint by adding a new group to the graph
    pub fn outlives(&mut self, c: OutlivesConstraint) {
        self.graph.read().1.issue_group(Vertex::untagged(c.sub), [Vertex::untagged(c.sup)].into_iter().collect());
    }
}

impl<'a, 'tcx> JoinSemiLattice for Exg<'a, 'tcx> {
    // I think as written, this is OK.
    // If the compiler tries to do joins at locations other than join points, this could pose a problem
    fn join(&mut self, other: &Self) -> bool {
        if self.is_pre && other.is_pre {
            return false; 
        } else if self.is_pre && !other.is_pre {
            *self = other.clone();
            return true;
        } else if !self.is_pre && other.is_pre {
            return false; 
        }
        // Otherwise, both are not pre. We construct a lazy coupling. 

        let r = Self { 
            cgx: self.cgx,
            output_facts: self.output_facts.clone(),
            graph: self.graph.join(&other.graph, &self.cgx.rp.body().basic_blocks),
            is_pre: false };
        *self = r; 
        return true;
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
        // This is a part of Jonas' analysis I do not understand 
        // When is bottom_value called? If it can be called at any location, 
        // we may need to set the location appropriately (ie, is it expecting X \wedge \bot = X?)
        let block = self.bb_index.get();
        self.bb_index.set(block.plus(1));

        Exg {
            cgx: self.cgx,
            graph: LazyCoupling::Done(Location { block, statement_index: 0, }, Eg::default()),
            output_facts: self.output_facts.clone(),
            is_pre : true
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
        _statement: &Statement<'tcx>,
        location: Location,
    ) {
        state.is_pre = false; 
        state.reset_ops();
        println!("[PRE statement effect:      {:?}]", location);

        // Get a coherent graph 
        if location.statement_index == 0 { state.graph.shoot(self.cgx); }
        state.graph.set_location(location);
        let (_, g) = state.graph.read();

        // Expire all dead vertices
        let mut to_retain = self.get_universal_origins().into_iter().map(|x| x).collect::<Vec<_>>();
        for r in self.get_origin_contains_loan_at(location, true) {
            to_retain.push(r);
        }
        g.expire_except(location, to_retain);

        // debug: we should not have any new vertices
        println!("  ** uo :   {:?}", self.get_universal_origins());
        println!("  ** ocla : {:?}", self.get_origin_contains_loan_at(location, true));
        println!("{}\n", state.graph.pretty()); 
    }

    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        state.is_pre = false; 
        state.reset_ops();
        println!("[POST statement effect:      {:?}]", location);
        println!("  ** uo :   {:?}", self.get_universal_origins());
        println!("  ** ocla : {:?}", self.get_origin_contains_loan_at(location, false));

        // Update the graph: Add new vertices and edges
        state.graph.set_location(location);
        let (_, g) = state.graph.read();
        for k in self.get_origin_contains_loan_at(location, false).iter() {
            g.include_vertex(Vertex::untagged(*k));
        }
        state.handle_outlives(location, statement.kind.assigns_to().map(|p| p.into()));

        println!("{}\n", state.graph.pretty()); 
    }

    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        _terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        state.is_pre = false; 
        // let point = self.cgx.facts.location_table.borrow().as_ref().unwrap().start_index(location);

        // FIXME: same live borrows calculation here 
        println!("APPLY BEFORE TERMINATOR EFFECT");
        state.graph.set_location(location);

        println!("{}\n", state.graph.pretty()); 
    }

    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        state.is_pre = false; 
        // let point = self.cgx.facts.location_table.borrow().as_ref().unwrap().mid_index(location);
        println!("APPLY TERMINATOR EFFECT");

        state.graph.set_location(location);
        // println!("  ** live: {:?}", self.get_live_borrows_at(location, false));
        println!("{}\n", state.graph.pretty()); 
        // todo!();
        /*
        state.reset_ops();
        state.handle_outlives(location, terminator.kind.assigns_to());
        state.visit_terminator(terminator, location);

        match &terminator.kind {
            TerminatorKind::Return => {
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
        // Nothing to do here? 
    }
}