// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// use log::info;

use crate::{
    abstract_interpretation::{
        AbstractState, AnalysisResult, CouplingState, FactTable, StateLocation,
    },
    mir_utils::{self, expand, expand_struct_place, is_prefix, Place},
    PointwiseState,
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

use super::{Annotation, ReborrowingGraph};

// These types are stolen from Prusti interface
pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;
pub type PointIndex = <RustcFacts as FactTypes>::Point;
pub type Variable = <RustcFacts as FactTypes>::Variable;
pub type Path = <RustcFacts as FactTypes>::Path;

#[derive(Clone)]
pub struct ReborrowingState<'cpl, 'facts: 'cpl, 'mir: 'facts, 'tcx: 'mir> {
    pub reborrowing_dag: ReborrowingGraph<'tcx>,

    pub annotations_at: Vec<Annotation<'tcx>>,

    // // Location this state applies to (possibly in-between basic blocks)
    pub loc: StateLocation,

    pub(crate) mir: &'mir BodyWithBorrowckFacts<'tcx>,
    pub(crate) fact_table: &'facts FactTable<'tcx>,
    pub(crate) coupling: &'cpl PointwiseState<'mir, 'tcx, CouplingState<'facts, 'mir, 'tcx>>,
}

impl<'cpl, 'facts: 'cpl, 'mir: 'facts, 'tcx: 'mir> ReborrowingState<'cpl, 'facts, 'mir, 'tcx> {
    pub(crate) fn new_bottom(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        fact_table: &'facts FactTable<'tcx>,
        coupling: &'cpl PointwiseState<'mir, 'tcx, CouplingState<'facts, 'mir, 'tcx>>,
    ) -> Self {
        Self {
            reborrowing_dag: ReborrowingGraph::default(),
            loc: StateLocation::BeforeProgram,
            annotations_at: Default::default(),
            fact_table,
            mir,
            coupling,
        }
    }

    pub(crate) fn new_empty(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        fact_table: &'facts FactTable<'tcx>,
        coupling: &'cpl PointwiseState<'mir, 'tcx, CouplingState<'facts, 'mir, 'tcx>>,
    ) -> Self {
        // Idk if this is what we want.
        Self::new_bottom(mir, fact_table, coupling)
    }

    pub(crate) fn apply_terminator_effect(
        &self,
        location: Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self)>> {
        todo!("apply_terminator_effect");
        // let mut new_state = self.clone();
        // new_state.coupling_commands = Default::default();
        // new_state.elim_commands = Default::default();
        // new_state.cdg_step(location)?;

        // let joining_from = location.block;
        // let terminator = self.mir.body[location.block].terminator();
        // Ok(terminator
        //     .successors()
        //     .into_iter()
        //     .map(|bb| {
        //         let mut ns = new_state.clone();
        //         ns.loc = StateLocation::Joining(joining_from, bb);
        //         (bb, ns)
        //     })
        //     .collect())
    }

    pub(crate) fn apply_statement_effect(&mut self, location: Location) -> AnalysisResult<()> {
        println!("== statement effect at {:?}", location);
        println!("  (both)  MIR {:?}", self.mir.body.stmt_at(location));
        println!(
            "  (both)  intro commands: {:?}",
            self.fact_table.graph_operations.get(&location)
        );
        println!(
            "  (both)  delta leaves: {:?}",
            self.fact_table.delta_leaves.get(&location)
        );
        println!(
            "  (both)  loan issues: {:?}",
            self.fact_table.loan_issues.get(&location)
        );
        println!(
            "  (both)  origin_expires_before: {:?}",
            self.fact_table.origin_expires_before.get(&location)
        );
        if let Some(before) = self.coupling.lookup_before(location) {
            println!("  (before) st_loc: {:?}", before.loc);
            println!("  (before) cdg: {:?}", before.coupling_graph);
            println!("  (before) elim commands: {:?}", before.elim_commands);
            println!(
                "  (before) coupling commands: {:?}",
                before.coupling_commands
            );
        }
        if let Some(after) = self.coupling.lookup_after(location) {
            println!("  (after) st_loc: {:?}", after.loc);
            println!("  (after) cdg: {:?}", after.coupling_graph);
            println!("  (after) elim commands: {:?}", after.elim_commands);
            println!("  (after) coupling commands: {:?}", after.coupling_commands);
        }
        todo!("apply_statement_effect");
        // self.coupling_commands = Default::default();
        // self.elim_commands = Default::default();
        // self.loc = StateLocation::InsideBB(location.block);
        // self.cdg_step(location)
    }
}

impl<'cpl, 'facts: 'cpl, 'mir: 'facts, 'tcx: 'mir> PartialEq
    for ReborrowingState<'cpl, 'facts, 'mir, 'tcx>
{
    fn eq(&self, other: &Self) -> bool {
        self.reborrowing_dag == other.reborrowing_dag
            && self.annotations_at == other.annotations_at
            && self.loc == other.loc
    }
}

impl<'cpl, 'facts: 'cpl, 'mir: 'facts, 'tcx: 'mir> Eq
    for ReborrowingState<'cpl, 'facts, 'mir, 'tcx>
{
}

impl<'cpl, 'facts: 'cpl, 'mir: 'facts, 'tcx: 'mir> Serialize
    for ReborrowingState<'cpl, 'facts, 'mir, 'tcx>
{
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        todo!("Serialize reborrowing state");
    }
}

impl<'cpl, 'facts: 'cpl, 'mir: 'facts, 'tcx: 'mir> AbstractState
    for ReborrowingState<'cpl, 'facts, 'mir, 'tcx>
{
    fn is_bottom(&self) -> bool {
        todo!("is_bottom");
    }

    fn join(&mut self, other: &Self) {
        todo!("join");
    }

    fn widen(&mut self, _: &Self) {
        unreachable!("widening is not possible in this model")
    }
}
