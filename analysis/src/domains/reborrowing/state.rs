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

// use super::{Annotation, ReborrowingGraph};

// These types are stolen from Prusti interface
pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;

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
            reborrowing_dag: Default::default(),
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
        // Terminators don't change the graph right?
        // I guess the will change the graph with function callls
        // We couple at the start of blocks?

        let terminator = self.mir.body[location.block].terminator();
        Ok(terminator
            .successors()
            .into_iter()
            .map(|bb| (bb, self.clone()))
            .collect())
    }

    pub(crate) fn apply_statement_effect(&mut self, location: Location) -> AnalysisResult<()> {
        println!("\n========== statement effect at {:?}", location);
        println!("  (both)  MIR {:?}", self.mir.body.stmt_at(location));
        println!(
            "  (both)  intro commands: {:?}",
            self.fact_table.graph_operations.get(&location)
        );
        let (delta_leaves_pre, delta_leaves_post) = self
            .fact_table
            .delta_leaves
            .get(&location)
            .map(|(v0, v1)| ((*v0).clone(), (*v1).clone()))
            .unwrap_or_default();

        println!(
            "  (both)  delta leaves: {:?}",
            (&delta_leaves_pre, &delta_leaves_post)
        );
        println!(
            "  (both)  loan issues: {:?}",
            self.fact_table.loan_issues.get(&location)
        );
        println!(
            "  (both)  origin_expires_before: {:?}",
            self.fact_table.origin_expires_before.get(&location)
        );

        let after = self.coupling.lookup_after(location).unwrap();

        println!("  (after) cdg: {:?}", after.coupling_graph);
        println!("  (after) elim commands: {:?}", after.elim_commands);
        println!("  (after) coupling commands: {:?}", after.coupling_commands);

        println!(
            "unimplemented: repack so that {:?} is in the PCS",
            delta_leaves_pre
        );

        if let Some(intros) = self.fact_table.graph_operations.get(&location) {
            for st in intros.iter() {
                self.annotations_at =
                    self.reborrowing_dag
                        .apply_intro_command(st, &self.mir.body, &self.fact_table);
            }
        }

        for cmd in after.elim_commands.iter() {
            self.annotations_at
                .append(&mut (self.reborrowing_dag.apply_elim_command(cmd)));
        }

        for cmd in after.coupling_commands.iter() {
            panic!("nontrivial coupling command");
            // self.annotations_at
            //     .append((self.reborrowing_dag.apply_elim_command(cmd)));
        }

        println!("reborrowing step done: ");
        println!("{:?}", self.reborrowing_dag);

        Ok(())
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
        // Maybe loc too?
        self.reborrowing_dag.is_empty()
    }

    fn join(&mut self, other: &Self) {
        // Filter out trivial cases (this is a substantial number of the joins in MIR).
        let mut states_to_join = vec![self.clone(), other.clone()];
        states_to_join = states_to_join
            .into_iter()
            .filter(|st| !st.is_bottom())
            .collect();
        match &states_to_join[..] {
            [] => (),
            [z] => {
                *self = (*z).clone();
                return;
            }
            _ => (),
        };
        todo!("join");
    }

    fn widen(&mut self, _: &Self) {
        unreachable!("widening is not possible in this model")
    }
}
