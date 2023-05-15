// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use std::{
    collections::{BTreeMap, BTreeSet},
    io,
    marker::PhantomData,
};

use crate::{
    abstract_interpretation::{CDGNode, ElimCommand, IntroStatement},
    mir_utils::{self, expand, expand_struct_place, is_prefix, Place, PlaceImpl},
};
use prusti_rustc_interface::{
    borrowck::{consumers::RustcFacts, BodyWithBorrowckFacts},
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{
        mir,
        mir::{BasicBlock, Location},
        ty::TyCtxt,
    },
    polonius_engine::FactTypes,
};

// These types are stolen from Prusti interface
pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;
pub type PointIndex = <RustcFacts as FactTypes>::Point;
pub type Variable = <RustcFacts as FactTypes>::Variable;
pub type Path = <RustcFacts as FactTypes>::Path;

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct SubgraphID(BTreeSet<Region>);

pub type OpaqueID = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConditionValue(pub u128);

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
pub struct ConditionId {
    value: ConditionValue,
    start: mir::BasicBlock,
}

/// The reborrowing graph is described by a collectionn of disjoint subgraphs.
///   Each subgraph has an ID, each subgraph must connect to all of its children.

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReborrowingGraph<'tcx>(pub BTreeMap<SubgraphID, ReborrowingGraphEntry<'tcx>>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReborrowingGraphEntry<'tcx> {
    children: BTreeSet<SubgraphID>,
    content: ReborrowingGraphKind<'tcx>,
}

/// The purpose of the reborrowing DAG is to track annotations.
///  These are steps that the a backend would have to take in order
///  to put all of the borrows back together while preserving values.
///
/// That said... we decided that the rbdag doesn't need to remain in sync
/// with the PCS. So in between each of these annotations, we may need
/// to call the FPCS to repack. An alternate design would include these edges here.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Annotation<'tcx> {
    // Package and apply collapsed (opaque) edges
    Package(OpaqueID, Vec<Annotation<'tcx>>),
    Apply(OpaqueID, PhantomData<&'tcx ()>),
    // Tag a place in the FPCS
    TagAt(CDGNode<'tcx>, Location),
    // ...
}

///   It does not have to interacct with the free PCS, nor does it have to know
///   why it's legal to emit some annotation. That is the job of the coupling
///   graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReborrowingGraphKind<'tcx> {
    // A sequence of annotations to emit on expiry
    Concrete(Vec<Annotation<'tcx>>),
    // A sequence of (condition-dependent) annotations to be added at a later point.
    Transparent(
        BTreeMap<ConditionId, Vec<Annotation<'tcx>>>,
        Box<Vec<SubgraphID>>,
    ),
    // A dynamic edge that is only populated at verification-time
    Opqaue(OpaqueID, PhantomData<&'tcx ()>),
}

impl<'tcx> ReborrowingGraph<'tcx> {
    pub(crate) fn apply_intro_command(
        &mut self,
        stmt: IntroStatement<'tcx>,
    ) -> Vec<Annotation<'tcx>> {
        match stmt {
            IntroStatement::Kill(_) => {
                // Emit an annotation at the current location that kills the place (actually, do we need to do this?)
                // Maybe just modify the annotations instead? This is not a _consume_.
                todo!()
            }

            IntroStatement::Assign(_, _) => {
                // Do any annotations need to be emitted in this case?
                // Modify the annotation in the related origin?
                // Not sure what is needed to propagate values in backends...
                todo!()
            }
            IntroStatement::Reborrow(_, _, _) => {
                // Add annotations that expire this reborrow
                todo!()
            }
            IntroStatement::Borrow(_, _) => {
                // Add annotations that expire this borrow
                todo!()
            }
        }
    }

    pub(crate) fn apply_elim_command(&mut self, stmt: ElimCommand<'tcx>) -> Vec<Annotation<'tcx>> {
        match stmt {
            ElimCommand::Consume(_) => {
                // Emit an annotation at the current location to snapshot a place,
                // removing it from the PCS and tagging all instances in the graph.
                todo!()
            }
            ElimCommand::Expire(_, _) => {
                // Emit the annotations associated to an origin and remove that origin from the graph.
                todo!();
            }
        }
    }

    pub(crate) fn collapse(&mut self, origins: BTreeSet<Region>) {
        todo!();
    }
}
