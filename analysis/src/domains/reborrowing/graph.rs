// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::{
        place_deep_cap, Capability, ElimCommand, IntroStatement, OriginLHS, Resource, Tagged,
    },
    domains::FactTable,
    mir_utils::{self, expand, expand_struct_place, is_prefix, Place, PlaceImpl},
};
use prusti_rustc_interface::{
    borrowck::{consumers::RustcFacts, BodyWithBorrowckFacts},
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{
        mir,
        mir::{BasicBlock, Body, Location},
        ty::TyCtxt,
    },
    polonius_engine::FactTypes,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    io,
    marker::PhantomData,
};

// These types are stolen from Prusti interface
pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;
pub type PointIndex = <RustcFacts as FactTypes>::Point;
pub type Variable = <RustcFacts as FactTypes>::Variable;
pub type Path = <RustcFacts as FactTypes>::Path;

#[derive(Debug, Clone, Eq, Hash, PartialEq, PartialOrd, Ord)]
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

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ReborrowingGraph<'tcx>(pub BTreeMap<SubgraphID, ReborrowingGraphEntry<'tcx>>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReborrowingGraphEntry<'tcx> {
    children: BTreeSet<SubgraphID>,
    content: ReborrowingGraphKind<'tcx>,
}

/// The purpose of the reborrowing DAG is to track annotations.
///  These are steps that the a backend would have to take in order
///  to put all of the borrows back together while preserving values.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Annotation<'tcx> {
    // Package and apply collapsed (opaque) edges
    Package(OpaqueID, Vec<Annotation<'tcx>>),
    Apply(OpaqueID, PhantomData<&'tcx ()>),
    // Tag a place in the FPCS
    Snapshot(Capability<'tcx>, Location),
    // Borrows: details of issuing a borrow should be handled by OpSem. Same with Moves.
    ExpireBorrow(Capability<'tcx>, Tagged<Loan, Location>),
    //     moved into    moved from
    UnMove(Capability<'tcx>, Capability<'tcx>),
    // For coupling
    Freeze(Capability<'tcx>),
    Thaw(Capability<'tcx>),
    // ...
}

impl<'tcx> Annotation<'tcx> {
    pub fn kill_annotation<'mir>(
        &mut self,
        k: &OriginLHS<'tcx>,
        l: &Location,
        mir: &'mir Body<'tcx>,
    ) where
        'tcx: 'mir,
    {
        match self {
            &mut Annotation::Package(_, ref mut anns) => {
                for a in anns.iter_mut() {
                    a.kill_annotation(k, l, mir);
                }
            }
            &mut Annotation::ExpireBorrow(ref mut cap, ref mut loan) => {
                // If we should tag the cap, tag it
                if cap.should_tag(&(k.clone().into_cap(mir))) {
                    cap.kill(l);
                }

                // If we should tag the loan, tag it
                if let OriginLHS::Loan(l0) = k {
                    if !loan.is_tagged() && loan.data == *l0 {
                        loan.tag(*l);
                    }
                }
            }
            &mut Annotation::UnMove(ref mut c0, ref mut c1) => {
                if c0.should_tag(&(k.clone().into_cap(mir))) {
                    c0.kill(l);
                }
                if c1.should_tag(&(k.clone().into_cap(mir))) {
                    c1.kill(l);
                }
            }

            _ => {
                unimplemented!("unknown how to kill {:?} at {:?} in {:?}", k, l, self);
            }
        }
    }
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
    // Make a new concrete edge
    // panic if that origin already has an edge
    fn new_concrete(
        &mut self,
        trg: SubgraphID,
        anns: Vec<Annotation<'tcx>>,
        children: BTreeSet<SubgraphID>,
    ) {
        let entry = ReborrowingGraphEntry {
            children,
            content: ReborrowingGraphKind::Concrete(anns),
        };
        assert!(self.0.insert(trg, entry).is_none())
    }

    // Apply an intro command to the graph, and translate it into a sequence of annotations.
    pub(crate) fn apply_intro_command<'mir>(
        &mut self,
        stmt: &IntroStatement<'tcx>,
        mir: &'mir Body<'tcx>,
        fact_table: &FactTable<'tcx>,
    ) -> Vec<Annotation<'tcx>>
    where
        'tcx: 'mir,
    {
        match stmt {
            IntroStatement::Kill(k, l) => {
                // Emit an annotation at the current location that kills the place (actually, do we need to do this?)
                // Maybe just modify the annotations instead? This is not a _consume_.

                // What kind of annotations does this entail?
                // Snapshot?
                self.do_kill(k, l, mir);
                [Annotation::Snapshot((*k).clone().into_cap(&mir), *l)].into()
            }

            IntroStatement::Assign(from, to) => {
                let move_to_origin = fact_table
                    .origins
                    .get_origin(mir, OriginLHS::Place((*to).clone()))
                    .unwrap();
                let move_from_origin = fact_table.origins.get_origin(mir, (*from).clone()).unwrap();
                self.new_concrete(
                    SubgraphID {
                        0: [move_to_origin].into(),
                    },
                    [Annotation::UnMove(
                        Capability {
                            resource: Resource::Place(to.clone()),
                            permission: Tagged::untagged(place_deep_cap(&mir, &to).unwrap()),
                        },
                        ((*from).clone()).into_cap(&mir),
                    )]
                    .into(),
                    [SubgraphID {
                        0: [move_from_origin].into(),
                    }]
                    .into(),
                );

                // Opsem should handle statements for this assignment
                [].into()
            }
            IntroStatement::Reborrow(rb_from_place, rb_loan, rb_from_region) => {
                // Add annotations that expire this reborrow
                let issuing_origin = fact_table
                    .origins
                    .get_origin(mir, OriginLHS::Loan(*rb_loan))
                    .unwrap();
                self.new_concrete(
                    SubgraphID {
                        0: [issuing_origin].into(),
                    },
                    [Annotation::ExpireBorrow(
                        Capability {
                            resource: Resource::Place(rb_from_place.clone()),
                            permission: Tagged::untagged(
                                place_deep_cap(&mir, &rb_from_place).unwrap(),
                            ),
                        },
                        Tagged::untagged(rb_loan.clone()),
                    )]
                    .into(),
                    [SubgraphID {
                        0: [*rb_from_region].into(),
                    }]
                    .into(),
                );
                // No annotations needed atm.
                // fixme: Unless we need to repack, in which case they get put here?
                // Or does OpSem handle it
                [].into()
            }
            IntroStatement::Borrow(from, ix) => {
                // Add annotations that expire this borrow
                // Get the origin associated to ix, put a transparent edge
                let issuing_origin = fact_table
                    .origins
                    .get_origin(mir, OriginLHS::Loan(*ix))
                    .unwrap();
                self.new_concrete(
                    SubgraphID {
                        0: [issuing_origin].into(),
                    },
                    [Annotation::ExpireBorrow(
                        Capability {
                            resource: Resource::Place(from.clone()),
                            permission: Tagged::untagged(place_deep_cap(&mir, &from).unwrap()),
                        },
                        Tagged::untagged(ix.clone()),
                    )]
                    .into(),
                    [].into(),
                );

                // No annotations needed at the current point; that is the
                // responsibility of the owned opsem
                [].into()
            }
        }
    }

    pub(crate) fn apply_elim_command(&mut self, stmt: &ElimCommand<'tcx>) -> Vec<Annotation<'tcx>> {
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

    fn do_kill<'mir>(&mut self, k: &OriginLHS<'tcx>, l: &Location, mir: &'mir Body<'tcx>)
    where
        'tcx: 'mir,
    {
        for (_, subg_content) in self.0.iter_mut() {
            match &mut subg_content.content {
                ReborrowingGraphKind::Concrete(anns) => {
                    for a in anns.iter_mut() {
                        a.kill_annotation(k, l, mir);
                    }
                }
                ReborrowingGraphKind::Transparent(mp, _) => {
                    for (_, anns) in mp.iter_mut() {
                        for a in anns.iter_mut() {
                            a.kill_annotation(k, l, mir);
                        }
                    }
                }
                ReborrowingGraphKind::Opqaue(_, _) => unimplemented!(
                    "what annotations do we need to kill part of an opaque edge? maybe none?"
                ),
            }
        }
    }

    pub(crate) fn collapse(&mut self, origins: BTreeSet<Region>) {
        todo!();
    }
}
