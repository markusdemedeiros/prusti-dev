// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]
use crate::{
    model::Resource::*,
    util::{preprocess_mir, EncodingResult},
};
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
// Permissions (Free PCS)
#[derive(Eq, Hash, PartialEq, Clone)]
pub enum Resource<T>
where
    T: Clone,
{
    Exclusive(T),
    Shared(T),
    Uninit(T),
    Blocked(T),
}

impl<'tcx> Debug for Resource<mir::Place<'tcx>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Exclusive(r) => write!(f, "e {:?}", r),
            Shared(r) => write!(f, "s {:?}", r),
            Uninit(r) => write!(f, "u {:?}", r),
            Blocked(r) => write!(f, "b {:?}", r),
        }
    }
}

impl<'tcx> Resource<mir::Place<'tcx>> {
    // Todo: Why can't I use functors again?
    pub fn local_permission(&self) -> Resource<mir::Local> {
        match self {
            Exclusive(r) => Exclusive(r.local),
            Shared(r) => Shared(r.local),
            Uninit(r) => Uninit(r.local),
            Blocked(r) => Blocked(r.local),
        }
    }
}

impl<T> Resource<T>
where
    T: Clone,
{
    pub fn permission_of(&self) -> &T {
        match self {
            Exclusive(t) => t,
            Shared(t) => t,
            Uninit(t) => t,
            Blocked(t) => t,
        }
    }

    pub fn is_uninit(&self) -> bool {
        if let Uninit(_) = self {
            true
        } else {
            false
        }
    }

    pub fn is_exclusive(&self) -> bool {
        if let Exclusive(_) = self {
            true
        } else {
            false
        }
    }
}

pub type Permission<'tcx> = Resource<mir::Place<'tcx>>;

#[derive(Clone, Debug, PartialEq)]
pub struct PermissionSet<'tcx>(pub FxHashSet<Permission<'tcx>>);

impl<'tcx> Default for PermissionSet<'tcx> {
    fn default() -> Self {
        PermissionSet {
            0: FxHashSet::default(),
        }
    }
}

impl<'tcx> PermissionSet<'tcx> {
    pub fn from_vec(vec: Vec<Permission<'tcx>>) -> Self {
        PermissionSet {
            0: vec.iter().cloned().collect(),
        }
    }
}

pub fn usize_place<'tcx>(id: usize) -> mir::Place<'tcx> {
    mir::Local::from_usize(id).into()
}

////////////////////////////////////////////////////////////////////////////////
// Guarded PCS

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum PlaceHole<'tcx> {
    Linear(mir::Place<'tcx>),
    NonLinear(mir::Place<'tcx>),
    None,
}

pub type Tag = mir::Location;

#[derive(Clone, PartialEq, Debug)]
pub struct Tagged<T> {
    pub item: T,
    pub tag: Option<Tag>,
}

impl<'tcx> Debug for PlaceHole<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            PlaceHole::Linear(r) => write!(f, "LN {:?}", r),
            PlaceHole::NonLinear(r) => write!(f, "NL {:?}", r),
            PlaceHole::None => write!(f, "NONE"),
        }
    }
}

pub type JoinPoint = usize;

pub type JoinPath = usize;

// Essentially: Tree of join points
pub enum GuardExpr {
    Top,
    ThroughJoin(JoinPoint, JoinPath),
    And(Box<GuardExpr>),
}

#[derive(Clone, PartialEq)]
pub struct Guard<'tcx> {
    pub label: Loan,
    pub rhs: Option<Tagged<Permission<'tcx>>>,
    // Generalization: for struct with borrow RHS can be not top-level place
    pub lhs: Vec<Tagged<PlaceHole<'tcx>>>,
}

impl<'tcx> Debug for Guard<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{:?}: {:?} --* {:?}", self.label, self.lhs, self.rhs)
    }
}

impl<'tcx> Guard<'tcx> {
    pub fn nop_guard(label: Loan) -> Self {
        Guard {
            label,
            rhs: None,
            lhs: vec![],
        }
    }

    pub fn expiry_requirements(&self) -> Vec<Permission<'tcx>> {
        self.lhs
            .iter()
            .filter_map(|t| match t.item {
                PlaceHole::None => None,
                PlaceHole::NonLinear(_) => todo!(),
                PlaceHole::Linear(pl) => Some(Exclusive(pl.clone())),
            })
            .collect()
    }

    pub fn fill_hole(&mut self, fill: &PlaceHole<'tcx>) {
        for t in self.lhs.iter_mut() {
            if t.item == *fill {
                t.item = PlaceHole::None;
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct GuardSet<'tcx>(Vec<Guard<'tcx>>);

impl<'tcx> Default for GuardSet<'tcx> {
    fn default() -> Self {
        GuardSet { 0: Vec::default() }
    }
}

impl<'tcx> GuardSet<'tcx> {
    pub fn get_guarded_places(&self) -> Vec<Permission<'tcx>> {
        self.0
            .iter()
            .filter_map(|g| g.rhs.as_ref())
            .map(|t| (t.item).clone())
            .collect::<Vec<_>>()
    }

    pub fn get_loans(&self) -> Vec<&Loan> {
        self.0.iter().map(|g| &g.label).collect::<Vec<_>>()
    }

    pub fn insert_guard(&mut self, guard: Guard<'tcx>) {
        // TODO: What happens when we indert a fake loan which is already in there?
        if let Some(rhs) = &guard.rhs {
            assert!(!self.get_guarded_places().contains(&(rhs.item)));
        }
        self.0.push(guard);
    }

    pub fn get_expiry_requirements(&self, label: Loan) -> Vec<Permission<'tcx>> {
        // 1. Assert that the loan must be guarded by the GPCS
        let matches = self
            .0
            .iter()
            .filter(|g| g.label == label)
            .collect::<Vec<_>>();

        match matches[..] {
            [v] => v.expiry_requirements(),
            _ => todo!(),
        }
    }

    /// Fill a PlaceHole across all loans
    pub fn eliminate_hole(&mut self, to_eliminate: PlaceHole<'tcx>) {
        for guard in self.0.iter_mut() {
            guard.fill_hole(&to_eliminate)
        }
    }

    /// Expect all preconditions to be None, and remove
    pub fn eliminate_loan(&mut self, to_eliminate: Loan) -> Vec<Permission<'tcx>> {
        let mut matches = self
            .0
            .iter_mut()
            .enumerate()
            .filter(|(_, g)| g.label == to_eliminate);

        let (egi, guard_to_kill) = matches.next().unwrap();
        assert!(matches.next() == None);
        assert!(guard_to_kill.expiry_requirements() == vec![]);

        let g = self.0.remove(egi);
        vec![g.rhs.unwrap().item]
    }

    pub fn move_loan(
        &mut self,
        to_eliminate: &mir::Place<'tcx>,
        new_guard: &mir::Place<'tcx>,
        bb: mir::BasicBlock,
    ) {
        // Map over all the possible LHS's.
        // If to_eliminate is blocking any loan, now new_guard is blocking that loan
        //  (conditionally)

        todo!();
        {
            for p in self.0.iter_mut() {
                for t in p.lhs.iter_mut() {
                    match t.item {
                        PlaceHole::Linear(h) => {
                            if h == *to_eliminate {
                                h = *new_guard;
                            }
                        }
                        PlaceHole::NonLinear(h) => todo!(),
                        PlaceHole::None => {}
                    }
                }
            }
        }

        // for p in self
        //     .0
        //     .iter()
        //     .filter_map(|g| g.rhs.as_ref())
        //     .map(|g| g.permission_of())
        // {
        //     println!("\t all blocked places {:?}", p);
        // }

        // let mut matches = self.0.iter_mut().enumerate().filter(|(_, g)| {
        //     if let Some(rhs) = &g.rhs {
        //         rhs.permission_of() == to_eliminate
        //     } else {
        //         false
        //     }
        // });

        // let (egi, mut guard_to_move) = matches.next().unwrap();
        // assert!(matches.next() == None);

        // guard_to_move.lhs = vec![(bb, PlaceHole::Linear((*new_guard).clone()))];
    }

    /// Return a collection of loans to be culled
    pub fn get_cullable_loans(&mut self, remaining_loans: Vec<Loan>) -> FxHashSet<Loan> {
        let current_loans = self.0.iter().map(|g| &g.label).collect::<FxHashSet<_>>();
        let rm_loans = remaining_loans.iter().collect::<FxHashSet<_>>();
        assert!(rm_loans.is_subset(&current_loans));
        (&current_loans - &rm_loans).into_iter().cloned().collect()
    }

    /// Given a set of loans which need to remain, remove all other guards
    ///     Eagerly fill holes and build up a contract for the free PCS
    pub fn cull_loans(
        &mut self,
        remaining_loans: Vec<Loan>,
    ) -> (FxHashSet<Permission<'tcx>>, FxHashSet<Permission<'tcx>>) {
        let mut free_requirement: FxHashSet<Permission<'tcx>> = FxHashSet::default();
        let mut free_ensures: FxHashSet<Permission<'tcx>> = FxHashSet::default();
        let mut lhs_union: FxHashSet<PlaceHole<'tcx>> = FxHashSet::default();
        let mut culled: FxHashSet<Loan> = FxHashSet::default();
        for loan in self.get_cullable_loans(remaining_loans).iter() {
            // For every one of the loans to kill
            //      Find the loan
            //      Add the LHS into free requirements
            //      Remove that requirement from every LHS
            //      Pop the culled loans from the list
            let g = self
                .0
                .iter_mut()
                .filter(|gg| gg.label == *loan)
                .next()
                .unwrap();

            for req in g.lhs.iter() {
                lhs_union.insert((req.item).clone());
            }

            if let Some(r) = &g.rhs {
                free_ensures.insert((r.item).clone());
            }

            culled.insert(*loan);
        }

        let mut possible_uninits = lhs_union.clone();

        for hole in lhs_union.into_iter() {
            if let PlaceHole::Linear(p) = hole {
                free_requirement.insert(Exclusive(p));
            }
            self.eliminate_hole(hole);
        }

        self.0.retain(|g| !culled.contains(&g.label));

        for g in self.0.iter() {
            // Retain if it's not a LHS
            possible_uninits.retain(|hole| !g.lhs.iter().any(|t| t.item == *hole));
        }

        // TODO: Should we really do this eagerly?
        for pu in possible_uninits.iter() {
            match pu {
                // Once a place is no longer a guard we get it's uninit permission again
                PlaceHole::Linear(p) => {
                    free_ensures.insert(Uninit(*p));
                }
                PlaceHole::NonLinear(p) => todo!(),
                PlaceHole::None => (),
            }
        }

        // Ignore intermediate permissions
        let req_diff = &free_requirement - &free_ensures;
        let ens_diff = &free_ensures - &free_requirement;

        (req_diff, ens_diff)
    }

    pub fn is_empty(&self) -> bool {
        self.0.len() == 0
    }

    pub fn kill_loan(&mut self, to_kill: Vec<Loan>, location: mir::Location) {
        // Tag the RHS of all loans killed at this location
        todo!();
    }
}

////////////////////////////////////////////////////////////////////////////////
// State

#[derive(Clone, PartialEq)]
pub struct PCSState<'tcx> {
    pub free: PermissionSet<'tcx>,
    pub guarded: GuardSet<'tcx>,
}

impl<'tcx> Default for PCSState<'tcx> {
    fn default() -> Self {
        PCSState {
            free: PermissionSet {
                0: FxHashSet::from_iter(vec![Uninit(usize_place(0))].iter().cloned()),
            },
            guarded: GuardSet::default(),
        }
    }
}

impl<'tcx> PCSState<'tcx> {
    // Adds in a new loan at the current point
    // Guards the
    pub fn issue_guard_for_loan<'mir>(&mut self, guard: Guard<'tcx>) {
        self.guarded.insert_guard(guard);
    }
}

impl<'tcx> Debug for PCSState<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{{ ")?;
        for s in self.free.0.iter() {
            write!(f, "{:?}, ", s)?;
        }
        write!(f, "}} [ ")?;
        for l in self.guarded.0.iter() {
            write!(f, "{:?}, ", l)?;
        }
        write!(f, "]")
    }
}

pub struct PCS<'mir, 'tcx: 'mir> {
    // Body only consists of accepted statements (otherwise, turn to nop)
    body: &'mir mir::Body<'tcx>,

    //
    before_pcs: FxHashMap<mir::Location, PCSState<'tcx>>,

    // Our annotations, between MIR statementds
    // Interp. (polonius) an edge from a mid-point to a start-point
    //
    //                  (before pcs)
    //                       |
    //  --- Start location -->-- Statement -->-- Mid Location -->-- edge_block -->-- Start Location
    //                                                        -->-- (potentially many edge blocks)
    edge_blocks: FxHashMap<(mir::Location, mir::Location), EdgeBlock<'tcx>>,
}

pub struct EdgeBlock<'tcx> {
    statements: Vec<FreeStatement<'tcx>>,
    before_pcs: Vec<PCSState<'tcx>>,
}

#[derive(Debug)]
pub enum FreeStatement<'tcx> {
    Pack(Vec<Permission<'tcx>>, Permission<'tcx>),
    Unpack(Permission<'tcx>, Vec<Permission<'tcx>>),
    Weaken(Permission<'tcx>, Permission<'tcx>),
    // Nop,
    // Permission lattice weakening
    // Set control flow variable
}
