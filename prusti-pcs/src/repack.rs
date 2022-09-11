// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]
use crate::{
    cfgiter::{DirtyBlock, PCSIter},
    model::{FreeStatement::*, Resource::*, *},
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

// PCS UNIFICATIONS WITH SOUND WEAKENING

// interp. Perfrom these in sequence.
#[derive(Debug)]
pub struct RepackWeaken<'tcx> {
    exclusive_unpack: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)>,
    exclusive_pack: Vec<(FxHashSet<mir::Place<'tcx>>, mir::Place<'tcx>)>,
    exclusive_weaken: FxHashSet<mir::Place<'tcx>>,
    uninit_unpack: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)>,
    uninit_pack: Vec<(FxHashSet<mir::Place<'tcx>>, mir::Place<'tcx>)>,
}

// Take two PCS's CUR, NEXT
//
// We have the following FREE PCS operations at our disposal
//  { unpack (e p) ...} { e p ...}        PACK   (unpack (e p)) (e p)
//  { e p ...} { unpack (e p) ...}        UNPACK (e p) (unpack (e p))
//  { e p } { u p }                       WEAKEN (e p)          (u p)
//
// The algorithm is as follows:
//      1. Turn the two PCS's into their most unpacked state
//           for uninit perms only ~> PACK + (reverse PACK)
//      2. Check for any weakening situations (required but not given)
//      2.5. Add uninit requirements to exclusive problem's postcondition
//      3. Turn the two PCS's into their most unpack state for
//          exclusive places only
//
//
// The string of generated annotations must be coherent and it's result
// should contain pcs_to

// TO DO NEXT:
//   Encode to the actual list of Free statements with pcs across them
//   Add in runtime init check (hopefully does nothing but might be needed for
//      init at loop heads and joins (or maybe just use them at join points lmfao))
//  Check coherence on examples
impl<'tcx> RepackWeaken<'tcx> {
    pub fn repack_weaken<'mir, 'env: 'mir>(
        // Context
        tcx: TyCtxt<'tcx>,
        mir: &'mir mir::Body<'tcx>,
        env: &'env Environment<'tcx>,
        // Repack pcs_from into pcs_to
        pcs_from: PermissionSet<'tcx>,
        pcs_to: PermissionSet<'tcx>,
    ) -> Self
    where
        'tcx: 'env,
    {
        let mut uninit_problems: FxHashMap<
            mir::Local,
            (FxHashSet<mir::Place<'tcx>>, FxHashSet<mir::Place<'tcx>>),
        > = FxHashMap::default();

        // Setup the problem
        for place in pcs_from
            .0
            .iter()
            .filter_map(|perm| if let Uninit(p) = perm { Some(p) } else { None })
        {
            let local = place.local.clone();
            let set_borrow = uninit_problems
                .entry(local)
                .or_insert((FxHashSet::default(), FxHashSet::default()));
            (*set_borrow).0.insert(place.clone());
        }

        for place in pcs_to
            .0
            .iter()
            .filter_map(|perm| if let Uninit(p) = perm { Some(p) } else { None })
        {
            let local = place.local.clone();
            let set_borrow = uninit_problems
                .entry(local)
                .or_insert((FxHashSet::default(), FxHashSet::default()));
            (*set_borrow).1.insert(place.clone());
        }

        // Repack the exclusive permissions
        let mut uninit_pack_stack: Vec<(FxHashSet<mir::Place<'tcx>>, mir::Place<'tcx>)> =
            Vec::default();
        let mut uninit_unpack_stack: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)> =
            Vec::default();

        // Weakening requirements
        let mut uninit_weakenings: FxHashSet<mir::Place> = FxHashSet::default();

        let mut uninit_problem_iter = uninit_problems.drain();
        while let Some((rloc, (mut set_rc_a, mut set_rc_b))) = uninit_problem_iter.next() {
            // Work until b is a subset of a
            while !set_rc_b.is_subset(&set_rc_a) {
                // Remove intersection (b still not subset of a afterwards)
                let mut intersection: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                for x in set_rc_a.intersection(&set_rc_b) {
                    intersection.insert(x.clone());
                }
                for x in intersection.into_iter() {
                    set_rc_a.remove(&x);
                    set_rc_b.remove(&x);
                }

                let mut gen_a: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                let mut kill_a: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                let mut gen_b: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                let mut kill_b: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                if let Some((a, b)) = set_rc_a
                    .iter()
                    .cartesian_product(set_rc_b.iter())
                    .filter(|(a, b)| is_prefix(**a, **b))
                    .next()
                {
                    // println!("(1) {:#?} is a prefix of {:#?}", b, a);
                    // expand b
                    let (expand_b, remainder_b) =
                        expand_one_level(mir, env.tcx(), (*b).into(), (*a).into());
                    gen_b = remainder_b.into_iter().collect();
                    gen_b.insert(expand_b);
                    kill_b = FxHashSet::from_iter([*b].into_iter());
                    uninit_pack_stack.push((gen_b.iter().cloned().collect(), *b));
                } else if let Some((a, b)) = set_rc_a
                    .iter()
                    .cartesian_product(set_rc_b.iter())
                    .filter(|(a, b)| is_prefix(**b, **a))
                    .next()
                {
                    // println!("(2) {:#?} is a prefix of {:#?}", a, b);
                    // expand a
                    let (expand_a, remainder_a) =
                        expand_one_level(mir, env.tcx(), (*a).into(), (*b).into());
                    gen_a = remainder_a.into_iter().collect();
                    gen_a.insert(expand_a);
                    kill_a = FxHashSet::from_iter([*a].into_iter());
                    uninit_unpack_stack.push((*a, gen_a.iter().cloned().collect()));
                } else {
                    //  There are no elements which can be packed and unpacked anymore, but
                    //   nevertheless set_rc_b is not a subset of set_rc_a.
                    // We must weaken away all remaining permissions in set_rc_b
                    uninit_weakenings = set_rc_b.clone();
                    kill_b = set_rc_b.clone();
                }

                // Apply the gen/kill operations for this iteration

                for a in kill_a.iter() {
                    set_rc_a.remove(a);
                }

                for a in gen_a.iter() {
                    set_rc_a.insert(*a);
                }

                for b in kill_b.iter() {
                    set_rc_b.remove(b);
                }

                for b in gen_b.iter() {
                    set_rc_b.insert(*b);
                }
            }
        }

        // Set up exclusive problems
        let mut ex_problems: FxHashMap<
            mir::Local,
            (FxHashSet<mir::Place<'tcx>>, FxHashSet<mir::Place<'tcx>>),
        > = FxHashMap::default();

        // Setup the problem
        for place in pcs_from.0.iter().filter_map(|perm| {
            if let Exclusive(p) = perm {
                Some(p)
            } else {
                None
            }
        }) {
            let local = place.local.clone();
            let set_borrow = ex_problems
                .entry(local)
                .or_insert((FxHashSet::default(), FxHashSet::default()));
            (*set_borrow).0.insert(place.clone());
        }

        for place in pcs_to.0.iter().filter_map(|perm| {
            if let Exclusive(p) = perm {
                Some(p)
            } else {
                None
            }
        }) {
            let local = place.local.clone();
            let set_borrow = ex_problems
                .entry(local)
                .or_insert((FxHashSet::default(), FxHashSet::default()));
            (*set_borrow).1.insert(place.clone());
        }

        // Add weakening to the exclusive problem requirements
        for place in uninit_weakenings.iter() {
            let local = place.local.clone();
            let set_borrow = ex_problems
                .entry(local)
                .or_insert((FxHashSet::default(), FxHashSet::default()));
            (*set_borrow).1.insert(place.clone());
        }

        // Solve the exclusive problem
        let mut ex_pack_stack: Vec<(FxHashSet<mir::Place<'tcx>>, mir::Place<'tcx>)> =
            Vec::default();
        let mut ex_unpack_stack: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)> =
            Vec::default();

        let mut ex_problem_iter = ex_problems.drain();
        while let Some((rloc, (mut set_rc_a, mut set_rc_b))) = ex_problem_iter.next() {
            // Work until b is a subset of a
            while !set_rc_b.is_subset(&set_rc_a) {
                // Remove intersection (b still not subset of a afterwards)
                let mut intersection: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                for x in set_rc_a.intersection(&set_rc_b) {
                    intersection.insert(x.clone());
                }
                for x in intersection.into_iter() {
                    set_rc_a.remove(&x);
                    set_rc_b.remove(&x);
                }

                let mut gen_a: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                let mut kill_a: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                let mut gen_b: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                let mut kill_b: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
                if let Some((a, b)) = set_rc_a
                    .iter()
                    .cartesian_product(set_rc_b.iter())
                    .filter(|(a, b)| is_prefix(**a, **b))
                    .next()
                {
                    // println!("(1) {:#?} is a prefix of {:#?}", b, a);
                    // expand b
                    let (expand_b, remainder_b) =
                        expand_one_level(mir, env.tcx(), (*b).into(), (*a).into());
                    gen_b = remainder_b.into_iter().collect();
                    gen_b.insert(expand_b);
                    kill_b = FxHashSet::from_iter([*b].into_iter());
                    ex_pack_stack.push((gen_b.iter().cloned().collect(), *b));
                } else if let Some((a, b)) = set_rc_a
                    .iter()
                    .cartesian_product(set_rc_b.iter())
                    .filter(|(a, b)| is_prefix(**b, **a))
                    .next()
                {
                    // println!("(2) {:#?} is a prefix of {:#?}", a, b);
                    // expand a
                    let (expand_a, remainder_a) =
                        expand_one_level(mir, env.tcx(), (*a).into(), (*b).into());
                    gen_a = remainder_a.into_iter().collect();
                    gen_a.insert(expand_a);
                    kill_a = FxHashSet::from_iter([*a].into_iter());
                    ex_unpack_stack.push((*a, gen_a.iter().cloned().collect()));
                } else {
                    // This should never happen if the semantics are sound
                    println!("Unsoundess: missing {:?}", set_rc_b);
                    panic!();
                }

                // Apply the gen/kill operations for this iteration

                for a in kill_a.iter() {
                    set_rc_a.remove(a);
                }

                for a in gen_a.iter() {
                    set_rc_a.insert(*a);
                }

                for b in kill_b.iter() {
                    set_rc_b.remove(b);
                }

                for b in gen_b.iter() {
                    set_rc_b.insert(*b);
                }
            }
        }

        // println!("REPACKING {:?} to {:?}", pcs_from, pcs_to);

        RepackWeaken {
            exclusive_unpack: ex_unpack_stack,
            exclusive_pack: ex_pack_stack.into_iter().rev().collect(),
            exclusive_weaken: uninit_weakenings,
            uninit_unpack: uninit_unpack_stack,
            uninit_pack: uninit_pack_stack.into_iter().rev().collect(),
        }
    }

    pub fn apply(
        &self,
        working_pcs: &mut PCSState<'tcx>,
        statements: &mut Vec<FreeStatement<'tcx>>,
        pcs_before: &mut Vec<PCSState<'tcx>>,
    ) {
        // 1. EXCLUSIVE UNPACKS
        for (pre, post) in self.exclusive_unpack.iter() {
            pcs_before.push(working_pcs.clone());
            let remove = Exclusive(*pre);
            let add = (*post).iter().map(|p| Exclusive(*p)).collect::<Vec<_>>();
            assert!(working_pcs.free.0.remove(&remove));
            for p in add.iter() {
                assert!(working_pcs.free.0.insert((*p).clone()));
            }
            statements.push(Unpack(remove, add));
        }

        // 2. EXCLUSIVE PACKS
        for (pre, post) in self.exclusive_pack.iter() {
            pcs_before.push(working_pcs.clone());
            let remove = (*pre).iter().map(|p| Exclusive(*p)).collect::<Vec<_>>();
            let add = Exclusive(*post);
            for p in remove.iter() {
                assert!(working_pcs.free.0.remove(p));
            }
            assert!(working_pcs.free.0.insert(add.clone()));
            statements.push(Pack(remove, add));
        }

        // 3. WEAKEN
        for to_weaken in self.exclusive_weaken.iter() {
            pcs_before.push(working_pcs.clone());
            let remove = Exclusive(*to_weaken);
            let add = Uninit(*to_weaken);
            assert!(working_pcs.free.0.remove(&remove));
            assert!(working_pcs.free.0.insert(add.clone()));
            statements.push(Weaken(remove, add));
        }

        // 4. UNINIT UNPACKS
        for (pre, post) in self.uninit_unpack.iter() {
            pcs_before.push(working_pcs.clone());
            let remove = Uninit(*pre);
            let add = (*post).iter().map(|p| Uninit(*p)).collect::<Vec<_>>();
            assert!(working_pcs.free.0.remove(&remove));
            for p in add.iter() {
                assert!(working_pcs.free.0.insert((*p).clone()));
            }
            statements.push(Unpack(remove, add));
        }

        // 5. UNINIT PACKS
        for (pre, post) in self.uninit_pack.iter() {
            pcs_before.push(working_pcs.clone());
            let remove = (*pre).iter().map(|p| Uninit(*p)).collect::<Vec<_>>();
            let add = Uninit(*post);
            for p in remove.iter() {
                assert!(working_pcs.free.0.remove(p));
            }
            assert!(working_pcs.free.0.insert(add.clone()));
            statements.push(Pack(remove, add));
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Repack Join

#[derive(Debug)]
pub struct Join<'tcx> {
    // TODO: Add the meet details to this somehow
    pub join_pcs: PCSState<'tcx>,
}

impl<'tcx> Join<'tcx> {
    pub fn join<'mir, 'env: 'mir>(
        // Context
        tcx: TyCtxt<'tcx>,
        mir: &'mir mir::Body<'tcx>,
        env: &'env Environment<'tcx>,
        mut pcs_a: PCSState<'tcx>,
        mut pcs_b: PCSState<'tcx>,
    ) -> Self
    where
        'tcx: 'env,
    {
        // TODO: We'll refactor a place to put the actual annotations sometime else
        //  when we get rid of that data clump.
        let mut st_a: Vec<FreeStatement<'tcx>> = vec![];
        let mut st_b: Vec<FreeStatement<'tcx>> = vec![];
        let mut bf_a: Vec<PCSState<'tcx>> = vec![];
        let mut bf_b: Vec<PCSState<'tcx>> = vec![];

        println!("  [debug] Performing a join");
        let mut problems = PCSProblems::new(&pcs_a, &pcs_b);

        // TODO: Collect MEET information into intermediate data structure instead of applying immedately
        // needed because we reverse the order of their computation and application etc

        while let Some((Uninit(l), inst)) = problems.next_uninit_problem() {
            println!("{:?}: {:?} / {:?}", l, inst.0, inst.1);
            let uninit_meet = Meet::new(tcx, mir, env, inst);
            uninit_meet.apply_to_infimum(
                &mut pcs_a,
                &mut st_a,
                &mut bf_a,
                &mut pcs_b,
                &mut st_b,
                &mut bf_b,
                |p| Uninit(p),
            );
        }

        println!("{:?}", problems.is_done());
        while let Some((Exclusive(l), inst)) = problems.next_exclusive_problem() {
            println!("{:?}: {:?} / {:?}", l, inst.0, inst.1);
            let exclusive_meet = Meet::new(tcx, mir, env, inst);
            exclusive_meet.apply_to_infimum(
                &mut pcs_a,
                &mut st_a,
                &mut bf_a,
                &mut pcs_b,
                &mut st_b,
                &mut bf_b,
                |p| Exclusive(p),
            );
        }
        println!("{:?}", problems.is_done());

        println!("{:?}", pcs_a);
        println!("{:?}", pcs_b);
        if pcs_a == pcs_b {
            println!("Join found: {:?}", pcs_a);
            return Join { join_pcs: pcs_a };
        }
        todo!();
    }
}

// General purpose data structure for iterating over PCS join problems
struct PCSProblems<'tcx> {
    free_problems: FxHashMap<Resource<mir::Local>, ProblemInstance<'tcx>>,
}

impl<'tcx> PCSProblems<'tcx> {
    pub fn new(pcs_a: &PCSState<'tcx>, pcs_b: &PCSState<'tcx>) -> Self {
        if !pcs_a.guarded.is_empty() || !pcs_b.guarded.is_empty() {
            println!("\t[debug] unsupported: pcs problems generation including the guarded PCS");
        }

        let mut free_problems = FxHashMap::default();
        for perm in pcs_a.free.0.iter() {
            let set_borrow = free_problems
                .entry(perm.local_permission())
                .or_insert((FxHashSet::default(), FxHashSet::default()));
            (*set_borrow).0.insert((*perm.permission_of()).into());
        }
        for perm in pcs_b.free.0.iter() {
            let set_borrow = free_problems
                .entry(perm.local_permission())
                .or_insert((FxHashSet::default(), FxHashSet::default()));
            (*set_borrow).1.insert((*perm.permission_of()).clone());
        }
        PCSProblems { free_problems }
    }

    pub fn is_done(&self) -> bool {
        self.free_problems.len() == 0
    }

    fn next_problem(
        &mut self,
        filter_fn: fn(&Resource<mir::Local>) -> bool,
    ) -> Option<(Resource<mir::Local>, ProblemInstance<'tcx>)> {
        let k = self
            .free_problems
            .keys()
            .filter(|res_l| filter_fn(res_l))
            .next()?
            .clone();
        self.free_problems.remove_entry(&k)
    }

    pub fn next_uninit_problem(&mut self) -> Option<(Resource<mir::Local>, ProblemInstance<'tcx>)> {
        self.next_problem(|rl| rl.is_uninit())
    }

    pub fn next_exclusive_problem(
        &mut self,
    ) -> Option<(Resource<mir::Local>, ProblemInstance<'tcx>)> {
        self.next_problem(|rl| rl.is_exclusive())
    }
}

// type of join problems equivalence class (module local and exclusivity)
type ProblemInstance<'tcx> = (FxHashSet<mir::Place<'tcx>>, FxHashSet<mir::Place<'tcx>>);

// Represents a basic repacking of places that computes their meet (infimum)
// to repack from a to b (and if the remainder is ({}, {})) one can
//  1. perform unpacks_a in order on a to yield infimum
//  2. perform unpacks_b in reverse order as packs to yield b
#[derive(Debug)]
struct Meet<'tcx> {
    unpacks_a: Vec<RepackLatticeEdge<'tcx>>,
    unpacks_b: Vec<RepackLatticeEdge<'tcx>>,
    meet: FxHashSet<mir::Place<'tcx>>,
    remainder: ProblemInstance<'tcx>,
}

impl<'tcx> Meet<'tcx> {
    pub fn new<'mir, 'env: 'mir>(
        tcx: TyCtxt<'tcx>,
        mir: &'mir mir::Body<'tcx>,
        env: &'env Environment<'tcx>,
        problem: ProblemInstance<'tcx>,
    ) -> Self
    where
        'tcx: 'env,
    {
        let mut prob_a = problem.0;
        let mut prob_b = problem.1;

        let mut unpacks_a: Vec<RepackLatticeEdge<'tcx>> = Vec::default();
        let mut unpacks_b: Vec<RepackLatticeEdge<'tcx>> = Vec::default();
        let mut meet: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();

        let mut gen_a: FxHashSet<mir::Place<'tcx>>;
        let mut kill_a: FxHashSet<mir::Place<'tcx>>;
        let mut gen_b: FxHashSet<mir::Place<'tcx>>;
        let mut kill_b: FxHashSet<mir::Place<'tcx>>;

        loop {
            // Reset variables
            // TODO: Can I get rid of these without angering the borrow checker?
            gen_a = FxHashSet::default();
            kill_a = FxHashSet::default();
            gen_b = FxHashSet::default();
            kill_b = FxHashSet::default();

            // 0. Move the intersection of the two sets to the infimum
            let intersection = prob_a
                .intersection(&prob_b)
                .cloned()
                .collect::<FxHashSet<_>>();
            prob_a.retain(|p| !intersection.contains(p));
            prob_b.retain(|p| !intersection.contains(p));
            meet.extend(intersection.into_iter());

            // TODO: If this is a bottleneck, this can be made more efficient with
            // vectors sorted by projection vector length (or just operation on a
            // ordered collection of projection vectors anyways)

            // 1.1 Search for place in B which is a prefix of an element in A
            if let Some((a, b)) = prob_a
                .iter()
                .cartesian_product(prob_b.iter())
                .filter(|(a, b)| is_prefix(**a, **b))
                .next()
            {
                let (expand_b, remainder_b) =
                    expand_one_level(mir, env.tcx(), (*b).into(), (*a).into());
                gen_b = remainder_b.into_iter().collect();
                gen_b.insert(expand_b);
                kill_b = FxHashSet::from_iter([*b].into_iter());
                unpacks_b.push(RepackLatticeEdge {
                    upper: *b,
                    lower: gen_b.iter().cloned().collect(),
                });
            }
            // 1.2 Search for place in A which is a prefix of an element in B
            else if let Some((a, b)) = prob_a
                .iter()
                .cartesian_product(prob_b.iter())
                .filter(|(a, b)| is_prefix(**b, **a))
                .next()
            {
                let (expand_a, remainder_a) =
                    expand_one_level(mir, env.tcx(), (*a).into(), (*a).into());
                gen_a = remainder_a.into_iter().collect();
                gen_a.insert(expand_a);
                kill_a = FxHashSet::from_iter([*a].into_iter());
                unpacks_a.push(RepackLatticeEdge {
                    upper: *a,
                    lower: gen_a.iter().cloned().collect(),
                });
            }
            // 1.3 If nothing expands, the remaining problem is the remiander
            else {
                return Meet {
                    unpacks_a,
                    unpacks_b,
                    meet,
                    remainder: (prob_a, prob_b),
                };
            }

            // Apply gen/kill operations
            for a in kill_a.iter() {
                assert!(prob_a.remove(a));
            }

            for a in gen_a.iter() {
                assert!(prob_a.insert(*a));
            }

            for b in kill_b.iter() {
                assert!(prob_b.remove(b));
            }

            for b in gen_b.iter() {
                assert!(prob_b.insert(*b));
            }
        }
    }

    // TODO: The triple (working_pcs, statements, pcs_before) is a data clump
    // TODO: this function should be a member of that data clump's struct, not the meet
    pub fn apply_to_infimum(
        &self,
        working_pcs_a: &mut PCSState<'tcx>,
        statements_a: &mut Vec<FreeStatement<'tcx>>,
        pcs_before_a: &mut Vec<PCSState<'tcx>>,
        working_pcs_b: &mut PCSState<'tcx>,
        statements_b: &mut Vec<FreeStatement<'tcx>>,
        pcs_before_b: &mut Vec<PCSState<'tcx>>,
        kind_f: fn(mir::Place<'tcx>) -> Resource<mir::Place<'tcx>>,
    ) {
        Self::do_apply_downwards(
            working_pcs_a,
            statements_a,
            pcs_before_a,
            &self.unpacks_a,
            kind_f,
        );
        Self::do_apply_downwards(
            working_pcs_b,
            statements_b,
            pcs_before_b,
            &self.unpacks_b,
            kind_f,
        );
    }

    // TODO: This also doesn't belong here!
    fn do_apply_downwards(
        working: &mut PCSState<'tcx>,
        statements: &mut Vec<FreeStatement<'tcx>>,
        before: &mut Vec<PCSState<'tcx>>,
        edges: &Vec<RepackLatticeEdge<'tcx>>,
        kind_f: fn(mir::Place<'tcx>) -> Resource<mir::Place<'tcx>>,
    ) {
        for edge in edges.iter() {
            before.push(working.clone());
            edge.apply_downwards(&mut working.free.0, kind_f);
            statements.push(edge.as_unpack(kind_f))
        }
    }
}

#[derive(Debug)]
struct RepackLatticeEdge<'tcx> {
    upper: mir::Place<'tcx>,
    lower: FxHashSet<mir::Place<'tcx>>,
}

impl<'tcx> RepackLatticeEdge<'tcx> {
    pub fn apply_downwards(
        &self,
        set: &mut FxHashSet<Resource<mir::Place<'tcx>>>,
        kind_f: fn(mir::Place<'tcx>) -> Resource<mir::Place<'tcx>>,
    ) {
        assert!(set.remove(&kind_f(self.upper)));
        for to in self.lower.iter() {
            assert!(set.insert(kind_f(*to).clone()));
        }
    }
    pub fn apply_upwards(
        &self,
        set: &mut FxHashSet<Resource<mir::Place<'tcx>>>,
        kind_f: fn(mir::Place<'tcx>) -> Resource<mir::Place<'tcx>>,
    ) {
        for from in self.lower.iter() {
            assert!(set.remove(&kind_f(*from)));
        }
        assert!(set.insert(kind_f(self.upper).clone()));
    }

    pub fn as_unpack(
        &self,
        kind_f: fn(mir::Place<'tcx>) -> Resource<mir::Place<'tcx>>,
    ) -> FreeStatement<'tcx> {
        Unpack(
            kind_f(self.upper.clone()),
            self.lower.iter().map(|p| kind_f(*p)).collect::<Vec<_>>(),
        )
    }
}
