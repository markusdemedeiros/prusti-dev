// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(unused_variables)]
#![allow(unused_imports)]
use super::pcs::Resource::*;
use crate::{
    cfgiter::{DirtyBlock, PCSIter},
    model::{Resource::*, *},
    pcs::FreeStatement::*,
    repack::*,
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

/// Computes the PCS and prints it to the console
/// Currently the entry point for the compiler
pub fn dump_pcs<'env, 'tcx: 'env>(env: &'env Environment<'tcx>) -> EncodingResult<()> {
    for proc_id in env.get_annotated_procedures().iter() {
        println!("id: {:#?}", env.get_unique_item_name(*proc_id));
        let current_procedure: Procedure<'tcx> = env.get_procedure(*proc_id);
        let local_def_id = proc_id.expect_local();
        //let borrowck_facts = *(env.local_mir_borrowck_facts(local_def_id).as_ref());
        //let facts = env.local_mir_borrowck_facts(local_def_id);
        //let borrowck_facts = facts.take().unwrap();
        //     .to_owned()
        //     .as_ref();

        let polonius_info =
            PoloniusInfo::new_without_loop_invariant_block(env, &current_procedure).unwrap();

        // let output_facts = prusti_rustc_interface::polonius_engine::Output::compute(
        //     &borrowck_facts.input_facts,
        //     prusti_rustc_interface::polonius_engine::Algorithm::Naive,
        //     true,
        // );
        // assert!(output_facts.errors.is_empty());

        let mut mir: mir::Body<'tcx> = current_procedure.get_mir().clone();

        // Preprocess the MIR
        preprocess_mir(&mut mir);

        let mut ctx = PCSctx {
            mir: &mir,
            env,
            init_analysis: compute_definitely_initialized((*proc_id).clone(), &mir, env.tcx()),
            alloc_analysis: compute_definitely_allocated((*proc_id).clone(), &mir),
            polonius_info,
        };

        ctx.compute_pcs();
    }
    Ok(())
}

////////////////////////////////////////////////////////////////////////////////
// PCS
// 1. Apply Polonius borrow information
// 2. Apply semantics

struct PCSctx<'mir, 'env: 'mir, 'tcx: 'env> {
    pub mir: &'mir mir::Body<'tcx>,
    pub env: &'env Environment<'tcx>,
    pub init_analysis: DefinitelyInitializedAnalysisResult<'tcx>,
    pub alloc_analysis: DefinitelyAllocatedAnalysisResult,
    pub polonius_info: PoloniusInfo<'env, 'tcx>,
}

/// Data structure for all computations of the CondPCS
impl<'mir, 'env: 'mir, 'tcx: 'env> PCSctx<'mir, 'env, 'tcx> {
    fn compute_pcs(&mut self) {
        // -> PCS<'mir, 'tcx>
        // Iteration: Prioritize blocks with in-blocks filled

        // Invariant: All fully computed blocks are returned before any partially
        // computed ones (loop heads)

        // Algorithm:
        // 0. If the in-degree is full
        //      0.1. (globally) flow exclusion at all in-edges
        //      0.2. Conditionally join the PCS's
        //    Otherwise,
        //      0.3. At a loop head.
        //      0.4. -- todo: old markings
        let mut pcs_iter = PCSIter::new(self.mir, self.initial_state());
        let mut end_states: FxHashMap<mir::BasicBlock, PCSState<'tcx>> = FxHashMap::default();

        while let Some((working_block, flow_exclusions)) = pcs_iter.next() {
            // Do the join here
            let mut working_pcs: PCSState<'tcx>;

            if flow_exclusions.len() == 1 {
                // No approximations needed (afaik)
                // Just select a done block (it must be done)
                // working_pcs = todo!(); // flow_exclusions[0].0;

                assert!(flow_exclusions[0].1);
                working_pcs = end_states.get(&flow_exclusions[0].0).unwrap().clone();
            } else if flow_exclusions.len() == 0 {
                // Initial state
                working_pcs = PCSState::default();
            } else if flow_exclusions.len() == 2 {
                println!("=== ATTEMPTING TO JOIN");
                let st_a = end_states.get(&flow_exclusions[0].0).unwrap().clone();
                let st_b = end_states.get(&flow_exclusions[1].0).unwrap().clone();
                println!("{:?} {:?}", flow_exclusions[0], st_a,);
                println!("{:?} {:?}", flow_exclusions[1], st_b,);
                let join = Join::join(
                    self.env.tcx(),
                    self.mir,
                    self.env,
                    st_a.clone(),
                    st_b.clone(),
                );
                // TODO: Log states from the join to post blocks here
                //  (possible Join.apply() or something)
                working_pcs = join.join_pcs;
            } else {
                todo!();
            }

            self.translate_body(&working_block, &mut working_pcs);

            if let Some(term) = &self
                .mir
                .basic_blocks()
                .get(*working_block.block())
                .unwrap()
                .terminator
            {
                println!("{:?}", &term.kind);
                match &term.kind {
                    TerminatorKind::Goto { target }
                    | TerminatorKind::FalseUnwind {
                        real_target: target,
                        unwind: _,
                    }
                    | TerminatorKind::Assert {
                        cond: _,
                        expected: _,
                        msg: _,
                        target,
                        cleanup: _,
                    } => pcs_iter.push(DirtyBlock::new(PCSState::default(), *target)),
                    TerminatorKind::Return => {}
                    TerminatorKind::SwitchInt {
                        discr,
                        switch_ty,
                        targets,
                    } => {
                        for next_bb in targets.all_targets().iter() {
                            pcs_iter.push(DirtyBlock::new(PCSState::default(), *next_bb));
                        }
                    }
                    _ => {
                        todo!();
                    }
                }
            }
            end_states.insert(*(working_block.block()), working_pcs);
            pcs_iter.finish(*(working_block.block()));
        }
    }

    fn initial_state(&self) -> DirtyBlock<'tcx> {
        // TODO: This is not correct, it misses paramaters
        DirtyBlock::new(PCSState::default(), mir::BasicBlock::from_u32(0 as u32))
    }

    // Returns a new CFGBlock with completely translated body
    fn translate_body(&self, dirty: &DirtyBlock, working_pcs: &mut PCSState<'tcx>) {
        // For each statement:
        println!("Translating block number {:?}", dirty.block());
        println!(
            "Reference Moves: {:?}",
            self.polonius_info.get_reference_moves()
        );
        // Block-level weakening
        // (iteration starts on the prior _edges_ through flow exclusion)

        //////////

        for (statement_index, stmt) in self
            .mir
            .basic_blocks()
            .get(*dirty.block())
            .unwrap()
            .statements
            .iter()
            .enumerate()
        {
            let location = mir::Location {
                block: *dirty.block(),
                statement_index,
            };

            let (cull_pre, cull_post) = working_pcs.guarded.cull_loans(
                self.polonius_info
                    .get_loan_live_at(location, PointType::Start),
            );

            // println!("cull_pre:  {:?}", cull_pre);
            // println!("cull_post: {:?}", cull_post);

            let mut cull_statements: Vec<FreeStatement<'tcx>> = vec![];
            let mut cull_before_pcs: Vec<PCSState<'tcx>> = vec![];
            let packing = RepackWeaken::repack_weaken(
                self.env.tcx(),
                self.mir,
                self.env,
                working_pcs.free.clone(),
                PermissionSet(cull_pre.clone()),
            );
            packing.apply(working_pcs, &mut cull_statements, &mut cull_before_pcs);
            if cull_statements.len() > 0 {
                for e in cull_statements.iter() {
                    println!("       (cull) {:?}", e);
                }
            }

            for p in cull_pre.iter() {
                if !working_pcs.free.0.remove(p) {
                    panic!();
                }
            }

            for p in cull_post.into_iter() {
                if !working_pcs.free.0.insert(p) {
                    panic!();
                }
            }

            // println!(
            //     "{:?}",
            //     self.polonius_info
            //         .get_loan_live_at(location, PointType::Start)
            // );
            // println!(
            //     "{:?}",
            //     self.polonius_info
            //         .get_loan_live_at(location, PointType::Mid)
            // );

            // let active_loans = self.polonius_info.get_active_loans(location, false);
            // print!("\t{:?} ========== [", location);
            // for l in active_loans {
            //     if let Ok(Some(assign)) = self.polonius_info.get_assignment_for_loan(l) {
            //         if let Assign(box (b, _)) = assign.kind {
            //             print!("{:?} ({:?}), ", l, b);
            //         } else {
            //             panic!();
            //         }
            //     } else {
            //         panic!();
            //     }
            // }
            // println!("]");

            // 2. Apply Polonius facts for dying loans at this point
            // 2.1. Remove all guards from GPCS
            // 2.2. While we can regain permissions, do so
            // 2.3. Packup (to get to unique state)
            // 2.4: Weaken
            // 2.5. Repack for Hoare condition

            let packing = RepackWeaken::repack_weaken(
                self.env.tcx(),
                self.mir,
                self.env,
                working_pcs.free.clone(),
                PermissionSet::from_vec(self.precondition_statement(&stmt.kind)).clone(),
            );
            let mut edge_statements: Vec<FreeStatement<'tcx>> = vec![];
            let mut edge_before_pcs: Vec<PCSState<'tcx>> = vec![];
            packing.apply(working_pcs, &mut edge_statements, &mut edge_before_pcs);
            if edge_statements.len() > 0 {
                for e in edge_statements.iter() {
                    println!("\t\t(edge) {:?}", e);
                }
            }

            println!("\t{:?}\tPCS: {:?}", location, working_pcs);
            println!("\t{:?}\t{:?}", location, stmt);

            let st_loan_live_at = self
                .polonius_info
                .get_loan_live_at(location, PointType::Mid);
            let st_loan_dying_at = self.polonius_info.get_loans_dying_at(location, false);

            // If there's an extra live loan, then issue a new one
            let new_guards: Vec<Guard<'tcx>> = vec![];
            let move_guards: Vec<(mir::Place<'tcx>, mir::Place<'tcx>)> = vec![];

            // for (p_from, p_to) in move_guards {
            //     println!("\t working on move loan {:?}, {:?}", p_from, p_to);
            //     working_pcs
            //         .guarded
            //         .move_loan(&p_from, &p_to, *dirty.block());
            // }

            // Update loan expiry

            // 4. Apply hoare semantics
            for p in self.precondition_statement(&stmt.kind).iter() {
                if !working_pcs.free.0.remove(p) {
                    panic!();
                }
            }

            for p in self.postcondition_statement(&stmt.kind).into_iter() {
                if !working_pcs.free.0.insert(p) {
                    panic!();
                }
            }

            // Can a loan be created and die at the same location?
            // If so, we might need to cull loans twice (preconditions can depend on loan deaths'
            //  permissions for example loan deaths due to RHS invalidations)

            // Apply guard effects to the PCS
            // 1. New loan issues

            let loan_issues = self
                .polonius_info
                .get_loan_issued_at(location, PointType::Mid);

            // println!("issues {:?}", loan_issues);
            // println!(
            //     "live st {:?}",
            //     self.polonius_info
            //         .get_loan_live_at(location, PointType::Start)
            // );
            // println!(
            //     "live md {:?}",
            //     self.polonius_info
            //         .get_loan_live_at(location, PointType::Start)
            // );

            let mut loan_issues_it = loan_issues.iter();
            if let Some(new) = loan_issues_it.next() {
                // For now, the creation of a loan can be decided completely syntactically
                match stmt.kind {
                    Assign(box (b, Ref(_, _, p))) => {
                        // new_guards.push(Guard {
                        //     label: *new,
                        //     lhs: vec![(*dirty.block(), PlaceHole::Linear(b))],
                        //     rhs: Exclusive(p),
                        // });
                        working_pcs.guarded.insert_guard(Guard {
                            label: *new,
                            lhs: vec![Tagged {
                                item: PlaceHole::Linear(b),
                                tag: None,
                            }],
                            rhs: Some(Tagged {
                                item: Exclusive(p),
                                tag: None,
                            }), // Some(Exclusive(p)),
                        });
                    }
                    // Note: Moving mut borrows are never copy
                    Assign(box (p_to, Use(mir::Operand::Move(p_from)))) => {
                        // When a borrow is moved, a new loan is made.
                        // After, we should have permission to write to the previously borrowed-from place
                        //      even if we didn't before (conditionally blah)
                        // The old loan can not be applied any longer

                        if self.polonius_info.get_reference_moves().contains(new) {
                            // The prior guards of the place are no longer guarding it
                            // The precondition of the move is definitely in the PCS at this point (?)

                            // Reset guards (without filling them)
                            // We have gotten permissions for the loan precondition

                            working_pcs
                                .guarded
                                .move_loan(&p_from, &p_to, *(*dirty).block());

                            // Set the fake loan as one with no pre- or post- condition
                            working_pcs.issue_guard_for_loan(Guard::nop_guard((*new).clone()));
                        } else {
                            // Just a regular, owned, move. Nothing to see here
                            todo!();
                        }
                        // move_guards.push((p_from, p_to));
                    }
                    _ => {
                        panic!();
                    }
                };
            }
            // Assertion: Only one new loan issued per statement (should be true, always)
            assert!(loan_issues_it.next() == None);

            // Now work through the dying loans
            //  Note: LHS of loans are always FULL PLACES (not x.f) since we don't support
            //      borrows in structs yet.

            // TODO: Tagging before or after culling?
            working_pcs.guarded.kill_loan(
                self.polonius_info
                    .get_loan_killed_at(location, PointType::Mid),
                location,
            );

            /*
            for dying in st_loan_dying_at {
                // (0) (unsoundness for now) find an order to apply loans in and do this procedure greedily
                // 1. Get all the LHS's the Guarded PCS infers we can no longer use
                let requirements = working_pcs.guarded.get_expiry_requirements(dying);

                // 1.1. Repack them fully (this is on an mid-edge now?)
                let mut edge_statements: Vec<FreeStatement<'tcx>> = vec![];
                let mut edge_before_pcs: Vec<PCSState<'tcx>> = vec![];
                packing.apply(working_pcs, &mut edge_statements, &mut edge_before_pcs);
                if edge_statements.len() > 0 {
                    for e in edge_statements.iter() {
                        println!("       (edge) {:?}", e);
                    }
                }

                // 1.2. Remove them from the free PCS
                // 1.2.5 Re-insert Uninit resouce once a loan is applied (we can still write to it after it dies)
                for req in requirements {
                    assert!(working_pcs.free.0.remove(&req));
                    assert!(working_pcs.free.0.insert(Uninit(*req.permission_of())));
                    // 1.3. Update constraints across entire guarded PCS
                    let hole = match req {
                        Exclusive(p) => PlaceHole::Linear(p),
                        _ => todo!(),
                    };
                    working_pcs.guarded.eliminate_hole(hole);
                }

                // 2. Assert that the loan's guard is completely fulfilled
                let regain_permissions = working_pcs.guarded.eliminate_loan(dying);

                // 3. Reclaim the loan's RHS into free PCS
                for perm in regain_permissions.into_iter() {
                    assert!(working_pcs.free.0.insert(perm));
                }
            }
            */

            // Apply new loan issues

            // for new in st_loan_live_at
            //     .iter()
            //     .filter(|live| !working_pcs.guarded.get_loans().contains(live))
            // {
            //     println!("computing {:?}", new);
            // }
            // for g in new_guards {
            //     println!("\t working on new loan {:?}", g);
            //     working_pcs.guarded.insert_guard(g);
            // }

            // 4. For each MicroMir statement:
            //      4.1. Repack Free PCS to Hoare precondition
            //              (may be something like "most packed" for drops etc)
            //      4.2. Apply the Hoare Semantics and wand effects
            //      4.3. Check lifeness facts
            //      4.3. Check Polonius facts (origin live at, etc.)
            //      4.4. Push the MicroMir statement (plus any computed elaborations)
            // 5. Repack free PCS to terminator precondition
            // 6. Apply terminator semantics to current PCS
            // 7. Push terminator
            // 8. Push dirty blocks with current state
            // 9. Check intialization requiremtnes
            // 10. Check midpoint status from Polonius
        }

        // Terminator Owned semantics
        let terminator = self
            .mir
            .basic_blocks()
            .get(*dirty.block())
            .unwrap()
            .terminator();

        for p in self.term_precondition(&terminator.kind).iter() {
            if !working_pcs.free.0.remove(p) {
                panic!();
            }
        }

        for p in self.term_postcondition(&terminator.kind).into_iter() {
            if !working_pcs.free.0.insert(p) {
                panic!();
            }
        }
    }

    fn flow_join(&self, flows: Vec<(mir::BasicBlock, bool)>) {}

    fn precondition_statement(
        &self,
        statement: &mir::StatementKind<'tcx>,
    ) -> Vec<Permission<'tcx>> {
        match statement {
            StorageDead(p) => vec![Uninit((*p).into())],
            Nop | StorageLive(_) => vec![],
            Assign(box (p_to, Use(op))) => {
                let mut a1 = vec![Uninit((*p_to).into())];
                a1.append(&mut self.op_precondition(op));
                a1
            }
            Assign(box (dest, Aggregate(box Adt(_, _, _, _, _), operands))) => {
                let mut a1 = vec![];
                for op in operands {
                    a1.append(&mut self.op_precondition(&op));
                }
                a1.push(Uninit((*dest).into()));
                a1
            }
            Assign(box (dest, Ref(_, _, p_from))) => {
                vec![Uninit((*dest).into()), Exclusive((*p_from).into())]
            }
            _ => panic!(),
        }
    }

    fn postcondition_statement(
        &self,
        statement: &mir::StatementKind<'tcx>,
    ) -> Vec<Permission<'tcx>> {
        match statement {
            Nop | StorageDead(_) => vec![],
            StorageLive(p) => vec![Uninit((*p).into())],
            Assign(box (p_to, Use(op))) => {
                let mut a1 = vec![Exclusive((*p_to).into())];
                a1.append(&mut self.op_use(op));
                a1
            }
            Assign(box (dest, Aggregate(box Adt(_, _, _, _, _), operands))) => {
                let mut a1 = vec![];
                for op in operands {
                    a1.append(&mut self.op_use(&op));
                }
                a1.push(Exclusive((*dest).into()));
                a1
            }
            Assign(box (dest, Ref(_, _, p_from))) => {
                vec![Exclusive((*dest).into())]
            }
            _ => panic!(),
        }
    }

    fn op_precondition(&self, op: &mir::Operand<'tcx>) -> Vec<Permission<'tcx>> {
        match op {
            Copy(p) | Move(p) => vec![Exclusive((*p).into())],
            Constant(_) => vec![],
        }
    }

    fn op_use(&self, op: &mir::Operand<'tcx>) -> Vec<Permission<'tcx>> {
        match op {
            Constant(_) => vec![],
            Copy(p) => vec![Exclusive((*p).into())],
            Move(p) => vec![Uninit((*p).into())],
        }
    }

    fn term_precondition(&self, term: &TerminatorKind<'tcx>) -> Vec<Permission<'tcx>> {
        match term {
            TerminatorKind::SwitchInt {
                discr,
                switch_ty: _,
                targets: _,
            } => self.op_precondition(&discr),
            _ => vec![],
        }
    }

    fn term_postcondition(&self, term: &TerminatorKind<'tcx>) -> Vec<Permission<'tcx>> {
        match term {
            TerminatorKind::SwitchInt {
                discr,
                switch_ty: _,
                targets: _,
            } => self.op_use(&discr),
            _ => vec![],
        }
    }
}
