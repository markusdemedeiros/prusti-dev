// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_variables)]
use super::pcs::Resource::*;
use crate::{pcs::FreeStatement::*, syntax::PCSPermission, util::EncodingResult};
use core::cell::*;
use itertools::{
    Either::{Left, Right},
    Itertools,
};
use prusti_interface::{
    environment::{
        borrowck::facts::{BorrowckFacts, Loan},
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

fn preprocess_mir<'tcx>(mir: &mut mir::Body<'tcx>) {
    // Simple filter on MIR statements
    // Ensure all statements are in model 1.
    for (bb, bbdata) in mir.basic_blocks_mut().iter_enumerated_mut() {
        for (st_no, st) in bbdata.statements.iter_mut().enumerate() {
            let l = mir::Location {
                block: bb,
                statement_index: st_no,
            };

            match st.kind {
                StorageLive(_)
                | StorageDead(_)
                | Assign(box (_, Use(_)))
                | Nop
                | Assign(box (_, Aggregate(box Adt(_, _, _, _, _), _)))
                | Assign(box (
                    _,
                    Ref(
                        _,
                        mir::BorrowKind::Mut {
                            allow_two_phase_borrow: _,
                        },
                        _,
                    ),
                )) => (),
                FakeRead(_) | AscribeUserType(_, _) => {
                    st.make_nop();
                }
                _ => {
                    println!("{:?}", st.kind);
                    panic!()
                }
            }
        }

        let term = bbdata.terminator_mut();
        match term.kind {
            Goto { target: _ }
            | SwitchInt {
                discr: _,
                switch_ty: _,
                targets: _,
            }
            | Return => (),
            FalseUnwind {
                real_target: target,
                unwind: _,
            }
            | Assert {
                cond: _,
                expected: _,
                msg: _,
                target,
                cleanup: _,
            } => {
                term.kind = Goto { target };
            }
            _ => {
                println!("{:?}", term.kind);
                panic!()
            }
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Permissions (Free PCS)

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub enum Resource<T>
where
    T: Clone,
{
    Exclusive(T),
    Shared(T),
    Uninit(T),
    Blocked(T),
}

type Permission<'tcx> = Resource<mir::Place<'tcx>>;

#[derive(Clone, Debug)]
pub struct PermissionSet<'tcx>(FxHashSet<Permission<'tcx>>);

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

fn usize_place<'tcx>(id: usize) -> mir::Place<'tcx> {
    mir::Local::from_usize(id).into()
}

////////////////////////////////////////////////////////////////////////////////
// Guarded PCS

#[derive(Clone, Debug)]
enum PlaceHole<'tcx> {
    Linear(mir::Place<'tcx>),
    NonLinear(mir::Place<'tcx>),
    None,
}

type JoinPoint = usize;

type JoinPath = usize;

// Essentially: Tree of join points
enum GuardExpr {
    Top,
    ThroughJoin(JoinPoint, JoinPath),
    And(Box<GuardExpr>),
}

#[derive(Clone, Debug)]
struct Guard<'tcx> {
    loan: usize,
    rhs: Permission<'tcx>,
    // Generalization: guards can be stronger expressions than a single bb
    // Generalization: for struct with borrow RHS can be not top-level place
    lhs: Vec<(mir::BasicBlock, PlaceHole<'tcx>)>,
}

#[derive(Clone, Debug)]
struct GuardSet<'tcx>(Vec<Guard<'tcx>>);

impl<'tcx> Default for GuardSet<'tcx> {
    fn default() -> Self {
        GuardSet { 0: Vec::default() }
    }
}

////////////////////////////////////////////////////////////////////////////////
// State

#[derive(Clone, Debug)]
struct PCSState<'tcx> {
    free: PermissionSet<'tcx>,
    guarded: GuardSet<'tcx>,
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

struct PCS<'mir, 'tcx: 'mir> {
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

struct EdgeBlock<'tcx> {
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

            let active_loans = self.polonius_info.get_active_loans(location, false);
            // print!("\tLoans: ");
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
            // println!();
            // println!("\t\t pcs {:?}", working_pcs);

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
                    println!("       (edge) {:?}", e);
                }
            }

            println!("\t{:?} {:?}", location, stmt);
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

            // 5. Add in new loans
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

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// CFG Iterator

struct PCSIter<'mir, 'tcx: 'mir> {
    mir: &'mir mir::Body<'tcx>,
    pub dirty_blocks: Vec<DirtyBlock<'tcx>>,
    pub next_blocks: Vec<DirtyBlock<'tcx>>,
    pub done_blocks: Vec<mir::BasicBlock>,
}

impl<'mir, 'tcx: 'mir> PCSIter<'mir, 'tcx> {
    fn new(mir: &'mir mir::Body<'tcx>, initial: DirtyBlock<'tcx>) -> Self {
        PCSIter {
            mir,
            dirty_blocks: vec![],
            next_blocks: vec![initial],
            done_blocks: vec![],
        }
    }

    fn is_done(&self) -> bool {
        self.next_blocks.is_empty() && self.dirty_blocks.is_empty()
    }

    // Greedily pick blocks with complete in-degree
    fn next(&mut self) -> Option<(DirtyBlock<'tcx>, FlowExclusion)> {
        // If there's a block with full in-degree,
        if let Some(ret) = self.next_blocks.pop() {
            return Some((ret.clone(), self.compute_flow_exclusion(ret)));
        }

        // TODO: This is inefficient
        // Update the dirty_blocks to see if any of them are full in-degree (inefficient,
        //  but only loop heads should be in here)
        let mut dirty_blocks1 = vec![];
        while let Some(d) = self.dirty_blocks.pop() {
            if self.mir.predecessors()[*d.block()]
                .iter()
                .all(|suc| self.done_blocks.contains(suc))
            {
                self.next_blocks.push(d);
            } else {
                dirty_blocks1.push(d);
            }
        }
        self.dirty_blocks = dirty_blocks1;

        // Pick from next_blocks, then dirty_blocks, then fail.
        // TODO: refactor to or_else
        if let Some(ret) = self.next_blocks.pop() {
            return Some((ret.clone(), self.compute_flow_exclusion(ret)));
        } else if let Some(ret) = self.dirty_blocks.pop() {
            return Some((ret.clone(), self.compute_flow_exclusion(ret)));
        } else {
            return None;
        }
    }

    fn compute_flow_exclusion(&self, d: DirtyBlock<'tcx>) -> FlowExclusion {
        self.mir.predecessors()[*d.block()]
            .iter()
            .map(|pred| (pred.clone(), self.done_blocks.contains(pred)))
            .collect()
    }

    fn push(&mut self, dirty: DirtyBlock<'tcx>) {
        if !self.done_blocks.contains(dirty.block())
            && !self.next_blocks.iter().any(|d| d.block() == dirty.block())
            && !self.dirty_blocks.iter().any(|d| d.block() == dirty.block())
        {
            self.dirty_blocks.push(dirty);
        }
    }

    fn finish(&mut self, done: mir::BasicBlock) {
        //  TODO: Runtime check that the key isn't already in there?
        self.done_blocks.push(done);
    }
}

#[derive(Clone)]
struct DirtyBlock<'tcx>(PCSState<'tcx>, mir::BasicBlock);

impl<'tcx> DirtyBlock<'tcx> {
    pub fn new(state: PCSState<'tcx>, block: mir::BasicBlock) -> Self {
        DirtyBlock { 0: state, 1: block }
    }

    pub fn block(&self) -> &mir::BasicBlock {
        &self.1
    }
}

type FlowExclusion = Vec<(mir::BasicBlock, bool)>;
// interp true iff basic block is previously computed.

// PCS UNIFICATIONS WITH SOUND WEAKENING

// interp. Perfrom these in sequence.
#[derive(Debug)]
struct RepackWeaken<'tcx> {
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
        mut pcs_from: PermissionSet<'tcx>,
        mut pcs_to: PermissionSet<'tcx>,
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
                    //  There are no elements which can be packed and unpacked anymore, but
                    //   nevertheless set_rc_b is not a subset of set_rc_a.
                    // We must weaken away all remaining permissions in set_rc_b
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
// Old Repacker

// Assumption: All places are mutably owned
// #[derive(Debug)]
// pub struct RepackUnify<'tcx> {
//     pub packs: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)>,
//     pub unpacks: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)>,
// }
//
// impl<'tcx> RepackUnify<'tcx> {
//     // TODO: Look over this again, many places need improvement
//     pub fn unify_moves<'mir, 'env: 'mir>(
//         a_pcs: &PermissionSet<'tcx>,
//         b_pcs: &PermissionSet<'tcx>,
//         mir: &'mir mir::Body<'tcx>,
//         env: &'env Environment<'tcx>,
//     ) -> RepackUnify<'tcx>
//     where
//         'tcx: 'env,
//     {
//         let mut mir_problems: FxHashMap<
//             Resource<mir::Local>,
//             (FxHashSet<mir::Place<'tcx>>, FxHashSet<mir::Place<'tcx>>),
//         > = FxHashMap::default();
//
//         // // Split the problem into independent parts
//         for pcs_permission in a_pcs.0.iter() {
//             //let permissionkind = pcs_permission.kind.clone();
//             match pcs_permission {
//                 perm @ Exclusive(place) => {
//                     let local = place.local.clone();
//                     let set_borrow = mir_problems
//                         .entry(Exclusive(local))
//                         .or_insert((FxHashSet::default(), FxHashSet::default()));
//                     (*set_borrow).0.insert(place.clone());
//                 }
//                 perm @ Uninit(place) => {
//                     let local = place.local.clone();
//                     let set_borrow = mir_problems
//                         .entry(Uninit(local))
//                         .or_insert((FxHashSet::default(), FxHashSet::default()));
//                     (*set_borrow).0.insert(place.clone());
//                 }
//                 _ => todo!(),
//             }
//         }
//
//         for pcs_permission in b_pcs.0.iter() {
//             //let permissionkind = pcs_permission.kind.clone();
//             match pcs_permission {
//                 perm @ Exclusive(place) => {
//                     let local = place.local.clone();
//                     let set_borrow = mir_problems
//                         .entry(Exclusive(local))
//                         .or_insert((FxHashSet::default(), FxHashSet::default()));
//                     (*set_borrow).1.insert(place.clone());
//                 }
//                 perm @ Uninit(place) => {
//                     let local = place.local.clone();
//                     let set_borrow = mir_problems
//                         .entry(Uninit(local))
//                         .or_insert((FxHashSet::default(), FxHashSet::default()));
//                     (*set_borrow).1.insert(place.clone());
//                 }
//                 _ => todo!(),
//             }
//         }
//
//         let mut a_unpacks: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)> = Vec::default();
//         let mut b_unpacks: Vec<(mir::Place<'tcx>, FxHashSet<mir::Place<'tcx>>)> = Vec::default();
//
//         // Iterate over subproblems (in any order)
//         let mut mir_problem_iter = mir_problems.drain();
//         while let Some((rloc, (mut set_rc_a, mut set_rc_b))) = mir_problem_iter.next() {
//             // No work to be done when PCS a is a subset of PCS b
//             while !set_rc_b.is_subset(&set_rc_a) {
//                 // Remove intersection (b still not subset of a afterwards)
//                 let mut intersection: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
//                 for x in set_rc_a.intersection(&set_rc_b) {
//                     intersection.insert(x.clone());
//                 }
//                 for x in intersection.into_iter() {
//                     set_rc_a.remove(&x);
//                     set_rc_b.remove(&x);
//                 }
//
//                 let mut gen_a: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
//                 let mut kill_a: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
//                 let mut gen_b: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
//                 let mut kill_b: FxHashSet<mir::Place<'tcx>> = FxHashSet::default();
//                 if let Some((a, b)) = set_rc_a
//                     .iter()
//                     .cartesian_product(set_rc_b.iter())
//                     .filter(|(a, b)| is_prefix(**a, **b))
//                     .next()
//                 {
//                     // println!("(1) {:#?} is a prefix of {:#?}", b, a);
//                     // expand b
//                     let (expand_b, remainder_b) =
//                         expand_one_level(mir, env.tcx(), (*b).into(), (*a).into());
//                     gen_b = remainder_b.into_iter().collect();
//                     gen_b.insert(expand_b);
//                     kill_b = FxHashSet::from_iter([*b].into_iter());
//                     b_unpacks.push((*b, gen_b.clone()));
//                 } else if let Some((a, b)) = set_rc_a
//                     .iter()
//                     .cartesian_product(set_rc_b.iter())
//                     .filter(|(a, b)| is_prefix(**b, **a))
//                     .next()
//                 {
//                     // println!("(2) {:#?} is a prefix of {:#?}", a, b);
//                     // expand a
//                     let (expand_a, remainder_a) =
//                         expand_one_level(mir, env.tcx(), (*a).into(), (*b).into());
//                     gen_a = remainder_a.into_iter().collect();
//                     gen_a.insert(expand_a);
//                     kill_a = FxHashSet::from_iter([*a].into_iter());
//                     a_unpacks.push((*a, gen_a.clone()));
//                 } else {
//                     // We missed a weakening problem!
//                     println!("{:?}", rloc);
//                     println!("{:?}", set_rc_a);
//                     println!("{:?}", set_rc_b);
//                     panic!();
//                 }
//
//                 for a in kill_a.iter() {
//                     set_rc_a.remove(a);
//                 }
//
//                 for a in gen_a.iter() {
//                     set_rc_a.insert(*a);
//                 }
//
//                 for b in kill_b.iter() {
//                     set_rc_b.remove(b);
//                 }
//
//                 for b in gen_b.iter() {
//                     set_rc_b.insert(*b);
//                 }
//             }
//         }
//
//         RepackUnify {
//             unpacks: a_unpacks,
//             packs: b_unpacks,
//         }
//     }
//
//     /// Apply a PCSRepacker to a state
//     pub fn apply_packings(
//         &self,
//         mut state: &mut PermissionSet<'tcx>,
//         statements: &mut Vec<FreeStatement<'tcx>>,
//         before_pcs: &mut Vec<PermissionSet<'tcx>>,
//     ) {
//         // TODO: Move insert and remove (guarded with linearity) into PCS
//
//         for (p, unpacked_p) in self.unpacks.iter() {
//             before_pcs.push(state.clone());
//
//             let to_lose = p.clone();
//             // TODO: We're assuming all places are mutably owned right now
//             if !state.0.remove(&Exclusive(to_lose.into())) {
//                 panic!();
//             }
//             let to_regain: Vec<mir::Place<'tcx>> = unpacked_p.iter().cloned().collect();
//             for p1 in to_regain.iter() {
//                 if !state.0.insert(Exclusive((*p1).into())) {
//                     panic!();
//                 }
//             }
//             statements.push(FreeStatement::Unpack(to_lose, to_regain));
//         }
//
//         for (p, pre_p) in self.packs.iter().rev() {
//             before_pcs.push(state.clone());
//
//             let to_lose: Vec<mir::Place<'tcx>> = pre_p.iter().cloned().collect(); // expand_place(*p, mir, env)?;
//             for p1 in to_lose.iter() {
//                 if !state.0.remove(&Exclusive((*p1).into())) {
//                     panic!();
//                 }
//             }
//
//             let to_regain = p.clone();
//             if !state.0.insert(Exclusive(to_regain.into())) {
//                 panic!();
//             }
//             statements.push(FreeStatement::Pack(to_lose, to_regain));
//         }
//
//         // State is correct now
//     }
// }
//
// // Repacks a PCS so it's maximally packed
// // pub struct RepackPackup<'tcx> {
// //     pub packs: Vec<(FxHashSet<mir::Place<'tcx>>, mir::Place<'tcx>)>,
// // }
// //
// // impl<'tcx> RepackPackup<'tcx> {
// //     pub fn new<'mir, 'env>(
// //         tcx: TyCtxt<'tcx>,
// //         mir: &'mir Body<'tcx>,
// //         pcs: PermissionSet<'tcx>,
// //     ) -> EncodingResult<Self>
// //     where
// //         'env: 'mir,
// //         'tcx: 'env,
// //     {
// //         // One packup problem for every Local base (uninit and temps are not packed up)
// //         let mut mir_problems: FxHashMap<Permission<'tcx>, Vec<mir::Place<'tcx>>> =
// //             FxHashMap::default();
// //         let mut packs: Vec<(FxHashSet<mir::Place<'tcx>>, mir::Place<'tcx>)> = Vec::default();
// //
// //         // Split the problem into independent parts
// //         for pcs_permission in pcs.0.iter() {
// //             match pcs_permission {
// //                 perm @ Exclusive(p) | perm @ Uninit(p) => {
// //                     let set_borrow = mir_problems.entry(perm).or_insert(Vec::default());
// //                     (*set_borrow).push(place.clone());
// //                 }
// //                 Shared(_) | Blocked(_) => todo!(),
// //             }
// //         }
// //
// //         let mut mir_problem_iter = mir_problems.drain();
// //         while let Some((_local, mut places)) = mir_problem_iter.next() {
// //             // Fully pack the given place set:
// //
// //             // Order the places by length of their projection lists
// //             places.sort_by(|p0, p1| p0.projection.len().cmp(&p1.projection.len()));
// //             // Pop the least projected place. Can we pack it?
// //
// //             // termination: packs always reduce the length of the projected elements by one
// //             while let Some(p) = places.pop() {
// //                 // TODO: This is pretty bad
// //
// //                 // Strip the last projection from p -> p'
// //                 // generate the unpack of p'... is it contained in places?
// //                 // if so, remove all relevant places and insert packed place
// //                 if let Some(pack_set) = pack_set(tcx, mir, p) {
// //                     if pack_set.iter().all(|pm| (*pm == p) || places.contains(pm)) {
// //                         let to_insert = strip_level(tcx, p)
// //                             .ok_or(PrustiError::internal("unexpected", MultiSpan::new()))?;
// //                         packs.push((pack_set.clone(), to_insert));
// //                         // Remove the pack_set from places
// //                         for to_remove in pack_set.iter() {
// //                             if *to_remove != p {
// //                                 if let Some(pos) = places.iter().position(|p1| *p1 == *to_remove) {
// //                                     places.remove(pos);
// //                                 } else {
// //                                     return Err(PrustiError::internal(
// //                                         format!(
// //                                             "tried to remove a nonexistent element {:?}",
// //                                             to_remove
// //                                         ),
// //                                         MultiSpan::new(),
// //                                     ));
// //                                 }
// //                             }
// //                         }
// //
// //                         // Insert the packed permission back into places
// //                         places.push(to_insert);
// //                         // ouch
// //                         places.sort_by(|p0, p1| p0.projection.len().cmp(&p1.projection.len()));
// //                     }
// //                 }
// //             }
// //         }
// //
// //         Ok(RepackPackup { packs })
// //     }
// //
// //     /// Apply a PCSRepacker to a state
// //     pub fn apply_packings(
// //         &self,
// //         mut state: PCS<'tcx>,
// //         statements: &mut Vec<MicroMirStatement<'tcx>>,
// //         before_pcs: &mut Vec<PCS<'tcx>>,
// //     ) -> EncodingResult<PCS<'tcx>> {
// //         // TODO: Move insert and remove (guarded with linearity) into PCS
// //         for (pre_p, p) in self.packs.iter() {
// //             before_pcs.push(state.clone());
// //
// //             let to_lose: Vec<Place<'tcx>> = pre_p.iter().cloned().collect(); // expand_place(*p, mir, env)?;
// //             for p1 in to_lose.iter() {
// //                 if !state.set.remove(&PCSPermission::new_initialized(
// //                     Mutability::Mut,
// //                     (*p1).into(),
// //                 )) {
// //                     return Err(PrustiError::internal(
// //                         format!("prusti generated an incoherent pack precondition {:?}", p1),
// //                         MultiSpan::new(),
// //                     ));
// //                 }
// //             }
// //
// //             let to_regain = p.clone();
// //
// //             if !state.set.insert(PCSPermission::new_initialized(
// //                 Mutability::Mut,
// //                 to_regain.into(),
// //             )) {
// //                 return Err(PrustiError::internal(
// //                     format!(
// //                         "prusti generated an incoherent pack postcondition: {:?}",
// //                         to_regain
// //                     ),
// //                     MultiSpan::new(),
// //                 ));
// //             }
// //
// //             statements.push(MicroMirStatement::Pack(to_lose, to_regain));
// //         }
// //         return Ok(state);
// //     }
// // }
// //
// // fn strip_level<'tcx>(tcx: TyCtxt<'tcx>, place: Place<'tcx>) -> Option<Place<'tcx>> {
// //     // Place projections use Rust's interned lists, so there can be only one of each list.
// //     //  (important for correctness! Rust compares projection lists by interned
// //     //   list address)
// //     // See implementation of mk_place_elem in rustc_middle/ty/context.rs
// //     let mut projection = place.projection.to_vec();
// //     projection.pop()?;
// //     Some(Place {
// //         local: place.local,
// //         projection: tcx.intern_place_elems(&projection),
// //     })
// // }
// //
// // // Compute the set of places needed to pack a place
// // fn pack_set<'mir, 'tcx: 'mir>(
// //     tcx: TyCtxt<'tcx>,
// //     mir: &'mir Body<'tcx>,
// //     place: Place<'tcx>,
// // ) -> Option<FxHashSet<Place<'tcx>>> {
// //     Some(
// //         expand_struct_place(strip_level(tcx, place)?, mir, tcx, None)
// //             .iter()
// //             .cloned()
// //             .collect(),
// //     )
// // }
// //
//
