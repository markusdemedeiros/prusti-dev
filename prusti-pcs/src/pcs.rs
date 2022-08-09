// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_variables)]
use super::pcs::Resource::*;
use crate::{syntax::PCSPermission, util::EncodingResult};
use core::cell::*;
use itertools::Either::{Left, Right};
use prusti_interface::environment::{
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
};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{
        mir,
        mir::{
            AggregateKind::*, Operand, Operand::*, Rvalue::*, StatementKind::*, Terminator,
            TerminatorKind, TerminatorKind::*,
        },
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
enum Resource<T>
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
struct PermissionSet<'tcx>(FxHashSet<Permission<'tcx>>);

impl<'tcx> Default for PermissionSet<'tcx> {
    fn default() -> Self {
        PermissionSet {
            0: FxHashSet::default(),
        }
    }
}

fn usize_place<'tcx>(id: usize) -> mir::Place<'tcx> {
    mir::Local::from_usize(id).into()
}

////////////////////////////////////////////////////////////////////////////////
// Guarded PCS

#[derive(Clone)]
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

#[derive(Clone)]
struct Guard<'tcx> {
    loan: usize,
    rhs: Permission<'tcx>,
    // Generalization: guards can be stronger expressions than a single bb
    // Generalization: for struct with borrow RHS can be not top-level place
    lhs: Vec<(mir::BasicBlock, PlaceHole<'tcx>)>,
}

#[derive(Clone)]
struct GuardSet<'tcx>(Vec<Guard<'tcx>>);

impl<'tcx> Default for GuardSet<'tcx> {
    fn default() -> Self {
        GuardSet { 0: Vec::default() }
    }
}

////////////////////////////////////////////////////////////////////////////////
// State

#[derive(Clone)]
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

enum FreeStatement<'tcx> {
    Pack(Vec<mir::Place<'tcx>>, mir::Place<'tcx>),
    Unack(mir::Place<'tcx>, Vec<mir::Place<'tcx>>),
    Nop,
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

            println!("\t{:?} {:?}", location, stmt);
            let active_loans = self.polonius_info.get_active_loans(location, false);
            print!("\tLoans: ");
            for l in active_loans {
                if let Ok(Some(assign)) = self.polonius_info.get_assignment_for_loan(l) {
                    if let Assign(box (b, _)) = assign.kind {
                        print!("{:?} ({:?}), ", l, b);
                    } else {
                        panic!();
                    }
                } else {
                    panic!();
                }
            }
            println!();

            // 2. Apply Polonius facts for dying loans at this point
            // 2.1. Remove all guards from GPCS
            // 2.2. While we can regain permissions, do so

            // 3. Repack for Hoare condition

            // 3.5: Weaken

            // 4. Apply hoare semantics
            for p in self.precondition_statement(&stmt.kind).iter() {
                if !working_pcs.free.0.remove(p) {
                    println!("{:?}", working_pcs.free);
                    println!("{:?}", p);
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
