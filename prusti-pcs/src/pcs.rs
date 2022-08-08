// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_variables)]
use super::pcs::Resource::*;
use crate::util::EncodingResult;
use itertools::Either::{Left, Right};
use prusti_interface::environment::{
    borrowck::facts::Loan,
    mir_analyses::{
        allocation::{compute_definitely_allocated, DefinitelyAllocatedAnalysisResult},
        initialization::{compute_definitely_initialized, DefinitelyInitializedAnalysisResult},
    },
    Environment, Procedure,
};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{
        mir,
        mir::{Terminator, TerminatorKind, TerminatorKind::*},
    },
};

/// Computes the PCS and prints it to the console
/// Currently the entry point for the compiler
pub fn dump_pcs<'env, 'tcx: 'env>(env: &'env Environment<'tcx>) -> EncodingResult<()> {
    for proc_id in env.get_annotated_procedures().iter() {
        println!("id: {:#?}", env.get_unique_item_name(*proc_id));
        let current_procedure: Procedure<'tcx> = env.get_procedure(*proc_id);
        let mir: &mir::Body<'tcx> = current_procedure.get_mir();
        let mut ctx = PCSctx {
            mir,
            env,
            init_analysis: compute_definitely_initialized((*proc_id).clone(), mir, env.tcx()),
            alloc_analysis: compute_definitely_allocated((*proc_id).clone(), mir),
        };

        ctx.compute_pcs();
    }
    Ok(())
}

////////////////////////////////////////////////////////////////////////////////
// Permissions (Free PCS)

#[derive(Clone)]
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

type TemporaryPlace = usize;

type TemporaryPermission<'tcx> = Resource<TemporaryPlace>;

#[derive(Clone)]
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
    // NonLinear(Place<'tcx>),
    None,
}

#[derive(Clone)]
struct Guard<'tcx> {
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
// MicroMir

enum MicroMirStatement<'tcx> {
    //
    Set(TemporaryPlace, Permission<'tcx>),
    Move(Permission<'tcx>, TemporaryPlace),
    Duplicate(Permission<'tcx>, TemporaryPlace),
    Constant(mir::Constant<'tcx>, TemporaryPlace),

    // Operations for RHS
    // NullOp(NullOp, TemporaryPlace),
    // UnOp(UnOp, TemporaryPlace, TemporaryPlace),
    // BinaryOp(BinOp, bool, TemporaryPlace, TemporaryPlace, TemporaryPlace),
    // Len(Place<'tcx>, TemporaryPlace, Mutability),

    // Struct Operations
    Aggregate(Vec<Permission<'tcx>>, Permission<'tcx>),

    // Scope Operations
    Allocate(mir::Local),
    Deallocate(mir::Local),

    // Free PCS operations
    Pack(PermissionSet<'tcx>, Permission<'tcx>),
    Unpack(Permission<'tcx>, PermissionSet<'tcx>),

    // The approximation check operator (interface to guarded PCS)
    Lcm(Permission<'tcx>),
}
enum MicroMirTerminator {
    Jump(mir::BasicBlock),
    JumpInt(TemporaryPlace, Vec<(Option<u128>, mir::BasicBlock)>),
    Return(),
    FailVerif(),
}

////////////////////////////////////////////////////////////////////////////////
// MIR translator

fn translate_statement<'mir, 'tcx: 'mir>(
    statement: mir::StatementKind<'tcx>,
) -> Vec<MicroMirStatement<'tcx>> {
    todo!();
}

////////////////////////////////////////////////////////////////////////////////
// State and Hoare style semantics

#[derive(Clone)]
struct PCSState<'tcx> {
    free: PermissionSet<'tcx>,
    guarded: GuardSet<'tcx>,
}

impl<'tcx> Default for PCSState<'tcx> {
    fn default() -> Self {
        PCSState {
            free: PermissionSet::default(),
            guarded: GuardSet::default(),
        }
    }
}

pub trait HoareSemantics {
    type PRE;
    type POST;
    fn precondition(&self) -> Self::PRE;
    fn postcondition(&self) -> Self::POST;
}

// Do we need to reify an interface for wand semantics?

////////////////////////////////////////////////////////////////////////////////
// Encoding

struct CFGBody<'tcx> {
    flow_exclusions: Vec<(mir::BasicBlock, bool)>,
    statements: Vec<MicroMirStatement<'tcx>>,
    pre_pcs: Vec<PCSState<'tcx>>,
    end_pcs: FxHashMap<mir::BasicBlock, PCSState<'tcx>>,
}

impl<'tcx> Default for CFGBody<'tcx> {
    fn default() -> Self {
        CFGBody {
            flow_exclusions: Vec::default(),
            statements: Vec::default(),
            pre_pcs: Vec::default(),
            end_pcs: FxHashMap::default(),
        }
    }
}

struct CFG<'tcx>(FxHashMap<mir::BasicBlock, CFGBody<'tcx>>);

impl<'tcx> Default for CFG<'tcx> {
    fn default() -> Self {
        CFG {
            0: FxHashMap::default(),
        }
    }
}

impl<'tcx> CFG<'tcx> {
    pub fn lookup_final_state(
        &self,
        bb: &mir::BasicBlock,
        to: &mir::BasicBlock,
    ) -> Option<PCSState<'tcx>> {
        Some(self.0.get(bb)?.end_pcs.get(to)?.clone())
    }
}

////////////////////////////////////////////////////////////////////////////////
/// Helper: gensym (hack for basic blocks)

struct Gensym {
    counter: u32,
}

impl Gensym {
    pub fn new() -> Self {
        Gensym {
            counter: mir::BasicBlock::MAX_AS_U32,
        }
    }

    pub fn gen_block(&mut self) -> mir::BasicBlock {
        let ret = mir::BasicBlock::from_u32(self.counter);
        self.counter -= 1;
        ret
    }
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

type FlowExclusion = Vec<(mir::BasicBlock, bool)>;
// interp true iff basic block is previously computed.

/// Data structure for all computations of the CondPCS
impl<'mir, 'env: 'mir, 'tcx: 'env> PCSctx<'mir, 'env, 'tcx> {
    fn compute_pcs(&mut self) -> Option<CFG<'tcx>> {
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
        let mut cfg: CFG<'tcx> = CFG::default();
        let mut pcs_iter = PCSIter::new(self.mir, self.initial_state());

        while let Some((working_block, flows)) = pcs_iter.next() {
            // Figure out if we're at a loop head (redundant work)
            /*
               let to_join = flows
                   .iter()
                   .map(|(bb, is_done)| {
                       if *is_done {
                           if let Some(fs) = cfg.lookup_final_state(bb, working_block.block()) {
                               ((*bb).clone(), fs)
                           } else {
                               panic!()
                           }
                       } else {
                           // What do to in conditional case
                           todo!();
                       }
                   })
                   .collect::<Vec<(mir::BasicBlock, PCSState<'tcx>)>>();
            */

            // TODO: Implement the conditional join here
            // Note: Each CFG edge will be traversed exactly once as long as the prior block is done.
            // Thereofre, we're free to add a FREE PCS block in between when we're doing to_join.

            // Update working_block with it's proper PCS

            // Now in the joined state, we can work through the body
            let mut body = self.translate_body(&working_block, flows);

            if let Some(term) = &self
                .mir
                .basic_blocks()
                .get(*working_block.block())?
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

            pcs_iter.finish(*(working_block.block()));
        }

        None
        // todo!();
    }

    fn initial_state(&self) -> DirtyBlock<'tcx> {
        // TODO: This is not correct, it misses paramaters
        DirtyBlock::new(PCSState::default(), mir::BasicBlock::from_u32(0 as u32))
    }

    // Returns a new CFGBlock with completely translated body
    fn translate_body(&self, dirty: &DirtyBlock, flow_exclusions: FlowExclusion) -> CFGBody<'tcx> {
        let mut block_body_data = CFGBody::default();
        // For each statement:
        println!("Translating block number {:?}", dirty.block());
        // 1. Read and apply Polonius facts
        // TODO

        // 2. Retrieve MicroMir instruction sequence
        // 3. Connstruct an iterator of MicroMirStatements (including terminator)
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

        CFGBody::default()
    }

    fn flow_join(&self, flows: Vec<(mir::BasicBlock, bool)>) {}

    /// Encodes the body-part of the statement- location can include terminators
    ///     (but terminator tranlation is a different function)
    fn translate_location(
        &self,
        location: mir::Location,
    ) -> (Vec<MicroMirStatement<'tcx>>, Option<MicroMirTerminator>) {
        if let Some(stmt) = self.mir.stmt_at(location).left() {
            match stmt {
                Assign(box (p_dest, Use(op))) => (vec![]),
                StorageDead(local) => todo!(),
                StorageLive(local) => todo!(),
                Assign(box (dest, Aggregate(box Adt(_, _, _, _, _), operands))) => todo!(),
                FakeRead(box (_, _)) => (vec![], None),
                AscribeUserType(box (_p, _proj), _variance) => (vec![], None),
                _ => todo!(),
            }
        }
        if let Some(term) = self.mir.stmt_at(location).right() {
            // compute_framing.visit_terminator(term, location);
        }
        todo!()
    }

    fn translate_operand(&self, operand: mir::Operand<'tcx>) -> MicroMirStatement<'tcx> {
        match operand {
            mir::Operand::Copy(p) => MicroMirStatement::Duplicate(Exclusive(p), 1),
            _ => todo!(),
        }
    }

    // match op {
    //             Copy(p) => {
    //                 let p_mut = Self::lookup_place_mutability(&p, ctx.mir())?;
    //                 ctx.push_stmt(MicroMirStatement::Duplicate(p.clone(), into, p_mut));
    //                 return Ok(p_mut);
    //             }
    //             Move(p) => {
    //                 ctx.push_stmt(MicroMirStatement::Move(p.clone(), into));
    //                 return Ok(Mut);
    //             }
    //             Constant(box k) => {
    //                 ctx.push_stmt(MicroMirStatement::Constant(*k, into));
    //                 return Ok(Mut);
    //             }
    //         }
}
