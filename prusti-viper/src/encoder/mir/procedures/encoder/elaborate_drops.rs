// This file was taken from the compiler:
// https://github.com/rust-lang/rust/blob/master/compiler/rustc_mir_transform/src/elaborate_drops.rs
// This file is licensed under Apache 2.0
// (https://github.com/rust-lang/rust/blob/86f5e177bca8121e1edc9864023a8ea61acf9034/LICENSE-APACHE)
// and MIT
// (https://github.com/rust-lang/rust/blob/86f5e177bca8121e1edc9864023a8ea61acf9034/LICENSE-MIT).

// Changes:
// + Fix compilation errors.
// + Allow obtaining the elaboration patch (this is the main reason for
//   duplication).

use std::collections::BTreeMap;

use log::debug;
use prusti_interface::utils;
use rustc_hash::FxHashMap;
use rustc_index::bit_set::BitSet;
use rustc_middle::{mir::*, ty::TyCtxt};
use rustc_mir_dataflow::{
    impls::MaybeInitializedPlaces, move_paths::LookupResult, on_all_drop_children_bits, Analysis,
    MoveDataParamEnv,
};

/// Returns the set of basic blocks whose unwind edges are known
/// to not be reachable, because they are `drop` terminators
/// that can't drop anything.
pub(super) fn find_dead_unwinds<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    env: &MoveDataParamEnv<'tcx>,
) -> BitSet<BasicBlock> {
    debug!("find_dead_unwinds({:?})", body.span);
    // We only need to do this pass once, because unwind edges can only
    // reach cleanup blocks, which can't have unwind edges themselves.
    let mut dead_unwinds = BitSet::new_empty(body.basic_blocks().len());
    let mut flow_inits = MaybeInitializedPlaces::new(tcx, body, env)
        .into_engine(tcx, body)
        .pass_name("find_dead_unwinds")
        .iterate_to_fixpoint()
        .into_results_cursor(body);
    for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
        let place = match bb_data.terminator().kind {
            TerminatorKind::Drop {
                ref place,
                unwind: Some(_),
                ..
            }
            | TerminatorKind::DropAndReplace {
                ref place,
                unwind: Some(_),
                ..
            } => place,
            _ => continue,
        };

        debug!("find_dead_unwinds @ {:?}: {:?}", bb, bb_data);

        let path = if let LookupResult::Exact(path) = env.move_data.rev_lookup.find(place.as_ref())
        {
            path
        } else {
            debug!("find_dead_unwinds: has parent; skipping");
            continue;
        };

        flow_inits.seek_before_primary_effect(body.terminator_loc(bb));
        debug!(
            "find_dead_unwinds @ {:?}: path({:?})={:?}; init_data={:?}",
            bb,
            place,
            path,
            flow_inits.get()
        );

        let mut maybe_live = false;
        on_all_drop_children_bits(tcx, body, env, path, |child| {
            maybe_live |= flow_inits.contains(child);
        });

        debug!("find_dead_unwinds @ {:?}: maybe_live={}", bb, maybe_live);
        if !maybe_live {
            dead_unwinds.insert(bb);
        }
    }

    dead_unwinds
}

use rustc_middle::mir;
use vir_crate::high::{self as vir_high, builders::procedure::BasicBlockBuilder};
use crate::encoder::{errors::{SpannedEncodingResult, ErrorCtxt}, mir::{errors::ErrorInterface, places::PlacesEncoderInterface}};
use super::ProcedureEncoder;

pub(super) struct DropFlags<'tcx> {
    /// The drop flag is true if the place needs to be dropped.
    flags: FxHashMap<mir::Place<'tcx>, vir_high::VariableDecl>,
}

impl<'tcx> DropFlags<'tcx> {
    pub(super) fn build(body: &Body<'tcx>) -> Self {
        let mut flags = FxHashMap::default();
        for bb_data in body.basic_blocks().iter() {
            match bb_data.terminator().kind {
                TerminatorKind::Drop {
                    place,
                    ..
                }
                | TerminatorKind::DropAndReplace {
                    place,
                    ..
                } => {
                    let identifier = flags.len();
                    flags.insert(place, vir_high::VariableDecl::new(format!("drop_flag${}", identifier), vir_high::Type::MBool));
                },
                _ => {},
            };
        }
        Self { flags }
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {

    pub(super) fn encode_drop_flag_initialization(&mut self) -> SpannedEncodingResult<Vec<vir_high::Statement>> {
        let mut statements = Vec::new();
        for (flag_place, flag_variable) in self.drop_flags.flags.clone() {
            let initialized = self.mir.args_iter().any(|arg| flag_place.local == arg);
            let assign_statement = vir_high::Statement::ghost_assign_no_pos(
                flag_variable,
                vir_high::Expression::constant_no_pos(
                    initialized.into(),
                    vir_high::Type::MBool,
                ),
            );
            let span = self.encoder.get_local_span(self.mir, flag_place.local)?;
            statements.push(self.encoder.set_statement_error_ctxt(
                assign_statement,
                span,
                ErrorCtxt::SetDropFlag,
                self.def_id,
            )?);
        }
        Ok(statements)
    }

    pub(super) fn set_drop_flag_false(&mut self,
        block_builder: &mut BasicBlockBuilder, location: mir::Location, place: mir::Place<'tcx>
) -> SpannedEncodingResult<()> {
    let mut statements = Vec::new();
        for (flag_place, flag_variable) in &self.drop_flags.flags {
            if utils::is_prefix(flag_place, &place) {
                let assign_statement = vir_high::Statement::ghost_assign_no_pos(
                    flag_variable.clone(),
                    vir_high::Expression::constant_no_pos(
                        false.into(),
                        vir_high::Type::MBool,
                    ),
                );
                statements.push(assign_statement);
            }
        }
        for statement in statements {
            block_builder.add_statement(self.set_statement_error(
                location,
                ErrorCtxt::SetDropFlag,
                statement,
            )?);
        }
        Ok(())
    }

    pub(super) fn get_drop_flag(&self, place: mir::Place<'tcx>) -> SpannedEncodingResult<vir_high::Expression> {
        Ok(self.drop_flags.flags[&place].clone().into())
    }
}