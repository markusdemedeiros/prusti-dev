use super::ProcedureEncoder;
use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    mir::{errors::ErrorInterface, places::PlacesEncoderInterface},
};
use prusti_interface::utils;
use rustc_hash::FxHashMap;
use rustc_middle::mir;
use vir_crate::high::{self as vir_high, builders::procedure::BasicBlockBuilder};

pub(super) mod compiler;
pub(super) mod mir_transform;
pub(super) mod mir_dataflow;

pub(super) struct DropFlags<'tcx> {
    /// The drop flag is true if the place needs to be dropped.
    flags: FxHashMap<mir::Place<'tcx>, vir_high::VariableDecl>,
}

impl<'tcx> DropFlags<'tcx> {
    pub(super) fn build(body: &mir::Body<'tcx>) -> Self {
        let mut flags = FxHashMap::default();
        for bb_data in body.basic_blocks().iter() {
            match bb_data.terminator().kind {
                mir::TerminatorKind::Drop { place, .. }
                | mir::TerminatorKind::DropAndReplace { place, .. } => {
                    let identifier = flags.len();
                    flags.insert(
                        place,
                        vir_high::VariableDecl::new(
                            format!("drop_flag${}", identifier),
                            vir_high::Type::MBool,
                        ),
                    );
                }
                _ => {}
            };
        }
        Self { flags }
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> ProcedureEncoder<'p, 'v, 'tcx> {
    pub(super) fn encode_drop_flag_initialization(
        &mut self,
    ) -> SpannedEncodingResult<Vec<vir_high::Statement>> {
        let mut statements = Vec::new();
        for (flag_place, flag_variable) in self.drop_flags.flags.clone() {
            let initialized = self.mir.args_iter().any(|arg| flag_place.local == arg);
            let assign_statement = vir_high::Statement::ghost_assign_no_pos(
                flag_variable,
                vir_high::Expression::constant_no_pos(initialized.into(), vir_high::Type::MBool),
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

    fn set_drop_flag(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        place: mir::Place<'tcx>,
        value: bool,
    ) -> SpannedEncodingResult<()> {
        let mut statements = Vec::new();
        for (flag_place, flag_variable) in &self.drop_flags.flags {
            if utils::is_prefix(flag_place, &place) {
                let assign_statement = vir_high::Statement::ghost_assign_no_pos(
                    flag_variable.clone(),
                    vir_high::Expression::constant_no_pos(value.into(), vir_high::Type::MBool),
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

    pub(super) fn set_drop_flag_false(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        place: mir::Place<'tcx>,
    ) -> SpannedEncodingResult<()> {
        self.set_drop_flag(block_builder, location, place, false)
    }

    pub(super) fn set_drop_flag_true(
        &mut self,
        block_builder: &mut BasicBlockBuilder,
        location: mir::Location,
        place: mir::Place<'tcx>,
    ) -> SpannedEncodingResult<()> {
        self.set_drop_flag(block_builder, location, place, true)
    }

    pub(super) fn get_drop_flag(
        &self,
        place: mir::Place<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        Ok(self.drop_flags.flags[&place].clone().into())
    }
}
