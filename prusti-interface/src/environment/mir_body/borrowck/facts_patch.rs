use crate::environment::mir_body::patch::MirPatch;
use super::facts::BorrowckFacts;

impl BorrowckFacts {
    pub fn apply_patch<'tcx>(&mut self, patch: &MirPatch<'tcx>) {
        unimplemented!();
    }
}