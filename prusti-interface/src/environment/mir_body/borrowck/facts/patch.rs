use super::BorrowckFacts;
use crate::environment::mir_body::patch::MirPatch;

impl BorrowckFacts {
    pub fn apply_patch<'tcx>(&mut self, patch: &MirPatch<'tcx>) {
        unimplemented!();
    }
}
