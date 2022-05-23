use super::{AllInputFacts, BorrowckFacts, LocationTable};
use crate::environment::mir_body::patch::MirPatch;

pub fn apply_patch_to_borrowck<'tcx>(
    borrowck_input_facts: &mut AllInputFacts,
    location_table: &mut LocationTable,
    patch: &MirPatch<'tcx>,
) {
    unimplemented!();
}
