use self::borrowck::facts::{patch::apply_patch_to_borrowck, AllInputFacts, LocationTable};
use rustc_middle::mir;

pub mod borrowck;
pub mod patch;

pub fn apply_patch<'tcx>(
    patch: self::patch::MirPatch<'tcx>,
    body: &mir::Body<'tcx>,
    borrowck_input_facts: &mut AllInputFacts,
    location_table: &mut LocationTable,
) -> mir::Body<'tcx> {
    apply_patch_to_borrowck(borrowck_input_facts, location_table, &patch, &body);
    let mut body = body.clone();
    patch.apply(&mut body);
    body
}
