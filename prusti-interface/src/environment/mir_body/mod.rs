use rustc_middle::mir;

pub mod borrowck;
pub mod patch;

pub fn apply_patch<'tcx>(
    patch: self::patch::MirPatch<'tcx>,
    body: &mir::Body<'tcx>,
    borrowck_facts: &mut self::borrowck::facts::BorrowckFacts,
) -> mir::Body<'tcx> {
    borrowck_facts.apply_patch(&patch);
    let mut body = body.clone();
    patch.apply(&mut body);
    body
}
