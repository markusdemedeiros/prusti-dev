// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
use crate::{
    syntax::{LinearResource, MicroMirStatement, PCSPermission, PCSPermissionKind, PCS},
    util::*,
};
use analysis::mir_utils::expand_struct_place;
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    errors::MultiSpan,
    middle::{
        mir::{Body, Local, Mutability, Place},
        ty::TyCtxt,
    },
};

/// Repacks a PCS so it's maximally packed
pub struct RepackPackup<'tcx> {
    pub packs: Vec<(FxHashSet<Place<'tcx>>, Place<'tcx>)>,
}

impl<'tcx> RepackPackup<'tcx> {
    pub fn new<'mir, 'env>(
        tcx: TyCtxt<'tcx>,
        mir: &'mir Body<'tcx>,
        pcs: PCS<'tcx>,
    ) -> EncodingResult<Self>
    where
        'env: 'mir,
        'tcx: 'env,
    {
        // One packup problem for every Local base (uninit and temps are not packed up)
        let mut mir_problems: FxHashMap<Local, Vec<Place<'tcx>>> = FxHashMap::default();
        let mut packs: Vec<(FxHashSet<Place<'tcx>>, Place<'tcx>)> = Vec::default();

        // Split the problem into independent parts
        for pcs_permission in pcs.free.iter() {
            match pcs_permission.target {
                LinearResource::Mir(place) => {
                    if pcs_permission.kind == PCSPermissionKind::Exclusive {
                        let set_borrow = mir_problems
                            .entry(place.local.clone())
                            .or_insert(Vec::default());
                        (*set_borrow).push(place.clone());
                    }
                }
                LinearResource::Tmp(_) => {
                    // Not changed by packs/unpacks
                }
            }
        }

        let mut mir_problem_iter = mir_problems.drain();
        while let Some((_local, mut places)) = mir_problem_iter.next() {
            // Fully pack the given place set:

            // Order the places by length of their projection lists
            places.sort_by(|p0, p1| p0.projection.len().cmp(&p1.projection.len()));
            // Pop the least projected place. Can we pack it?

            // termination: packs always reduce the length of the projected elements by one
            while let Some(p) = places.pop() {
                // TODO: This is pretty bad

                // Strip the last projection from p -> p'
                // generate the unpack of p'... is it contained in places?
                // if so, remove all relevant places and insert packed place
                if let Some(pack_set) = pack_set(tcx, mir, p) {
                    if pack_set.iter().all(|pm| (*pm == p) || places.contains(pm)) {
                        let to_insert = strip_level(tcx, p)
                            .ok_or(PrustiError::internal("unexpected", MultiSpan::new()))?;
                        packs.push((pack_set.clone(), to_insert));
                        // Remove the pack_set from places
                        for to_remove in pack_set.iter() {
                            if *to_remove != p {
                                if let Some(pos) = places.iter().position(|p1| *p1 == *to_remove) {
                                    places.remove(pos);
                                } else {
                                    return Err(PrustiError::internal(
                                        format!(
                                            "tried to remove a nonexistent element {:?}",
                                            to_remove
                                        ),
                                        MultiSpan::new(),
                                    ));
                                }
                            }
                        }

                        // Insert the packed permission back into places
                        places.push(to_insert);
                        // ouch
                        places.sort_by(|p0, p1| p0.projection.len().cmp(&p1.projection.len()));
                    }
                }
            }
        }

        Ok(RepackPackup { packs })
    }

    /// Apply a PCSRepacker to a state
    pub fn apply_packings(
        &self,
        mut state: PCS<'tcx>,
        statements: &mut Vec<MicroMirStatement<'tcx>>,
        before_pcs: &mut Vec<PCS<'tcx>>,
    ) -> EncodingResult<PCS<'tcx>> {
        // TODO: Move insert and remove (guarded with linearity) into PCS
        for (pre_p, p) in self.packs.iter() {
            before_pcs.push(state.clone());

            let to_lose: Vec<Place<'tcx>> = pre_p.iter().cloned().collect(); // expand_place(*p, mir, env)?;
            for p1 in to_lose.iter() {
                if !state.free.remove(&PCSPermission::new_initialized(
                    Mutability::Mut,
                    (*p1).into(),
                )) {
                    return Err(PrustiError::internal(
                        format!("prusti generated an incoherent pack precondition {:?}", p1),
                        MultiSpan::new(),
                    ));
                }
            }

            let to_regain = p.clone();

            if !state.free.insert(PCSPermission::new_initialized(
                Mutability::Mut,
                to_regain.into(),
            )) {
                return Err(PrustiError::internal(
                    format!(
                        "prusti generated an incoherent pack postcondition: {:?}",
                        to_regain
                    ),
                    MultiSpan::new(),
                ));
            }

            statements.push(MicroMirStatement::Pack(to_lose, to_regain));
        }
        return Ok(state);
    }
}

fn strip_level<'tcx>(tcx: TyCtxt<'tcx>, place: Place<'tcx>) -> Option<Place<'tcx>> {
    // Place projections use Rust's interned lists, so there can be only one of each list.
    //  (important for correctness! Rust compares projection lists by interned
    //   list address)
    // See implementation of mk_place_elem in rustc_middle/ty/context.rs
    let mut projection = place.projection.to_vec();
    projection.pop()?;
    Some(Place {
        local: place.local,
        projection: tcx.intern_place_elems(&projection),
    })
}

// Compute the set of places needed to pack a place
fn pack_set<'mir, 'tcx: 'mir>(
    tcx: TyCtxt<'tcx>,
    mir: &'mir Body<'tcx>,
    place: Place<'tcx>,
) -> Option<FxHashSet<Place<'tcx>>> {
    Some(
        expand_struct_place(strip_level(tcx, place)?, mir, tcx, None)
            .iter()
            .cloned()
            .collect(),
    )
}
