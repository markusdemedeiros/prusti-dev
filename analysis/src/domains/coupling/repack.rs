// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{cmp::Ordering, collections::BTreeSet, fmt};

use crate::{
    abstract_interpretation::{AbstractState, AnalysisResult},
    mir_utils::{is_prefix, Place, PlaceImpl},
};
use prusti_rustc_interface::{
    borrowck::consumers::RustcFacts,
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{
        mir,
        mir::{BasicBlock, Body, Local, Location, Mutability},
        ty::TyCtxt,
    },
    polonius_engine::FactTypes,
};

// These types are stolen from Prusti interface
pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;

#[derive(PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub struct Tagged<Data, Tag> {
    pub data: Data,
    pub tag: Option<Tag>,
}

impl<Data, Tag> Tagged<Data, Tag> {
    // Tag a place if it is not already tagged
    pub fn tag(&mut self, t: Tag) {
        if self.tag.is_none() {
            self.tag = Some(t);
        }
    }

    pub fn untagged(data: Data) -> Self {
        Self { data, tag: None }
    }

    pub fn tagged(data: Data, tag: Tag) -> Self {
        Self {
            data,
            tag: Some(tag),
        }
    }

    pub fn is_tagged(&self) -> bool {
        self.tag.is_some()
    }
}

impl<Data: fmt::Debug, Tag: fmt::Debug> fmt::Debug for Tagged<Data, Tag> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.tag {
            Some(t) => write!(f, "{:?}@{:?}", self.data, t),
            None => write!(f, "{:?}", self.data),
        }
    }
}

/// Linear resources
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Resource<'tcx> {
    Place(Place<'tcx>),
    Borrow(Loan),
}

/// Permission Kinds
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PermissionKind {
    Excl,
    Read,
    ShallowExcl,
    ShallowRead,
}

/// Capability
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Capability<'tcx> {
    pub resource: Resource<'tcx>,
    pub permission: Tagged<PermissionKind, Location>,
}

impl fmt::Debug for PermissionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PermissionKind::Excl => write!(f, "E"),
            PermissionKind::Read => write!(f, "R"),
            PermissionKind::ShallowExcl => write!(f, "e"),
            PermissionKind::ShallowRead => write!(f, "r"),
        }
    }
}

impl<'tcx> fmt::Debug for Resource<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Resource::Place(p) => write!(f, "{:?}", p),
            Resource::Borrow(l) => write!(f, "{:?}", l),
        }
    }
}

impl<'tcx> fmt::Debug for Capability<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} {:?}", self.permission, self.resource)
    }
}

impl<'tcx> Capability<'tcx> {
    /// Tags a node at a point, if it isn't already untagged
    pub fn kill(&mut self, l: &Location) {
        self.permission.tag(*l);
    }

    /// Determine if a kill should tag the current place:
    ///     - A borrow should be tagged only if it is untagged, and equal to to_kill
    ///     - A place should be tagged only if it is untagged, and to_kill is its prefix
    pub fn should_tag(&self, to_kill: &Self) -> bool {
        if self.is_tagged() {
            return false;
        }

        match (&self.resource, &to_kill.resource) {
            (Resource::Place(p_self), Resource::Place(p_other)) => is_prefix(*p_self, *p_other),
            (Resource::Borrow(l_self), Resource::Borrow(l_other)) => l_self == l_other,
            _ => false,
        }
    }

    pub fn is_tagged(&self) -> bool {
        self.permission.is_tagged()
    }
}

/// Helper function: Get mutability associated to a local
pub fn loc_mutability<'mir, 'tcx: 'mir>(
    body: &'mir Body<'tcx>,
    local: &Local,
) -> Option<Mutability> {
    Some(body.local_decls.get(*local)?.mutability)
}

/// Get the mutability associated with a place
pub fn place_mutability<'mir, 'tcx: 'mir>(
    body: &'mir Body<'tcx>,
    place: &Place<'tcx>,
) -> Option<Mutability> {
    loc_mutability(body, &place.to_mir_place().local)
}

/// Get the deep capabilty associate with a place
pub fn place_deep_cap<'mir, 'tcx: 'mir>(
    body: &'mir Body<'tcx>,
    place: &Place<'tcx>,
) -> Option<PermissionKind> {
    match place_mutability(body, place)? {
        Mutability::Mut => Some(PermissionKind::Excl),
        Mutability::Not => Some(PermissionKind::Read),
    }
}

/// Get the shallow capabilty associate with a place
pub fn place_shallow_cap<'mir, 'tcx: 'mir>(
    body: &'mir Body<'tcx>,
    place: &Place<'tcx>,
) -> Option<PermissionKind> {
    match place_mutability(body, place)? {
        Mutability::Mut => Some(PermissionKind::ShallowExcl),
        Mutability::Not => Some(PermissionKind::ShallowRead),
    }
}

/// Struct to help us do repacks at the capability level
/// Helper functions for places live in mir_utils; this struct
/// does repacks at the capability level
pub struct Repacker<'mir, 'tcx: 'mir> {
    mir: &'mir Body<'tcx>,
    tcx: TyCtxt<'tcx>,
}

pub enum FreeOp<'tcx> {
    Pack(Capability<'tcx>),
    Unpack(Capability<'tcx>),
}

pub struct RepackOp<'tcx> {
    op: FreeOp<'tcx>,
    pre: BTreeSet<Capability<'tcx>>,
    post: BTreeSet<Capability<'tcx>>,
}

/// A sequence of repack ops
pub struct Repacking<'tcx> {
    ops: Vec<RepackOp<'tcx>>,
    pre: BTreeSet<Capability<'tcx>>,
    post: BTreeSet<Capability<'tcx>>,
}

pub trait Triple<'tcx> {
    fn pre(&self) -> &BTreeSet<Capability<'tcx>>;
    fn post(&self) -> &BTreeSet<Capability<'tcx>>;

    // Helper function to apply a Hoare triple at the PCS level
    // The triple must be met exactly, ie must be correctly repacked
    // beforehand.
    fn apply_triple(&self, set: &mut BTreeSet<Capability<'tcx>>) {
        for c in self.pre().iter() {
            assert!(set.remove(c))
        }
        for c in self.post().iter() {
            assert!(set.insert(c.clone()));
        }
    }
}

impl<'tcx> Triple<'tcx> for Repacking<'tcx> {
    fn pre(&self) -> &BTreeSet<Capability<'tcx>> {
        &self.pre
    }

    fn post(&self) -> &BTreeSet<Capability<'tcx>> {
        &self.post
    }
}

impl<'tcx> Triple<'tcx> for RepackOp<'tcx> {
    fn pre(&self) -> &BTreeSet<Capability<'tcx>> {
        &self.pre
    }

    fn post(&self) -> &BTreeSet<Capability<'tcx>> {
        &self.post
    }
}

impl<'mir, 'tcx: 'mir> Repacker<'mir, 'tcx> {
    /// Determine the sequence of ops needed to repack source to include target
    /// If possible, it returns a sequence of steps repack. Includes the overall
    /// transfer of caps
    pub fn repack_to_include(
        &self,
        source: &BTreeSet<Capability<'tcx>>,
        target: &Capability<'tcx>,
    ) -> Option<Repacking<'tcx>> {
        let mut working_set = source.clone();
        let mut ops = vec![];

        loop {
            let (closest, ord) = Self::closest_in_set(&working_set, target)?;
            match ord {
                Ordering::Equal => break,
                Ordering::Less => {
                    let next_unpack = self.valid_unpacks(&closest)?;
                    next_unpack.apply_triple(&mut working_set);
                    ops.push(next_unpack);
                }
                Ordering::Greater => {
                    let next_pack = self.valid_packs(&closest)?;
                    next_pack.apply_triple(&mut working_set);
                    ops.push(next_pack);
                }
            }
        }

        // (hack)
        // There are no repack rules that have weakest trips like {A, X} ... {A, Y}
        // So we remove common elements in both to get the weakest triple
        // A better way would be to update pre and post during the iteration w/
        // a more general method in Triple (eg. track_weakest_triple) or something.
        let intersection = source.intersection(&working_set).cloned().collect();
        let pre = source.difference(&intersection).cloned().collect();
        let post = working_set.difference(&intersection).cloned().collect();
        Some(Repacking { ops, pre, post })
    }

    /// Determines which capabilities this place unpacks to
    pub fn valid_unpacks(&self, c: &Capability<'tcx>) -> Option<RepackOp<'tcx>> {
        // Borrows can't be unpacked
        let p = match c.resource {
            Resource::Borrow(_) => return None,
            Resource::Place(p) => p,
        };

        // For borrow-typed places, unpack to their deref according to their mutability
        // letting m stand for the shallow mutability
        // (S x) -> { m x, S (*x) }
        // (E x) -> { m x, E (*x) }
        if p.to_mir_place().ty(self.mir, self.tcx).ty.is_ref() {
            // Shallow part
            let shallow_permission = match place_mutability(self.mir, &p)? {
                Mutability::Not => PermissionKind::ShallowRead,
                Mutability::Mut => PermissionKind::ShallowExcl,
            };
            let shallow_cap = Capability {
                resource: Resource::Place(p),
                permission: Tagged {
                    data: shallow_permission,
                    tag: c.permission.tag.clone(),
                },
            };

            // Deep part
            let deref_p: Place<'tcx> =
                PlaceImpl::from_mir_place(self.tcx.mk_place_deref(p.to_mir_place()));
            let deep_cap = Capability {
                resource: Resource::Place(deref_p),
                permission: c.permission.clone(),
            };

            let op = FreeOp::Unpack(c.clone());
            let pre = [c.clone()].into();
            let post = [shallow_cap, deep_cap].into();

            return Some(RepackOp { op, pre, post });
        }

        unimplemented!("unhandled unpack: {:?}", p);
    }

    /// Determines which capabilities this pack can pack to
    pub fn valid_packs(&self, c: &Capability<'tcx>) -> Option<RepackOp<'tcx>> {
        let p = match c.resource {
            Resource::Borrow(_) => return None,
            Resource::Place(p) => p,
        };
        let stripped_cap = Capability {
            resource: Resource::Place(p.strip_uppermost(self.tcx)?),
            ..(c.clone())
        };
        let valid_unpack = self.valid_unpacks(&stripped_cap)?;
        Some(RepackOp {
            op: FreeOp::Pack(stripped_cap.clone()),
            pre: valid_unpack.post,
            post: valid_unpack.pre,
        })
    }

    // Returns Less when the set needs a unpack to get closer, and a place to unpack
    // Returns greater when the set needs a pack to get closer, and a place to pack
    fn closest_in_set(
        set: &BTreeSet<Capability<'tcx>>,
        target: &Capability<'tcx>,
    ) -> Option<(Capability<'tcx>, Ordering)> {
        // Measuring a borrow against anything else is 1 if they are equal,
        // and 0 if not.
        // Measuring caps with different permissions is 0.
        // Otherwise, measuring two places gets the number of projections
        // that are the same.
        let measure = |cap: &Capability<'tcx>| {
            if cap.permission != target.permission {
                return 0;
            }
            match (&cap.resource, &target.resource) {
                // place/place case
                (Resource::Place(p0), Resource::Place(p1)) => {
                    let p0 = p0.to_mir_place();
                    let p1 = p1.to_mir_place();
                    if p0.local != p1.local {
                        return 0;
                    };
                    let mut r = 1;
                    for (pi0, pi1) in p0.iter_projections().zip(p1.iter_projections()) {
                        if pi0 == pi1 {
                            r += 1
                        } else {
                            break;
                        }
                    }
                    return r;
                }
                // Any borrow case
                _ => {
                    if cap == target {
                        return 1;
                    } else {
                        return 0;
                    }
                }
            }
        };

        // This last comparison might be backwards
        let mut set = set.iter().collect::<Vec<_>>();
        set.sort_by_key(|k| measure(k));
        let closest_elt = set.iter().next()?;
        return Some((
            (*closest_elt).clone(),
            measure(&closest_elt).cmp(&measure(&target)),
        ));
    }
}
