// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt;

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

/// Struct to help us do repacks at the capability level
/// Helper functions for places live in mir_utils; this struct
/// does repacks at the capability level
pub struct Repacker<'mir, 'tcx: 'mir> {
    mir: &'mir Body<'tcx>,
}

impl<'mir, 'tcx: 'mir> Repacker<'mir, 'tcx> {
    pub fn legal_unpacks(&self, c: &Capability<'tcx>) -> Vec<()> {
        todo!();
    }
}
