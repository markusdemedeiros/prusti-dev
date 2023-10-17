// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{fmt::{Debug, Formatter, Result}, cell::RefCell};

use derive_more::{Deref, DerefMut};
use prusti_rustc_interface::{
    dataflow::fmt::DebugWithContext, index::IndexVec, middle::mir::Local,
};

use crate::{
    free_pcs::{
        engine::FreePlaceCapabilitySummary, CapabilityLocal, CapabilityProjections, RepackOp,
    },
    utils::{PlaceRepacker, Place},
};

use super::CapabilityKind;

pub struct FpcsBound<'tcx>(pub Option<Box<dyn Fn(Place<'tcx>) -> CapabilityKind>>, pub bool);
impl FpcsBound<'_> {
    pub fn empty(expect: bool) -> RefCell<Self> {
        RefCell::new(Self(None, expect))
    }
}

pub struct Fpcs<'a, 'tcx> {
    pub(crate) repacker: PlaceRepacker<'a, 'tcx>,
    pub(crate) bottom: bool,
    pub summary: CapabilitySummary<'tcx>,
    pub repackings: Vec<RepackOp<'tcx>>,
    pub bound: RefCell<FpcsBound<'tcx>>,
}
impl<'a, 'tcx> Fpcs<'a, 'tcx> {
    pub(crate) fn new(repacker: PlaceRepacker<'a, 'tcx>) -> Self {
        let summary = CapabilitySummary::default(repacker.local_count());
        Self {
            repacker,
            bottom: true,
            summary,
            repackings: Vec::new(),
            bound: FpcsBound::empty(false),
        }
    }
    #[tracing::instrument(name = "Fpcs::bound", level = "trace", skip(self), ret)]
    pub(crate) fn bound(&self, place: Place<'tcx>) -> CapabilityKind {
        let bound = self.bound.borrow();
        assert_eq!(bound.1, bound.0.is_some());
        bound.0.as_ref().map(|b| b(place)).unwrap_or(CapabilityKind::Exclusive)
    }
}

impl Clone for Fpcs<'_, '_> {
    fn clone(&self) -> Self {
        let expect_bound = self.bound.borrow().1;
        Self { repacker: self.repacker, bottom: self.bottom, summary: self.summary.clone(), repackings: self.repackings.clone(), bound: FpcsBound::empty(expect_bound) }
    }
}
impl PartialEq for Fpcs<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.bottom == other.bottom
            && self.summary == other.summary
            && self.repackings == other.repackings
    }
}
impl Eq for Fpcs<'_, '_> {}

impl Debug for Fpcs<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.summary.fmt(f)
    }
}
impl<'a, 'tcx> DebugWithContext<FreePlaceCapabilitySummary<'a, 'tcx>> for Fpcs<'a, 'tcx> {
    fn fmt_diff_with(
        &self,
        old: &Self,
        _ctxt: &FreePlaceCapabilitySummary<'a, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> Result {
        // let rp = self.repacker;
        assert_eq!(self.summary.len(), old.summary.len());
        for op in &self.repackings {
            writeln!(f, "{op}")?;
        }
        for (new, old) in self.summary.iter().zip(old.summary.iter()) {
            let changed = match (new, old) {
                (CapabilityLocal::Unallocated, CapabilityLocal::Unallocated) => false,
                (CapabilityLocal::Unallocated, CapabilityLocal::Allocated(a)) => {
                    write!(f, "\u{001f}-{:?}", a.get_local())?;
                    true
                }
                (CapabilityLocal::Allocated(a), CapabilityLocal::Unallocated) => {
                    write!(f, "\u{001f}+{a:?}")?;
                    true
                }
                (CapabilityLocal::Allocated(new), CapabilityLocal::Allocated(old)) => {
                    if new != old {
                        let mut new_set = CapabilityProjections::empty();
                        let mut old_set = CapabilityProjections::empty();
                        for (&p, &nk) in new.iter() {
                            match old.get(&p) {
                                Some(&ok) if nk == ok => (),
                                _ => {
                                    new_set.insert(p, nk);
                                }
                            }
                        }
                        for (&p, &ok) in old.iter() {
                            match new.get(&p) {
                                Some(&nk) if nk == ok => (),
                                _ => {
                                    old_set.insert(p, ok);
                                }
                            }
                        }
                        if !new_set.is_empty() {
                            write!(f, "\u{001f}+{new_set:?}")?
                        }
                        if !old_set.is_empty() {
                            write!(f, "\u{001f}-{old_set:?}")?
                        }
                        true
                    } else {
                        false
                    }
                }
            };
            if changed {
                if f.alternate() {
                    writeln!(f)?;
                } else {
                    write!(f, "\t")?;
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq, Deref, DerefMut)]
/// Generic state of a set of locals
pub struct Summary<T>(IndexVec<Local, T>);

impl<T: Debug> Debug for Summary<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.0.fmt(f)
    }
}

impl<T> Summary<T> {
    pub fn default(local_count: usize) -> Self
    where
        T: Default + Clone,
    {
        Self(IndexVec::from_elem_n(T::default(), local_count))
    }
}

/// The free pcs of all locals
pub type CapabilitySummary<'tcx> = Summary<CapabilityLocal<'tcx>>;
