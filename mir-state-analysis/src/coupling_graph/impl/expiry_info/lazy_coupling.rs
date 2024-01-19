// © 2024, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::coupling_graph::CgContext;

use super::{graph::Eg, control_flow::ControlFlowFlag};
use prusti_rustc_interface::middle::mir::Location;

#[derive(Debug, Clone, Eq)]
pub(crate) enum LazyCoupling {
    Done(Location, Eg),
    Lazy(Vec<(ControlFlowFlag, Eg)>)
}

impl PartialEq for LazyCoupling {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Done(l0, g0), Self::Done(l1, g1)) => (l0 == l1) && (g0 == g1),
            (Self::Lazy(l), Self::Lazy(r)) => {
                l.iter().all(|v| r.contains(v)) &&
                r.iter().all(|v| l.contains(v)) 
            }
            _ => false,
        }
    }
}

impl LazyCoupling {
    /// Lazily join two LazyCouplings together,
    /// The coupling must not be shot yet
    pub(crate) fn append(&mut self, mut other: Self) {
        match (self, other) {
            (Self::Lazy(l), Self::Lazy(mut r)) => {
                todo!(); // Check to see if there's a lazy case already?
                // l.append(&mut r)
            }
            _ => {
                panic!("one-shot lazy join given Done value");
            }
        }
    }

    /// Lazily add a single branch to a LazyCoupling
    pub(crate) fn add_case(&mut self, mut other: (ControlFlowFlag, Eg)) {
        self.append(LazyCoupling::Lazy(vec![other]));
    }

    /// Identity for join 
    pub(crate) fn empty() -> Self {
        Self::Lazy(vec![])
    }

    /// Ensure that the lazy join is completed, or attempt to complete it
    /// Calling this asserts that nothing else will be added to this join point afterwards, which should be the case
    /// if we are correcrtly combining state together (never joining with prior work)
    pub(crate) fn shoot<'a, 'tcx>(&mut self, cgx: &'a CgContext<'a, 'tcx>) {
        if let (Self::Lazy(v)) = self {
            let v = std::mem::take(v);
            assert!(ControlFlowFlag::join_is_complete(v.iter().map(|x| &x.0).collect::<_>(), cgx));
            assert!(v.len() > 0);
            let location = Location { block: v[0].0.to, statement_index: 0 };
            *self = Self::Done(location, Eg::couple(v));
        }
    }

    pub(crate) fn set_location(&mut self, l: Location) {
        match &mut *self {
            LazyCoupling::Done(l1, _) => *l1 = l,
            LazyCoupling::Lazy(_) => panic!("cannot set location on lazy join"),
        }
    }

    /// Ensures we only ever read shot values
    pub(crate) fn read(&mut self) -> (Location, &mut Eg) {
        match self {
            Self::Lazy(_) => panic!("tried to read an unevaluated lazy coupling"),
            Self::Done(l, v) => (*l, &mut (*v))
        }

    }

    pub(crate) fn pretty(&self) -> String {
        match self {
            LazyCoupling::Done(l, g) => format!("EG@{:?}:\n{}", l, g.pretty()),
            LazyCoupling::Lazy(v) => {
                let mut r  = "".to_string();
                for (c, g) in v.iter() {
                   r = format!("{}\n{:?}: {:?}", r, c, g.pretty()).to_string();
                }
                return r.to_string();
            }
        }
    }
}