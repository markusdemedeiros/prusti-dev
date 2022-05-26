// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use serde::{Serialize, Serializer};
use std::marker::PhantomData;

pub struct PCSState<'mir, 'tcx: 'mir> {
    pub(super) _value: i32,
    pub(super) phantom1: PhantomData<&'mir i32>,
    pub(super) phantom2: PhantomData<&'tcx i32>,
}

impl<'mir, 'tcx: 'mir> Serialize for PCSState<'mir, 'tcx> {
    fn serialize<S>(&self, _serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        todo!()
    }
}
