// © 2024, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

/// Errors possible during the expiry analusis
#[derive(Debug)]
pub enum ExpiryError {

}

pub type ExpiryResult<T> = Result<T, ExpiryError>;