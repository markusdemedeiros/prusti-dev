// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]
use core::cell::*;
use itertools::{
    Either::{Left, Right},
    Itertools,
};
use prusti_interface::{
    environment::{
        borrowck::facts::{BorrowckFacts, Loan, PointType},
        mir_analyses::{
            allocation::{compute_definitely_allocated, DefinitelyAllocatedAnalysisResult},
            initialization::{compute_definitely_initialized, DefinitelyInitializedAnalysisResult},
        },
        mir_body::borrowck::facts::{
            LocationTable,
            RichLocation::{Mid, Start},
        },
        polonius_info::PoloniusInfo,
        Environment, Procedure,
    },
    utils::{expand_one_level, is_prefix},
    PrustiError,
};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{
        mir,
        mir::{
            AggregateKind::*, Operand, Operand::*, Rvalue::*, StatementKind::*, Terminator,
            TerminatorKind, TerminatorKind::*,
        },
        ty::TyCtxt,
    },
};
use std::fmt::Debug;

/// Wrapper type for all errors
pub type EncodingResult<A> = Result<A, PrustiError>;

pub fn preprocess_mir<'tcx>(mir: &mut mir::Body<'tcx>) {
    // Simple filter on MIR statements
    // Ensure all statements are in model 1.
    for (bb, bbdata) in mir.basic_blocks_mut().iter_enumerated_mut() {
        for (st_no, st) in bbdata.statements.iter_mut().enumerate() {
            let l = mir::Location {
                block: bb,
                statement_index: st_no,
            };

            match st.kind {
                StorageLive(_)
                | StorageDead(_)
                | Assign(box (_, Use(_)))
                | Nop
                | Assign(box (_, Aggregate(box Adt(_, _, _, _, _), _)))
                | Assign(box (
                    _,
                    Ref(
                        _,
                        mir::BorrowKind::Mut {
                            allow_two_phase_borrow: _,
                        },
                        _,
                    ),
                )) => (),
                FakeRead(_) | AscribeUserType(_, _) => {
                    st.make_nop();
                }
                _ => {
                    println!("{:?}", st.kind);
                    panic!()
                }
            }
        }

        let term = bbdata.terminator_mut();
        match term.kind {
            Goto { target: _ }
            | SwitchInt {
                discr: _,
                switch_ty: _,
                targets: _,
            }
            | Return => (),
            FalseUnwind {
                real_target: target,
                unwind: _,
            }
            | Assert {
                cond: _,
                expected: _,
                msg: _,
                target,
                cleanup: _,
            } => {
                term.kind = Goto { target };
            }
            _ => {
                println!("{:?}", term.kind);
                panic!()
            }
        }
    }
}
