// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Stacked Borrows / Tree Borrows retag emission helpers for VIR lowering.
//!
//! These helpers emit `Stmt::Retag` at the correct program points:
//! - After `Rvalue::Ref` assignments (Default / TwoPhase)
//! - At function entry for reference-typed parameters (FnEntry)
//! - After reference-to-raw-pointer casts (Raw)

use super::context::FunctionLoweringContext;
use crate::ownership::Place;
use crate::types::RustType;
use crate::vir::{BorrowKind, RetagKind, Rvalue, Stmt as VirStmt};

impl<'a> FunctionLoweringContext<'a> {
    /// Emit a `Rvalue::Ref` assignment followed by a `Stmt::Retag`.
    pub(super) fn emit_ref_and_retag(
        &mut self,
        destination: Place,
        borrow_kind: BorrowKind,
        place: Place,
        retag_kind: RetagKind,
    ) {
        self.emit(VirStmt::Assign {
            place: destination.clone(),
            rvalue: Rvalue::Ref { borrow_kind, place },
        });
        self.emit(VirStmt::Retag {
            kind: retag_kind,
            place: destination,
        });
    }

    /// Emit `FnEntry` retags for reference-typed parameters (Stacked Borrows).
    pub(super) fn emit_fn_entry_retags(&mut self, params: &[(String, RustType)]) {
        for (i, (_name, ty)) in params.iter().enumerate() {
            if matches!(ty, RustType::Reference { .. }) {
                self.emit(VirStmt::Retag {
                    kind: RetagKind::FnEntry,
                    place: Place::Local((i as u32) + 1), // local 0 is return place
                });
            }
        }
    }
}
