// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression lowering helpers for borrows, assignments, and casts.

use super::context::FunctionLoweringContext;
use super::ops::lower_cast_kind;
use super::VirLoweringError;
use crate::expr::Expr;
use crate::ownership::Place;
use crate::types::{Mutability, RustType};
use crate::values::BinOp as ExprBinOp;
use crate::vir::{BorrowKind, MutBorrowKind, RetagKind, Rvalue, Stmt as VirStmt};

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn lower_addr_of_expr(
        &mut self,
        destination: Place,
        mutability: Mutability,
        expr: &Expr,
    ) -> Result<(), VirLoweringError> {
        let place = self.lower_place_or_temp(expr)?;
        let borrow_kind = match mutability {
            Mutability::Shared => BorrowKind::Shared,
            Mutability::Mutable => BorrowKind::Mut {
                kind: MutBorrowKind::Default,
            },
        };
        self.emit_ref_and_retag(destination, borrow_kind, place, RetagKind::Default);
        Ok(())
    }

    pub(super) fn lower_assign_expr(
        &mut self,
        destination: Place,
        target: &Expr,
        value: &Expr,
    ) -> Result<(), VirLoweringError> {
        let place = self.lower_place(target)?;
        self.lower_expr_into(place, value, matches!(value, Expr::Block { .. }))?;
        self.assign_unit(destination)
    }

    pub(super) fn lower_assign_op_expr(
        &mut self,
        destination: Place,
        op: ExprBinOp,
        target: &Expr,
        value: &Expr,
    ) -> Result<(), VirLoweringError> {
        let place = match self.lower_place(target) {
            Ok(place) => place,
            Err(_) if self.terminated => return Ok(()),
            Err(err) => return Err(err),
        };
        let rhs = match self.lower_operand(value) {
            Ok(rhs) => rhs,
            Err(_) if self.terminated => return Ok(()),
            Err(err) => return Err(err),
        };
        let lhs = self.place_operand(place.clone())?;
        self.emit(VirStmt::Assign {
            place,
            rvalue: Rvalue::BinaryOp {
                op: super::ops::lower_bin_op(op),
                lhs,
                rhs,
            },
        });
        self.assign_unit(destination)
    }

    pub(super) fn lower_cast_expr(
        &mut self,
        destination: Place,
        expr: &Expr,
        target: &RustType,
    ) -> Result<(), VirLoweringError> {
        let source_ty = self.infer_expr_type(expr)?;
        let operand = self.materialize_operand(expr)?;
        if self.terminated {
            return Ok(());
        }
        let is_ref_to_raw = matches!(&source_ty, RustType::Reference { .. })
            && matches!(target, RustType::RawPtr { .. });
        self.emit(VirStmt::Assign {
            place: destination.clone(),
            rvalue: Rvalue::Cast {
                kind: lower_cast_kind(&source_ty, target),
                operand,
                ty: target.clone(),
            },
        });
        if is_ref_to_raw {
            let raw_mutability = match target {
                RustType::RawPtr { mutability, .. } => *mutability,
                _ => Mutability::Shared,
            };
            self.emit(VirStmt::Retag {
                kind: RetagKind::Raw(raw_mutability),
                place: destination,
            });
        }
        Ok(())
    }
}
