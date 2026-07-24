// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::context::FunctionLoweringContext;
use super::type_helpers::autoderef_place_to_expected_inner;
use super::VirLoweringError;
use crate::expr::Expr;
use crate::ownership::Place;
use crate::types::{Mutability, RustType};
use crate::vir::{BorrowKind, MutBorrowKind, Operand, RetagKind};

impl<'a> FunctionLoweringContext<'a> {
    pub(super) fn try_materialize_autoderef_reference_operand(
        &mut self,
        expr: &Expr,
        expected_ty: &RustType,
    ) -> Result<Option<Operand>, VirLoweringError> {
        let Some((place, borrow_kind)) = self.autoderef_reference_place(expr, expected_ty)? else {
            return Ok(None);
        };
        let temp = self.alloc_local(None, expected_ty.clone(), Mutability::Mutable);
        self.emit_ref_and_retag(Place::Local(temp), borrow_kind, place, RetagKind::Default);
        Ok(Some(self.place_operand(Place::Local(temp))?))
    }

    pub(super) fn try_lower_autoderef_reference_expr(
        &mut self,
        destination: Place,
        expr: &Expr,
        target_ty: &RustType,
    ) -> Result<bool, VirLoweringError> {
        let Some((place, borrow_kind)) = self.autoderef_reference_place(expr, target_ty)? else {
            return Ok(false);
        };
        self.emit_ref_and_retag(destination, borrow_kind, place, RetagKind::Default);
        Ok(true)
    }

    fn autoderef_reference_place(
        &mut self,
        expr: &Expr,
        target_ty: &RustType,
    ) -> Result<Option<(Place, BorrowKind)>, VirLoweringError> {
        let RustType::Reference {
            mutability, inner, ..
        } = target_ty
        else {
            return Ok(None);
        };
        let place = match autoderef_place_to_expected_inner(self, expr, inner) {
            Ok(place) => place,
            Err(VirLoweringError::Unsupported {
                context: "method receiver",
                ..
            }) => {
                return Ok(None);
            }
            Err(err) => return Err(err),
        };
        let borrow_kind = match mutability {
            Mutability::Shared => BorrowKind::Shared,
            Mutability::Mutable => BorrowKind::Mut {
                kind: MutBorrowKind::Default,
            },
        };
        Ok(Some((place, borrow_kind)))
    }
}
