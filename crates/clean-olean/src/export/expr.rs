// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression and literal serialization.

use super::OleanExporter;
use crate::error::OleanResult;
use crate::expr::expr_tags;
use clean_kernel::expr::{BinderInfo, Expr, ExprKind, Literal};
use clean_kernel::level::Level;

impl OleanExporter {
    // =========================================================================
    // Expression Serialization
    // =========================================================================

    /// Convert BinderInfo to u8 for serialization
    pub(super) fn binder_info_to_u8(info: BinderInfo) -> u8 {
        match info {
            BinderInfo::Default => 0,
            BinderInfo::Implicit => 1,
            BinderInfo::StrictImplicit => 2,
            BinderInfo::InstImplicit => 3,
        }
    }

    /// Write an Expr object and return its pointer value
    ///
    /// Expr is an inductive type with constructors:
    /// - bvar (tag 0, scalar de Bruijn index)
    /// - fvar (tag 1, 1 field: fvarId)
    /// - mvar (tag 2, 1 field: mvarId)
    /// - sort (tag 3, 1 field: level)
    /// - const (tag 4, 2 fields: name, levels)
    /// - app (tag 5, 2 fields: fn, arg)
    /// - lam (tag 6, 3 fields: binderName, binderType, body + binderInfo scalar)
    /// - forallE (tag 7, 3 fields: binderName, binderType, body + binderInfo scalar)
    /// - letE (tag 8, 4 fields: declName, type, value, body + nondep scalar)
    /// - lit (tag 9, 1 field: literal)
    /// - mdata (tag 10, 2 fields: data, expr)
    /// - proj (tag 11, 2 fields: typeName, struct + idx scalar)
    ///
    /// # ENSURES
    /// - Returns Ok(pointer) for use in parent objects.
    /// - Returns Err(UnsupportedBigNat) if a Nat literal exceeds u64::MAX.
    /// - BVar with index 0 is encoded as scalar 0 (pointer value 1).
    pub(crate) fn write_expr(&mut self, expr: &Expr) -> OleanResult<u64> {
        match expr.kind() {
            ExprKind::BVar(idx) => {
                // BVar is encoded as a scalar
                Ok(Self::scalar_ptr(*idx as u64))
            }
            ExprKind::FVar(fvar_id) => {
                // FVarId is a Name under the hood
                let name_offset = self.write_name(&format!("_fvar_{}", fvar_id.as_u64()));
                let name_ptr = self.offset_to_ptr(name_offset);
                self.align8();
                let offset = self.current_offset();
                self.write_header(expr_tags::FVAR, 1, 0);
                self.write_u64(name_ptr);
                Ok(self.offset_to_ptr(offset))
            }
            ExprKind::Sort(level) => {
                let level_ptr = self.write_level(level);
                self.align8();
                let offset = self.current_offset();
                self.write_header(expr_tags::SORT, 1, 0);
                self.write_u64(level_ptr);
                Ok(self.offset_to_ptr(offset))
            }
            ExprKind::Const(name, levels) => {
                let name_offset = self.write_kernel_name(name);
                let name_ptr = self.offset_to_ptr(name_offset);
                // Write levels as List Level
                let levels_ptr = self.write_level_list(levels);
                self.align8();
                let offset = self.current_offset();
                self.write_header(expr_tags::CONST, 2, 0);
                self.write_u64(name_ptr);
                self.write_u64(levels_ptr);
                Ok(self.offset_to_ptr(offset))
            }
            ExprKind::App(func, arg) => {
                let func_ptr = self.write_expr(func)?;
                let arg_ptr = self.write_expr(arg)?;
                self.align8();
                let offset = self.current_offset();
                self.write_header(expr_tags::APP, 2, 0);
                self.write_u64(func_ptr);
                self.write_u64(arg_ptr);
                Ok(self.offset_to_ptr(offset))
            }
            ExprKind::Lam(binder_info, binder_type, body) => {
                // Lambda: binderName (anonymous), binderType, body
                let name_ptr = Self::scalar_ptr(0); // Name.anonymous
                let type_ptr = self.write_expr(binder_type)?;
                let body_ptr = self.write_expr(body)?;
                self.align8();
                let offset = self.current_offset();
                self.write_header(expr_tags::LAM, 3, 0);
                self.write_u64(name_ptr);
                self.write_u64(type_ptr);
                self.write_u64(body_ptr);
                // BinderInfo as scalar byte
                self.data.push(Self::binder_info_to_u8(binder_info.info));
                self.align8();
                Ok(self.offset_to_ptr(offset))
            }
            ExprKind::Pi(binder_info, binder_type, body) => {
                let name_ptr = Self::scalar_ptr(0); // Name.anonymous
                let type_ptr = self.write_expr(binder_type)?;
                let body_ptr = self.write_expr(body)?;
                self.align8();
                let offset = self.current_offset();
                self.write_header(expr_tags::FORALL_E, 3, 0);
                self.write_u64(name_ptr);
                self.write_u64(type_ptr);
                self.write_u64(body_ptr);
                self.data.push(Self::binder_info_to_u8(binder_info.info));
                self.align8();
                Ok(self.offset_to_ptr(offset))
            }
            ExprKind::Let(let_name, let_type, let_value, body, nondep) => {
                let name_offset = self.write_kernel_name(let_name);
                let name_ptr = self.base_addr + name_offset as u64;
                let type_ptr = self.write_expr(let_type)?;
                let value_ptr = self.write_expr(let_value)?;
                let body_ptr = self.write_expr(body)?;
                self.align8();
                let offset = self.current_offset();
                self.write_header(expr_tags::LET_E, 4, 0);
                self.write_u64(name_ptr);
                self.write_u64(type_ptr);
                self.write_u64(value_ptr);
                self.write_u64(body_ptr);
                self.data.push(if *nondep { 1 } else { 0 });
                self.align8();
                Ok(self.offset_to_ptr(offset))
            }
            ExprKind::Lit(lit) => {
                let lit_ptr = self.write_literal(lit)?;
                self.align8();
                let offset = self.current_offset();
                self.write_header(expr_tags::LIT, 1, 0);
                self.write_u64(lit_ptr);
                Ok(self.offset_to_ptr(offset))
            }
            ExprKind::Proj(type_name, idx, struct_expr) => {
                let name_offset = self.write_kernel_name(type_name);
                let name_ptr = self.offset_to_ptr(name_offset);
                let struct_ptr = self.write_expr(struct_expr)?;
                self.align8();
                let offset = self.current_offset();
                self.write_header(expr_tags::PROJ, 2, 0);
                self.write_u64(name_ptr);
                self.write_u64(struct_ptr);
                // idx as scalar after pointer fields
                self.write_u64(Self::scalar_ptr(*idx as u64));
                Ok(self.offset_to_ptr(offset))
            }
            ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                // MData/Squash are transparent - write the inner expression
                self.write_expr(inner)
            }
            // Extended mode expressions (SProp, Cubical, HoTT, etc.) are not
            // supported in .olean export. These should not appear in normal
            // Lean 4 .olean files. Encode as Sort(0) = Prop as fallback.
            _ => {
                // Unsupported expression type - encode as Prop
                self.align8();
                let offset = self.current_offset();
                self.write_header(expr_tags::SORT, 1, 0);
                self.write_u64(Self::scalar_ptr(0)); // Level.zero
                Ok(self.offset_to_ptr(offset))
            }
        }
    }

    /// Write a List Level and return its pointer
    pub(super) fn write_level_list(&mut self, levels: &[Level]) -> u64 {
        // List nil = scalar 0
        let mut list_ptr = Self::scalar_ptr(0);

        // Build list in reverse order
        for level in levels.iter().rev() {
            let level_ptr = self.write_level(level);
            self.align8();
            let cons_offset = self.current_offset();
            self.write_header(1, 2, 0); // cons tag
            self.write_u64(level_ptr);
            self.write_u64(list_ptr);
            list_ptr = self.offset_to_ptr(cons_offset);
        }

        list_ptr
    }

    /// Write a Literal and return its pointer
    ///
    /// Returns `OleanError::UnsupportedBigNat` if a Nat literal exceeds u64::MAX.
    pub(super) fn write_literal(&mut self, lit: &Literal) -> OleanResult<u64> {
        match lit {
            Literal::Nat(n) => {
                // Literal.natVal (tag 0, 1 scalar field)
                let val = n
                    .to_u64()
                    .ok_or(crate::error::OleanError::UnsupportedBigNat)?;
                self.align8();
                let offset = self.current_offset();
                self.write_header(0, 0, 0);
                self.write_u64(val);
                Ok(self.offset_to_ptr(offset))
            }
            Literal::String(s) => {
                // Literal.strVal (tag 1, 1 field: string)
                let str_offset = self.write_string(s);
                let str_ptr = self.offset_to_ptr(str_offset);
                self.align8();
                let offset = self.current_offset();
                self.write_header(1, 1, 0);
                self.write_u64(str_ptr);
                Ok(self.offset_to_ptr(offset))
            }
        }
    }
}
