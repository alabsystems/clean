// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Conversion from kernel Expr/Level/Name to flat format.

use std::collections::HashMap;

use crate::expr::{stack_safe, BinderInfo, Expr, ExprKind, Literal};
use crate::level::Level;
use crate::name::Name;

use super::builder::FlatBuilder;
use super::error::FlatError;
use super::types::{FlatExpr, FlatFlags, FlatLevel};

impl FlatBuilder {
    /// Convert a kernel `Expr` to flat format, adding it to this builder.
    ///
    /// Returns the index of the expression in the flat array.
    /// Uses memoization to avoid duplicating subexpressions.
    ///
    /// # Errors
    /// Returns `FlatError::UnsupportedBigNat` if a Nat literal exceeds u64::MAX.
    pub fn add_kernel_expr(&mut self, expr: &Expr) -> Result<u32, FlatError> {
        // INVARIANT: *const Expr is used as HashMap key for O(1) identity-based
        // memoization. This is sound because all Expr sub-expressions in ExprKind
        // variants (App, Lam, Pi, Let, etc.) are stored behind Arc<Expr>, which
        // heap-allocates and never moves the inner Expr. The memo map lives only
        // for the duration of this call, and the input `expr` reference (plus the
        // Arc refcounts within it) keeps all sub-expression addresses stable.
        // Using content-based Hash would be O(n) per lookup; pointer identity is O(1).
        //
        // CANONICALITY: the pointer memo is a PERF layer only (it skips
        // re-walks of Arc-shared DAGs). The records themselves are appended via
        // the content-dedup `add_expr_dedup`/`add_level_dedup`, so the flat
        // encoding is invariant under Arc-sharing topology: a maximally shared
        // DAG and a fresh unshared tree of the same term produce identical
        // tables (and hence identical `expr_canonical_digest` bytes). The memo
        // can only skip nodes the content dedup would collapse anyway.
        let mut memo: HashMap<*const Expr, u32> = HashMap::new();
        self.add_kernel_expr_memo(expr, &mut memo)
    }

    fn add_kernel_expr_memo(
        &mut self,
        expr: &Expr,
        memo: &mut HashMap<*const Expr, u32>,
    ) -> Result<u32, FlatError> {
        stack_safe(|| self.add_kernel_expr_memo_inner(expr, memo))
    }

    /// Inner implementation of `add_kernel_expr_memo` (called via `stack_safe`).
    ///
    /// Every recursive call goes through `add_kernel_expr_memo` which re-enters
    /// `stack_safe` to prevent stack overflow on deeply nested expressions.
    fn add_kernel_expr_memo_inner(
        &mut self,
        expr: &Expr,
        memo: &mut HashMap<*const Expr, u32>,
    ) -> Result<u32, FlatError> {
        // Check memo first
        let ptr = expr as *const Expr;
        if let Some(&idx) = memo.get(&ptr) {
            return Ok(idx);
        }

        let idx = match &expr.kind {
            ExprKind::BVar(n) => self.add_expr_dedup(FlatExpr::bvar(*n)),

            ExprKind::FVar(fvar_id) => self.add_expr_dedup(FlatExpr::fvar(fvar_id.0)),

            ExprKind::Sort(level) => {
                let level_idx = self.add_kernel_level(level);
                self.add_expr_dedup(FlatExpr::sort(level_idx))
            }

            ExprKind::Const(name, levels) => {
                let name_idx = self.add_kernel_name(name);
                // Multi-level universe polymorphism support (#1162).
                // Convert each Level to a flat level index, then store the list.
                let level_indices: Vec<u32> = levels
                    .iter()
                    .map(|level| self.add_kernel_level(level))
                    .collect();
                let levels_list_idx = self.add_level_list(&level_indices);
                self.add_expr_dedup(FlatExpr::const_ref(name_idx, levels_list_idx))
            }

            ExprKind::App(f, a) => {
                let fn_idx = self.add_kernel_expr_memo(f, memo)?;
                let arg_idx = self.add_kernel_expr_memo(a, memo)?;
                self.add_expr_dedup(FlatExpr::app(fn_idx, arg_idx))
            }

            ExprKind::Lam(bi, ty, body) => {
                let ty_idx = self.add_kernel_expr_memo(ty, memo)?;
                let body_idx = self.add_kernel_expr_memo(body, memo)?;
                self.add_expr_dedup(FlatExpr::lam(binder_info_to_u8(bi.info), ty_idx, body_idx))
            }

            ExprKind::Pi(bi, ty, body) => {
                let ty_idx = self.add_kernel_expr_memo(ty, memo)?;
                let body_idx = self.add_kernel_expr_memo(body, memo)?;
                self.add_expr_dedup(FlatExpr::pi(binder_info_to_u8(bi.info), ty_idx, body_idx))
            }

            ExprKind::Let(_, ty, val, body, _) => {
                let ty_idx = self.add_kernel_expr_memo(ty, memo)?;
                let val_idx = self.add_kernel_expr_memo(val, memo)?;
                let body_idx = self.add_kernel_expr_memo(body, memo)?;
                self.add_expr_dedup(FlatExpr::let_expr(ty_idx, val_idx, body_idx))
            }

            ExprKind::Lit(lit) => match lit {
                Literal::Nat(n) => match n.to_u64() {
                    Some(val) => self.add_expr_dedup(FlatExpr::lit_nat(val)),
                    None => {
                        // BigNat > u64: store the little-endian u64 limbs as a
                        // comma-separated decimal string in the string table and
                        // flag the LitNat as NAT_BIG (#1174). Round-trips exactly
                        // via BigNat::from_limbs on read.
                        let limbs = n
                            .limbs()
                            .iter()
                            .map(|l| l.to_string())
                            .collect::<Vec<_>>()
                            .join(",");
                        let str_idx = self.add_string(&limbs);
                        let mut e = FlatExpr::lit_nat(0);
                        e.data[0..4].copy_from_slice(&str_idx.to_le_bytes());
                        e.flags |= FlatFlags::NAT_BIG.0;
                        self.add_expr_dedup(e)
                    }
                },
                Literal::String(s) => {
                    let str_idx = self.add_string(s);
                    self.add_expr_dedup(FlatExpr::lit_str(str_idx))
                }
            },

            ExprKind::Proj(name, field, e) => {
                let name_idx = self.add_kernel_name(name);
                let expr_idx = self.add_kernel_expr_memo(e, memo)?;
                self.add_expr_dedup(FlatExpr::proj(name_idx, *field as u16, expr_idx))
            }

            // MData is transparent - just store the inner expression
            ExprKind::MData(_, inner) => return self.add_kernel_expr_memo(inner, memo),

            // Mode extensions are not supported in flat format.
            // These require specialized proof modes (cubical, ZFC, classical).
            // We encode as Sort(0) with UNSUPPORTED flag to signal
            // that verification should treat this subtree as opaque.
            ExprKind::SProp
            | ExprKind::Squash(_)
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1
            | ExprKind::CubicalPath { .. }
            | ExprKind::CubicalPathLam { .. }
            | ExprKind::CubicalPathApp { .. }
            | ExprKind::CubicalHComp { .. }
            | ExprKind::CubicalTransp { .. }
            | ExprKind::CubicalCoe { .. }
            | ExprKind::ZFCSet(_)
            | ExprKind::ZFCMem { .. }
            | ExprKind::ZFCComprehension { .. } => {
                // Encode as Sort(0) with UNSUPPORTED flag.
                // Full support would require adding tags for each mode.
                let level_idx = self.add_level_dedup(FlatLevel::zero());
                let mut expr = FlatExpr::sort(level_idx);
                expr.flags |= FlatFlags::UNSUPPORTED.0;
                self.add_expr_dedup(expr)
            }
        };

        memo.insert(ptr, idx);
        Ok(idx)
    }

    /// Convert a kernel `Level` to flat format.
    fn add_kernel_level(&mut self, level: &Level) -> u32 {
        stack_safe(|| self.add_kernel_level_inner(level))
    }

    /// Inner implementation of `add_kernel_level` (called via `stack_safe`).
    ///
    /// Every recursive call goes through `add_kernel_level` which re-enters
    /// `stack_safe` to prevent stack overflow on deeply nested level trees.
    fn add_kernel_level_inner(&mut self, level: &Level) -> u32 {
        match level {
            Level::Zero => self.add_level_dedup(FlatLevel::zero()),
            Level::Succ(inner) => {
                let inner_idx = self.add_kernel_level(inner);
                self.add_level_dedup(FlatLevel::succ(inner_idx))
            }
            Level::Max(l, r) => {
                let left_idx = self.add_kernel_level(l);
                let right_idx = self.add_kernel_level(r);
                self.add_level_dedup(FlatLevel::max(left_idx, right_idx))
            }
            Level::IMax(l, r) => {
                // IMax uses same encoding as Max for now
                let left_idx = self.add_kernel_level(l);
                let right_idx = self.add_kernel_level(r);
                let mut level = FlatLevel::max(left_idx, right_idx);
                level.tag = FlatLevel::TAG_IMAX;
                self.add_level_dedup(level)
            }
            Level::Param(name) => {
                let name_idx = self.add_kernel_name(name);
                self.add_level_dedup(FlatLevel::param(name_idx))
            }
        }
    }

    /// Convert a kernel `Name` to a string index.
    fn add_kernel_name(&mut self, name: &Name) -> u32 {
        let s = name.to_string();
        self.add_name(&s)
    }
}

/// Convert BinderInfo to u8 for flat format.
fn binder_info_to_u8(bi: BinderInfo) -> u8 {
    match bi {
        BinderInfo::Default => 0,
        BinderInfo::Implicit => 1,
        BinderInfo::StrictImplicit => 2,
        BinderInfo::InstImplicit => 3,
    }
}
