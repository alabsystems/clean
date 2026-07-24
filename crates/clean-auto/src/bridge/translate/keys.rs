// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId};

/// Key for hashing expressions (avoiding Arc comparison issues).
///
/// Includes universe levels in `Const` and `BinderInfo` in `Lam`/`Pi` so that
/// expressions differing only in these fields get distinct keys. Without this,
/// `@Eq.{0}` and `@Eq.{1}` would collide, and implicit vs explicit binders
/// would be conflated. (#2109)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ExprKey {
    BVar(u32),
    FVar(FVarId),
    Const(Name, Vec<Level>),
    App(Box<ExprKey>, Box<ExprKey>),
    Lam(BinderInfo, Box<ExprKey>, Box<ExprKey>),
    Pi(BinderInfo, Box<ExprKey>, Box<ExprKey>),
    Lit(LitKey),
}

impl ExprKey {
    /// Convert an expression to a hashable key (static version).
    pub(crate) fn from_expr(expr: &Expr) -> Option<ExprKey> {
        crate::bridge::stack_safe(|| match expr.kind() {
            ExprKind::BVar(idx) => Some(ExprKey::BVar(*idx)),
            ExprKind::FVar(fvar_id) => Some(ExprKey::FVar(*fvar_id)),
            ExprKind::Const(name, levels) => Some(ExprKey::Const(name.clone(), levels.to_vec())),
            ExprKind::App(f, a) => {
                let f_key = Self::from_expr(f)?;
                let a_key = Self::from_expr(a)?;
                Some(ExprKey::App(Box::new(f_key), Box::new(a_key)))
            }
            ExprKind::Lam(bi, ty, body) => {
                let ty_key = Self::from_expr(ty)?;
                let body_key = Self::from_expr(body)?;
                Some(ExprKey::Lam(bi.info, Box::new(ty_key), Box::new(body_key)))
            }
            ExprKind::Pi(bi, ty, body) => {
                let ty_key = Self::from_expr(ty)?;
                let body_key = Self::from_expr(body)?;
                Some(ExprKey::Pi(bi.info, Box::new(ty_key), Box::new(body_key)))
            }
            ExprKind::Lit(lit) => match &lit {
                clean_kernel::expr::Literal::Nat(n) => {
                    n.to_u64().map(|v| ExprKey::Lit(LitKey::Nat(v)))
                }
                clean_kernel::expr::Literal::String(s) => {
                    Some(ExprKey::Lit(LitKey::String(s.to_string())))
                }
            },
            // MData is transparent metadata - unwrap to inner expression (#2279)
            ExprKind::MData(_, inner) => Self::from_expr(inner),
            _ => None, // Don't cache Sort, Let, Proj
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum LitKey {
    Nat(u64),
    String(String),
}

/// Unfold nested `App` nodes into `(head, [arg0, arg1, ...])`.
///
/// Shared utility used by trigger extraction and goal-directed scoring.
pub(crate) fn collect_app_args(expr: &Expr) -> (Expr, Vec<Expr>) {
    let mut args = Vec::new();
    // Strip MData before decomposing - MData(md, App(f, a)) should be
    // decomposed as App(f, a) (#2279)
    let mut current = expr.strip_mdata().clone();

    while let ExprKind::App(func, arg) = current.kind() {
        args.push((**arg).clone());
        current = (**func).clone();
    }

    args.reverse();
    (current, args)
}
