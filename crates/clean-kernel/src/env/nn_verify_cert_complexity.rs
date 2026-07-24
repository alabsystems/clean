// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate complexity measurement for NN verification proof terms.
//!
//! This module provides stack-safe structural metrics for certificate
//! expressions used in neural network verification. The measurements track
//! total term size, maximum nesting depth, and the number of distinct constant
//! names referenced by a certificate expression, including embedded ZFC set
//! constructors when present.
//!
//! Part of #3260.

use crate::expr::{stack_safe, Expr, ExprKind};
use crate::name::Name;
use std::collections::HashSet;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CertComplexityMetrics {
    pub(crate) term_size: usize,
    pub(crate) depth: usize,
    pub(crate) unique_constants: usize,
}

#[must_use]
pub(crate) fn cert_term_size(expr: &Expr) -> usize {
    fn cert_term_size_impl(expr: &Expr) -> usize {
        match expr.kind() {
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Const(_, _)
            | ExprKind::Lit(_)
            | ExprKind::SProp
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1 => 1,
            ExprKind::App(f, a) => 1 + cert_term_size(f) + cert_term_size(a),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                1 + cert_term_size(ty) + cert_term_size(body)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                1 + cert_term_size(ty) + cert_term_size(val) + cert_term_size(body)
            }
            ExprKind::Proj(_, _, e)
            | ExprKind::MData(_, e)
            | ExprKind::Squash(e)
            | ExprKind::CubicalPathLam { body: e } => 1 + cert_term_size(e),
            ExprKind::CubicalPath { ty, left, right } => {
                1 + cert_term_size(ty) + cert_term_size(left) + cert_term_size(right)
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                1 + cert_term_size(ty) + cert_term_size(phi) + cert_term_size(base)
            }
            ExprKind::CubicalCoe { ty, r, s, base } => {
                1 + cert_term_size(ty)
                    + cert_term_size(r)
                    + cert_term_size(s)
                    + cert_term_size(base)
            }
            ExprKind::CubicalPathApp { path, arg } => {
                1 + cert_term_size(path) + cert_term_size(arg)
            }
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                1 + cert_term_size(ty)
                    + cert_term_size(phi)
                    + cert_term_size(u)
                    + cert_term_size(base)
            }
            ExprKind::ZFCSet(set_expr) => 1 + zfc_term_size(set_expr),
            ExprKind::ZFCMem { element, set } => 1 + cert_term_size(element) + cert_term_size(set),
            ExprKind::ZFCComprehension { domain, pred } => {
                1 + cert_term_size(domain) + cert_term_size(pred)
            }
        }
    }

    stack_safe(|| cert_term_size_impl(expr))
}

#[must_use]
pub(crate) fn cert_depth(expr: &Expr) -> usize {
    fn cert_depth_impl(expr: &Expr) -> usize {
        match expr.kind() {
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Const(_, _)
            | ExprKind::Lit(_)
            | ExprKind::SProp
            | ExprKind::CubicalInterval
            | ExprKind::CubicalI0
            | ExprKind::CubicalI1 => 1,
            ExprKind::App(f, a) => 1 + cert_depth(f).max(cert_depth(a)),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                1 + cert_depth(ty).max(cert_depth(body))
            }
            ExprKind::Let(_, ty, val, body, _) => {
                1 + cert_depth(ty).max(cert_depth(val)).max(cert_depth(body))
            }
            ExprKind::Proj(_, _, e)
            | ExprKind::MData(_, e)
            | ExprKind::Squash(e)
            | ExprKind::CubicalPathLam { body: e } => 1 + cert_depth(e),
            ExprKind::CubicalPath { ty, left, right } => {
                1 + cert_depth(ty).max(cert_depth(left)).max(cert_depth(right))
            }
            ExprKind::CubicalTransp { ty, phi, base } => {
                1 + cert_depth(ty).max(cert_depth(phi)).max(cert_depth(base))
            }
            ExprKind::CubicalCoe { ty, r, s, base } => {
                1 + cert_depth(ty)
                    .max(cert_depth(r))
                    .max(cert_depth(s))
                    .max(cert_depth(base))
            }
            ExprKind::CubicalPathApp { path, arg } => 1 + cert_depth(path).max(cert_depth(arg)),
            ExprKind::CubicalHComp { ty, phi, u, base } => {
                1 + cert_depth(ty)
                    .max(cert_depth(phi))
                    .max(cert_depth(u))
                    .max(cert_depth(base))
            }
            ExprKind::ZFCSet(set_expr) => 1 + zfc_depth(set_expr),
            ExprKind::ZFCMem { element, set } => 1 + cert_depth(element).max(cert_depth(set)),
            ExprKind::ZFCComprehension { domain, pred } => {
                1 + cert_depth(domain).max(cert_depth(pred))
            }
        }
    }

    stack_safe(|| cert_depth_impl(expr))
}

#[must_use]
pub(crate) fn zfc_term_size(set_expr: &crate::expr::ZFCSetExpr) -> usize {
    fn zfc_term_size_impl(set_expr: &crate::expr::ZFCSetExpr) -> usize {
        match set_expr {
            crate::expr::ZFCSetExpr::Empty | crate::expr::ZFCSetExpr::Infinity => 1,
            crate::expr::ZFCSetExpr::Singleton(e)
            | crate::expr::ZFCSetExpr::Union(e)
            | crate::expr::ZFCSetExpr::PowerSet(e)
            | crate::expr::ZFCSetExpr::Choice(e) => 1 + cert_term_size(e),
            crate::expr::ZFCSetExpr::Pair(a, b) => 1 + cert_term_size(a) + cert_term_size(b),
            crate::expr::ZFCSetExpr::Separation { set, pred }
            | crate::expr::ZFCSetExpr::Replacement { set, func: pred } => {
                1 + cert_term_size(set) + cert_term_size(pred)
            }
        }
    }

    stack_safe(|| zfc_term_size_impl(set_expr))
}

#[must_use]
pub(crate) fn zfc_depth(set_expr: &crate::expr::ZFCSetExpr) -> usize {
    fn zfc_depth_impl(set_expr: &crate::expr::ZFCSetExpr) -> usize {
        match set_expr {
            crate::expr::ZFCSetExpr::Empty | crate::expr::ZFCSetExpr::Infinity => 1,
            crate::expr::ZFCSetExpr::Singleton(e)
            | crate::expr::ZFCSetExpr::Union(e)
            | crate::expr::ZFCSetExpr::PowerSet(e)
            | crate::expr::ZFCSetExpr::Choice(e) => 1 + cert_depth(e),
            crate::expr::ZFCSetExpr::Pair(a, b) => 1 + cert_depth(a).max(cert_depth(b)),
            crate::expr::ZFCSetExpr::Separation { set, pred }
            | crate::expr::ZFCSetExpr::Replacement { set, func: pred } => {
                1 + cert_depth(set).max(cert_depth(pred))
            }
        }
    }

    stack_safe(|| zfc_depth_impl(set_expr))
}

#[must_use]
pub(crate) fn cert_unique_constants(expr: &Expr) -> HashSet<Name> {
    expr.collect_constants()
}

#[must_use]
pub(crate) fn measure_cert_complexity(expr: &Expr) -> CertComplexityMetrics {
    let unique_constants = cert_unique_constants(expr);
    CertComplexityMetrics {
        term_size: cert_term_size(expr),
        depth: cert_depth(expr),
        unique_constants: unique_constants.len(),
    }
}
