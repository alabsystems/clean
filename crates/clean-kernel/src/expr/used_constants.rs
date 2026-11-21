// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The constants an expression uses, walked as a DAG.
//!
//! Lean's `Expr.getUsedConstants` (`src/lean/Lean/Util/FoldConsts.lean`) folds
//! every `.const` node and memoizes on the node pointer, so a heavily shared
//! term costs its number of DISTINCT nodes. [`Expr::collect_constants_into`]
//! walks the same term as a tree, which is exponential in the sharing depth.
//! The `.olean` re-check lanes and the Lean kernel-theory profile ask this
//! question for every checked declaration and every reducer head, so they use
//! this walk instead: an explicit stack (no recursion depth limit) and a set of
//! visited node addresses. A node reached through an `Arc` child keeps its
//! address while the root is borrowed, so the address identifies it.
//!
//! [`UsedConstants::WithProjectionStructures`] additionally reports the
//! structure name of every `Proj` node. Lean's fold skips it, but the kernel
//! must find that structure to type the projection, so an ordering check that
//! wants every constant a check can consult asks for it.

use std::collections::HashSet;

use super::{Expr, ExprKind, Literal};
use crate::name::Name;

/// Which names [`Expr::used_constants_dag`] reports.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum UsedConstants {
    /// Every `Const` head — Lean's `getUsedConstants`.
    ConstantsOnly,
    /// Every `Const` head and the structure name of every `Proj` node.
    WithProjectionStructures,
    /// References in value positions, including projections and all application
    /// arguments. Lambda/let domains and entire Pi expressions are type slots.
    /// Unknown expression forms retain their complete conservative walk.
    ValuePositions,
}

impl Expr {
    /// Insert every constant `self` uses into `out` (see the module docs).
    pub fn used_constants_dag(&self, mode: UsedConstants, out: &mut HashSet<Name>) {
        self.used_constants_dag_with_literals(mode, out, |_| {});
    }

    /// Collect constant references and visit literal leaves in the same DAG walk.
    /// A caller can account for implicit literal dependencies of the Lean format.
    pub fn used_constants_dag_with_literals(
        &self,
        mode: UsedConstants,
        out: &mut HashSet<Name>,
        mut visit_literal: impl FnMut(&Literal),
    ) {
        let mut seen: HashSet<usize> = HashSet::new();
        let mut stack: Vec<&Expr> = vec![self];
        while let Some(e) = stack.pop() {
            if !seen.insert(std::ptr::from_ref(e) as usize) {
                continue;
            }
            match e.kind() {
                ExprKind::Const(name, _) => {
                    out.insert(name.clone());
                }
                ExprKind::BVar(_) | ExprKind::FVar(_) | ExprKind::Sort(_) => {}
                ExprKind::Lit(lit) => visit_literal(lit),
                ExprKind::App(f, a) => {
                    stack.push(f);
                    stack.push(a);
                }
                ExprKind::Pi(..) if mode == UsedConstants::ValuePositions => {}
                ExprKind::Lam(_, _, body) if mode == UsedConstants::ValuePositions => {
                    stack.push(body)
                }
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    stack.push(ty);
                    stack.push(body);
                }
                ExprKind::Let(_, ty, val, body, _) => {
                    if mode != UsedConstants::ValuePositions {
                        stack.push(ty);
                    }
                    stack.push(val);
                    stack.push(body);
                }
                ExprKind::Proj(structure, _, inner) => {
                    if mode != UsedConstants::ConstantsOnly {
                        out.insert(structure.clone());
                    }
                    stack.push(inner);
                }
                ExprKind::MData(_, inner) => stack.push(inner),
                // Clean's non-Lean expression forms never occur in a Lean term;
                // fall back to the tree walk so they are still covered.
                _ => e.collect_constants_into(out),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::BinderInfo;
    use std::sync::Arc;

    fn c(s: &str) -> Expr {
        Expr::const_(Name::from_string(s), vec![])
    }

    fn names(e: &Expr, mode: UsedConstants) -> Vec<String> {
        let mut out = HashSet::new();
        e.used_constants_dag(mode, &mut out);
        let mut v: Vec<String> = out.iter().map(ToString::to_string).collect();
        v.sort();
        v
    }

    #[test]
    fn test_used_constants_dag_collects_every_const_under_binders() {
        let e = Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            Expr::app(c("Nat.succ"), Expr::bvar(0)),
        );
        assert_eq!(names(&e, UsedConstants::ConstantsOnly), ["Nat", "Nat.succ"]);
    }

    #[test]
    fn test_used_constants_dag_projection_structure_only_when_asked() {
        let e = Expr::proj(Name::from_string("Prod"), 0, c("p"));
        assert_eq!(names(&e, UsedConstants::ConstantsOnly), ["p"]);
        assert_eq!(
            names(&e, UsedConstants::WithProjectionStructures),
            ["Prod", "p"]
        );
    }

    /// A term with `2^60` tree paths but 61 distinct nodes: the tree walk would
    /// never finish, the DAG walk visits each shared node once.
    #[test]
    fn test_used_constants_dag_is_linear_in_shared_nodes() {
        let mut e = c("leaf");
        for _ in 0..60 {
            let shared = Arc::new(e);
            e = Expr::from(ExprKind::App(Arc::clone(&shared), shared));
        }
        assert_eq!(names(&e, UsedConstants::ConstantsOnly), ["leaf"]);
    }
}
