// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof term construction helpers for superposition reconstruction.
//!
//! Contains free functions and impl methods for building kernel proof terms:
//! - `abstract_at_rewrite_site`: position-aware abstraction (for superposition)
//! - `abstract_over_expr`: abstract over ALL occurrences of target (for demodulation)
//! - `mk_eq_refl`: build `@Eq.refl.{u} α a`
//! - Proposition builders: literal_to_prop, clause_to_prop
//! - Motive construction: build_motive, build_motive_positional, mk_eq_subst

use std::sync::Arc;

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use crate::superposition::{Clause, Literal};

use super::types::ReconstructionResult;
use super::SuperpositionReconstructor;

/// Build `@Eq.refl.{u} α a`.
pub(super) fn mk_eq_refl(u: &Level, ty: &Expr, val: &Expr) -> Expr {
    crate::bridge::eq_proof_builders::mk_eq_refl(u, ty, val)
}

/// Position-aware abstraction: only abstract over `target` at positions where
/// `orig` and `rewritten` differ. At positions where they are identical (even
/// if the subtree equals `target`), the original is preserved unchanged.
///
/// Used for superposition motive construction where only one specific
/// occurrence of `lhs` was rewritten to `rhs`. Without position awareness,
/// `abstract_over_expr` replaces ALL occurrences, producing an incorrect motive
/// when `lhs` appears multiple times in the clause.
pub(super) fn abstract_at_rewrite_site(
    orig: &Expr,
    rewritten: &Expr,
    target: &Expr,
    depth: u32,
) -> Expr {
    crate::bridge::stack_safe(|| {
        // If orig and rewritten are identical, no rewrite happened at or below this node.
        // Return orig as-is, even if it contains `target` as a subtree.
        if orig == rewritten {
            return orig.clone();
        }

        // If orig equals target and rewritten differs, this IS the rewrite site.
        if orig == target {
            return Expr::bvar(depth);
        }

        // Structure differs but orig isn't target — recurse into matching structure.
        match (orig.kind(), rewritten.kind()) {
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => Expr::app(
                abstract_at_rewrite_site(f1, f2, target, depth),
                abstract_at_rewrite_site(a1, a2, target, depth),
            ),
            (ExprKind::Lam(bi, ty1, body1), ExprKind::Lam(_, ty2, body2)) => Expr::lam(
                *bi,
                abstract_at_rewrite_site(ty1, ty2, target, depth),
                abstract_at_rewrite_site(body1, body2, target, depth + 1),
            ),
            (ExprKind::Pi(bi, ty1, body1), ExprKind::Pi(_, ty2, body2)) => Expr::pi(
                *bi,
                abstract_at_rewrite_site(ty1, ty2, target, depth),
                abstract_at_rewrite_site(body1, body2, target, depth + 1),
            ),
            (ExprKind::Let(name, ty1, val1, body1, nd), ExprKind::Let(_, ty2, val2, body2, _)) => {
                Expr::let_named(
                    name.clone(),
                    abstract_at_rewrite_site(ty1, ty2, target, depth),
                    abstract_at_rewrite_site(val1, val2, target, depth),
                    abstract_at_rewrite_site(body1, body2, target, depth + 1),
                    *nd,
                )
            }
            _ => {
                // Structural mismatch — fallback to all-occurrences abstraction.
                // This shouldn't happen in well-formed superposition traces.
                abstract_over_expr(orig, target, depth)
            }
        }
    })
}

/// Abstract over all occurrences of `target` in `expr`, replacing them
/// with `BVar(depth)`. Correctly increments depth under binders to
/// maintain de Bruijn indexing.
///
/// Protected by `stacker::maybe_grow` since Expr trees from SMT proofs
/// can be arbitrarily deep (hundreds of nested applications).
pub(super) fn abstract_over_expr(expr: &Expr, target: &Expr, depth: u32) -> Expr {
    stacker::maybe_grow(32 * 1024, 1024 * 1024, || {
        if expr == target {
            return Expr::bvar(depth);
        }
        match expr.kind() {
            ExprKind::App(f, a) => Expr::app(
                abstract_over_expr(f, target, depth),
                abstract_over_expr(a, target, depth),
            ),
            ExprKind::Lam(bi, ty, body) => Expr::lam(
                *bi,
                abstract_over_expr(ty, target, depth),
                abstract_over_expr(body, target, depth + 1),
            ),
            ExprKind::Pi(bi, ty, body) => Expr::pi(
                *bi,
                abstract_over_expr(ty, target, depth),
                abstract_over_expr(body, target, depth + 1),
            ),
            ExprKind::Let(name, ty, val, body, non_dep) => Expr::let_named(
                name.clone(),
                abstract_over_expr(ty, target, depth),
                abstract_over_expr(val, target, depth),
                abstract_over_expr(body, target, depth + 1),
                *non_dep,
            ),
            ExprKind::Proj(name, idx, inner) => {
                Expr::proj(name.clone(), *idx, abstract_over_expr(inner, target, depth))
            }
            ExprKind::MData(md, inner) => {
                Expr::mdata(md.clone(), abstract_over_expr(inner, target, depth))
            }
            ExprKind::Squash(inner) => Expr::from_kind(ExprKind::Squash(Arc::new(
                abstract_over_expr(inner, target, depth),
            ))),
            _ => expr.clone(),
        }
    })
}

/// Extract disjuncts from a right-associative Or chain.
///
/// `P` → `[P]`
/// `Or P Q` → `[P, Q]`
/// `Or P (Or Q R)` → `[P, Q, R]`
///
/// Non-Or expressions are treated as single-element disjunctions.
/// Used by `reconstruct_goal` to decompose multi-clause Or-goals.
pub(super) fn extract_or_disjuncts(expr: &Expr) -> Vec<Expr> {
    crate::bridge::stack_safe(|| {
        if let ExprKind::App(app_or_p, q) = expr.kind() {
            if let ExprKind::App(or_const, p) = app_or_p.kind() {
                if let ExprKind::Const(name, levels) = or_const.kind() {
                    if *name == Name::from_string("Or") && levels.is_empty() {
                        let mut result = vec![p.as_ref().clone()];
                        result.extend(extract_or_disjuncts(q));
                        return result;
                    }
                }
            }
        }
        vec![expr.clone()]
    })
}

/// Extract the antecedent and consequent from an Implies (non-dependent Pi) goal.
///
/// Returns `Some((P, Q))` when `expr` is `Pi (x : P) Q` where Q does not
/// reference `x` (BVar(0) is free in Q). Returns `None` for dependent Pi types
/// or non-Pi expressions.
pub(super) fn extract_implies_components(expr: &Expr) -> Option<(Expr, Expr)> {
    if let ExprKind::Pi(_, domain, body) = expr.kind() {
        // Check that the body doesn't reference BVar(0) — non-dependent Pi = arrow type
        if !body.has_loose_bvar(0) {
            return Some((domain.as_ref().clone(), body.as_ref().clone()));
        }
    }
    None
}

/// Extract the components of an Iff expression.
///
/// Returns `Some((P, Q))` when `expr` is `@Iff P Q`. Returns `None` for
/// non-Iff expressions. Used by `reconstruct_goal` to detect Iff goals
/// and dispatch to the Iff.intro proof strategy.
pub(super) fn extract_iff_components(expr: &Expr) -> Option<(Expr, Expr)> {
    if let ExprKind::App(iff_p, q) = expr.kind() {
        if let ExprKind::App(iff_const, p) = iff_p.kind() {
            if let ExprKind::Const(name, levels) = iff_const.kind() {
                if *name == Name::from_string("Iff") && levels.is_empty() {
                    return Some((p.as_ref().clone(), q.as_ref().clone()));
                }
            }
        }
    }
    None
}

/// Build ¬P = P → False.
pub(super) fn mk_negation(p: &Expr) -> Expr {
    Expr::pi(
        BinderInfo::Default,
        p.clone(),
        Expr::const_(Name::from_string("False"), vec![]),
    )
}

/// Lift free de Bruijn variables in `expr` by `amount`.
///
/// Delegates to the kernel's `Expr::lift` which uses `ExprFolderOpt`
/// for sharing-preserving traversal with O(1) metadata guards. This
/// replaces ~30 LOC of manual match arms that missed Cubical/ZFC
/// extension variants. (#2141)
pub(super) fn lift_bvars(expr: &Expr, amount: u32) -> Expr {
    expr.lift(amount)
}

impl<'a> SuperpositionReconstructor<'a> {
    /// Convert a literal to its kernel proposition Expr.
    ///
    /// Positive literal `l = r` → `@Eq.{u} α l r`
    /// Negative literal `l ≠ r` → `Not (@Eq.{u} α l r)`
    pub(super) fn literal_to_prop(&self, lit: &Literal) -> ReconstructionResult<Expr> {
        let lhs_expr = self.symbol_map.term_to_expr(&lit.lhs)?;
        let rhs_expr = self.symbol_map.term_to_expr(&lit.rhs)?;
        let eq_type = self.symbol_map.term_type(&lit.lhs)?;
        let u = self.sort_level_of_type(&eq_type)?;

        let eq_prop = Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("Eq"), vec![u]), eq_type),
                lhs_expr,
            ),
            rhs_expr,
        );

        if lit.positive {
            Ok(eq_prop)
        } else {
            Ok(Expr::app(
                Expr::const_(Name::from_string("Not"), vec![]),
                eq_prop,
            ))
        }
    }

    /// Convert a clause to its kernel proposition Expr.
    ///
    /// Empty clause → `False`
    /// Single literal → literal proposition
    /// Multiple literals → right-associative `Or` chain
    pub(super) fn clause_to_prop(&self, clause: &Clause) -> ReconstructionResult<Expr> {
        if clause.literals.is_empty() {
            return Ok(Expr::const_(Name::from_string("False"), vec![]));
        }

        let mut props: Vec<Expr> = clause
            .literals
            .iter()
            .map(|lit| self.literal_to_prop(lit))
            .collect::<Result<_, _>>()?;

        // Build right-associative disjunction: l1 ∨ (l2 ∨ (... ∨ ln))
        // Safety: props is non-empty (checked by is_empty guard above)
        let mut result = props
            .pop()
            .expect("invariant: non-empty props after is_empty check");
        while let Some(prop) = props.pop() {
            result = Expr::app(
                Expr::app(Expr::const_(Name::from_string("Or"), vec![]), prop),
                result,
            );
        }

        Ok(result)
    }

    /// Build the Eq.subst motive by abstracting over ALL occurrences of the
    /// rewritten subterm. Suitable for demodulation (rewrites all positions).
    ///
    /// Given a clause proposition `P(l)` where `l` is the rewritten subterm,
    /// produces `fun (x : α) => P(x)` — a lambda that represents the
    /// property being transported by the equality.
    pub(super) fn build_motive(
        &self,
        clause_prop: &Expr,
        rewritten_subterm: &Expr,
        subterm_type: &Expr,
    ) -> Expr {
        let motive_body = abstract_over_expr(clause_prop, rewritten_subterm, 0);
        Expr::lam(BinderInfo::Default, subterm_type.clone(), motive_body)
    }

    /// Build a position-aware motive by diffing original and result propositions.
    ///
    /// Only abstracts over `rewritten_subterm` at positions where `orig_prop`
    /// and `result_prop` actually differ, preserving other occurrences of the
    /// subterm unchanged. Use this for superposition (single-position rewrite).
    /// For demodulation (all-positions rewrite), use `build_motive` instead.
    pub(super) fn build_motive_positional(
        &self,
        orig_prop: &Expr,
        result_prop: &Expr,
        rewritten_subterm: &Expr,
        subterm_type: &Expr,
    ) -> Expr {
        let motive_body = abstract_at_rewrite_site(orig_prop, result_prop, rewritten_subterm, 0);
        Expr::lam(BinderInfo::Default, subterm_type.clone(), motive_body)
    }

    /// Build `@Eq.symm.{u} α a b h`.
    ///
    /// Eq.symm signature:
    /// ```text
    /// @Eq.symm.{u} {α : Sort u} {a b : α} (h : Eq a b) : Eq b a
    /// ```
    pub(super) fn mk_eq_symm(
        &self,
        eq_type: &Expr,
        a: &Expr,
        b: &Expr,
        h: &Expr,
    ) -> ReconstructionResult<Expr> {
        let u = self.sort_level_of_type(eq_type)?;
        Ok(crate::bridge::eq_proof_builders::mk_eq_symm(
            &u, eq_type, a, b, h,
        ))
    }

    /// Build `@Eq.trans.{u} α a b c h₁ h₂`.
    pub(super) fn mk_eq_trans(
        &self,
        eq_type: &Expr,
        a: &Expr,
        b: &Expr,
        c: &Expr,
        h1: &Expr,
        h2: &Expr,
    ) -> ReconstructionResult<Expr> {
        let u = self.sort_level_of_type(eq_type)?;
        Ok(crate::bridge::eq_proof_builders::mk_eq_trans(
            &u, eq_type, a, b, c, h1, h2,
        ))
    }

    /// Build `@Eq.subst.{u} α motive a b h m`.
    ///
    /// Note: Unlike Lean 4's `Eq.subst.{u1, u2}`, the clean kernel
    /// fixes the motive codomain to `Prop`, so only 1 universe param.
    pub(super) fn mk_eq_subst(
        &self,
        eq_type: &Expr,
        motive: &Expr,
        a: &Expr,
        b: &Expr,
        h: &Expr,
        m: &Expr,
    ) -> ReconstructionResult<Expr> {
        let u = self.sort_level_of_type(eq_type)?;
        Ok(crate::bridge::eq_proof_builders::mk_eq_subst(
            &u, eq_type, motive, a, b, h, m,
        ))
    }
}
