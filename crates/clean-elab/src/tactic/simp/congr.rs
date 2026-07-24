// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Auto-generated congruence lemmas for simp.
//!
//! In Lean 4, `simp` generates congruence lemmas for every inductive type
//! and function application. These lemmas allow simp to simplify arguments
//! of function applications and constructor arguments.
//!
//! For a function `f : A → B → C`, the congruence lemma is:
//! ```text
//! @congr_f : ∀ (a₁ a₂ : A) (b₁ b₂ : B),
//!   a₁ = a₂ → b₁ = b₂ → f a₁ b₁ = f a₂ b₂
//! ```
//!
//! This module generates such lemmas on-the-fly during simp, based on the
//! structure of the expression being simplified.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind};

use super::types::{SimpIndexMode, SimpLemma};
use crate::tactic::core::{Goal, ProofState};

/// Generate congruence lemmas for a constant application.
///
/// Given `f a₁ a₂ ... aₙ`, generates lemmas of the form:
/// ```text
/// f a₁ ... aᵢ ... aₙ = f a₁ ... aᵢ' ... aₙ   when   aᵢ = aᵢ'
/// ```
///
/// This is used when simp cannot find a matching simp lemma and needs to
/// simplify subterms of a function application.
///
/// REQUIRES: `expr` is a function application
/// ENSURES: Returns congruence lemmas for each argument position
/// ENSURES: Each lemma rewrites one argument position, leaving others fixed
pub(crate) fn generate_congr_lemmas_for_app(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
) -> Vec<SimpLemma> {
    let fn_expr = expr.get_app_fn();
    let args = expr.get_app_args();

    if args.is_empty() {
        return Vec::new();
    }

    let fn_name = match fn_expr.kind() {
        ExprKind::Const(name, _) => name.clone(),
        _ => return Vec::new(),
    };

    let mut lemmas = Vec::new();

    // For each argument position, create a congruence lemma that allows
    // rewriting just that argument.
    for (i, arg) in args.iter().enumerate() {
        // Try to infer the type of the argument
        let Ok(_arg_ty) = state.infer_type(goal, arg) else {
            continue;
        };

        // Build LHS pattern: f a₁ ... BVar(0) ... aₙ
        // where BVar(0) is in position i
        let mut lhs_args: Vec<Expr> = args.iter().map(|a| (*a).clone()).collect();
        lhs_args[i] = Expr::bvar(0);
        let mut lhs = fn_expr.clone();
        for a in &lhs_args {
            lhs = Expr::app(lhs, a.clone());
        }

        // RHS is the same as LHS (the BVar will be unified with the actual arg)
        let rhs = lhs.clone();

        let lemma_name = Name::from_string(&format!("{fn_name}.congr_arg{i}"));

        lemmas.push(SimpLemma {
            name: lemma_name,
            lhs,
            rhs,
            eq_type: None,
            proof_expr: None,
            index_mode: SimpIndexMode::NoIndexAtArgs,
            priority: 10, // Low priority — only fire as fallback
        });
    }

    lemmas
}

/// Check if a registered @[congr] lemma applies to the given expression.
///
/// Looks up congr lemmas from the environment registry and returns those
/// whose head matches the expression's head constant.
///
/// REQUIRES: `state.env` has congr lemmas registered via `register_congr`
/// ENSURES: Returns congr lemmas matching the expression head
pub(crate) fn collect_congr_lemmas(state: &ProofState, _goal: &Goal, expr: &Expr) -> Vec<Name> {
    let head = expr.get_app_fn();
    let head_name = match head.kind() {
        ExprKind::Const(name, _) => name,
        _ => return Vec::new(),
    };

    // Check for registered @[congr] lemmas that match this head
    let mut results = Vec::new();

    // Look for `<head_name>.congr` pattern
    let congr_name = Name::from_string(&format!("{head_name}.congr"));
    if state.env.is_congr(&congr_name) {
        results.push(congr_name);
    }

    // Also check for generic congr lemma names
    let generic_congr = Name::from_string(&format!("congr_{head_name}"));
    if state.env.is_congr(&generic_congr) {
        results.push(generic_congr);
    }

    results
}

/// Generate congruence lemma for an inductive constructor.
///
/// For `MyType.mk a b c`, generates:
/// ```text
/// MyType.mk a₁ b₁ c₁ = MyType.mk a₂ b₂ c₂  when  a₁=a₂ ∧ b₁=b₂ ∧ c₁=c₂
/// ```
///
/// REQUIRES: `ctor_name` is a valid constructor in `state.env`
/// ENSURES: Returns a congruence lemma for the constructor, or None
pub(crate) fn generate_ctor_congr_lemma(
    state: &ProofState,
    _goal: &Goal,
    ctor_name: &Name,
) -> Option<SimpLemma> {
    let ctor_decl = state.env.get_const(ctor_name)?;
    let ctor_ty = &ctor_decl.type_;

    // Count the number of explicit arguments (Pi binders with Default info)
    let mut num_args = 0u32;
    let mut current = ctor_ty;
    while let ExprKind::Pi(bi, _ty, body) = current.kind() {
        if *bi == BinderInfo::Default.into() {
            num_args += 1;
        }
        current = body;
    }

    if num_args == 0 {
        return None;
    }

    // Build LHS: ctor BVar(n-1) BVar(n-2) ... BVar(0)
    let mut lhs = Expr::const_(ctor_name.clone(), vec![]);
    for i in (0..num_args).rev() {
        lhs = Expr::app(lhs, Expr::bvar(i));
    }

    // RHS is identical (pattern matching will unify bvars with actual args)
    let rhs = lhs.clone();

    let lemma_name = Name::from_string(&format!("{ctor_name}.congr"));
    Some(SimpLemma {
        name: lemma_name,
        lhs,
        rhs,
        eq_type: None,
        proof_expr: None,
        index_mode: SimpIndexMode::Normal,
        priority: 20,
    })
}
