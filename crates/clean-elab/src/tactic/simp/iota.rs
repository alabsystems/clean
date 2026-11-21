// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! simp's ι step (Lean's `Simp.Config.iota`, on by default and under
//! `simp only`): a recursor — `T.rec`, or a `T.casesOn` Clean's kernel
//! registers as one — applied to a constructor reduces by its rule. Imported
//! `casesOn` definitions are reduced through their actual recursor wrapper.
//!
//! Clean's simp had none: a case split it met on a constructor stayed in
//! place. `simp only [P.beq] at h` on the nested `P`, whose lifted equations
//! keep a `P.casesOn` on the second column (brick B3), left
//! `h : P.casesOn … (P.leaf x) … = true` where Lean's `h` reads `(a == x) =
//! true` (trust-ir `Proofs/PredLatticeProps.lean` `Pred.beq_eq`, block 13).
//! The step is definitional — the kernel's own ι recipe, plus δ/β for an
//! imported `casesOn` wrapper that reaches that recipe — so
//! simp records it without a proof, like its β and η steps.

use clean_kernel::env::ConstantKind;
use clean_kernel::name::NameInner;
use clean_kernel::{BinderInfo, Expr, ExprKind, RecursorArgOrder};

use super::budget::SimpBudget;
use super::expr::proof_matches_rewrite;
use super::proof::mk_congr_arg;
use super::reduce::{beta_reduce, shift_expr};
use super::types::SimpResult;
use crate::tactic::core::{Goal, ProofState};

/// Bound on the β rounds that normalize one reduct.
const BETA_ROUNDS: usize = 64;

/// A proven change to one argument can expose the branch of a complete
/// recursor. Transport the whole application through that change before
/// simplifying its alternatives. A prefix ending just after the major may
/// still have a dependent function type even when the final result is constant.
pub(super) fn reduce_after_argument_rewrite(
    state: &ProofState,
    goal: &Goal,
    original: &Expr,
    index: usize,
    after: &Expr,
    equality: &Expr,
    budget: &SimpBudget,
) -> Option<SimpResult> {
    let head = original.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    if state.env.get_recursor(name).is_none()
        && !matches!(name.inner(), NameInner::Str(_, suffix) if suffix.as_ref() == "casesOn")
    {
        return None;
    }
    let args = original.get_app_args();
    let (previous, rest) = args.split_at(index);
    let (before, remaining) = rest.split_first()?;
    let prefix = Expr::apps(head.clone(), previous.iter().map(|arg| (*arg).clone()));
    let rewritten = Expr::apps(
        Expr::app(prefix.clone(), after.clone()),
        remaining.iter().map(|arg| (*arg).clone()),
    );
    let reduced = reduce_recursor_app(state, goal, &rewritten, budget)?;
    let argument_type = state.infer_type(goal, before).ok()?;
    let context = Expr::lam(
        BinderInfo::Default,
        argument_type,
        Expr::apps(
            Expr::app(shift_expr(&prefix, 1), Expr::bvar(0)),
            remaining.iter().map(|arg| shift_expr(arg, 1)),
        ),
    );
    let proof = mk_congr_arg(state, goal, &context, before, after, equality)?;
    if !proof_matches_rewrite(state, goal, &proof, original, &reduced)
        || !budget.admit(&reduced, "reducing a recursor after rewriting its argument")
    {
        return None;
    }
    Some(SimpResult {
        expr: reduced,
        proof: Some(proof),
    })
}

/// The ι reduct of `expr` when it is a registered recursor applied to a
/// constructor application in its major position, else `None`.
///
/// The rule's right-hand side takes the parameters, motives, minors and the
/// constructor's fields (Lean's `RecursorRule.rhs`, which Clean's
/// `build_cases_on` builds against the recursor-layout twin for `casesOn`);
/// any arguments past the recursor's own follow.
pub(super) fn reduce_recursor_app(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    budget: &SimpBudget,
) -> Option<Expr> {
    reduce_registered_recursor(state, goal, expr)
        .or_else(|| reduce_imported_cases_on(state, goal, expr, budget))
}

fn reduce_imported_cases_on(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    budget: &SimpBudget,
) -> Option<Expr> {
    let ExprKind::Const(name, levels) = expr.get_app_fn().kind() else {
        return None;
    };
    let NameInner::Str(parent, suffix) = name.inner() else {
        return None;
    };
    if suffix.as_ref() != "casesOn" || state.env.get_inductive(parent).is_none() {
        return None;
    }
    let info = state.env.get_const(name)?;
    if !matches!(info.kind, ConstantKind::Definition) || info.level_params.len() != levels.len() {
        return None;
    }
    let value = info.value.as_ref()?;
    // The spelling only selects an imported eliminator candidate. Reduction
    // follows its actual checked body, which must call this family's recursor.
    let mut body = value.strip_mdata();
    while let ExprKind::Lam(_, _, next) = body.kind() {
        body = next.strip_mdata();
    }
    let ExprKind::Const(rec_name, _) = body.get_app_fn().kind() else {
        return None;
    };
    if &state.env.get_recursor(rec_name)?.inductive_name != parent.as_ref() {
        return None;
    }
    let mut applied = value.instantiate_level_params_direct(&info.level_params, levels);
    for argument in expr.get_app_args() {
        applied = Expr::app(applied, argument.clone());
    }
    if !budget.admit_before_zeta(&applied, format_args!("reducing {name}")) {
        return None;
    }
    let reduced = beta_reduce(&applied);
    // An unknown major remains folded. Only a genuine constructor iota step
    // authorizes returning the delta/beta result to the simplifier.
    reduce_registered_recursor(state, goal, &reduced)
}

fn reduce_registered_recursor(state: &ProofState, goal: &Goal, expr: &Expr) -> Option<Expr> {
    let ExprKind::Const(name, levels) = expr.get_app_fn().kind() else {
        return None;
    };
    let rec = state.env.get_recursor(name)?;
    let args = expr.get_app_args();
    let params = rec.num_params as usize;
    let motives = rec.num_motives as usize;
    let minors = rec.num_minors as usize;
    let indices = rec.num_indices as usize;
    let (major_at, minors_from, rest_from) = match rec.arg_order {
        RecursorArgOrder::MajorAfterMinors => {
            let major = params + motives + minors + indices;
            (major, params + motives, major + 1)
        }
        RecursorArgOrder::MajorAfterMotive => {
            let major = params + motives + indices;
            (major, major + 1, major + 1 + minors)
        }
    };
    if args.len() < rest_from.max(major_at + 1) {
        return None;
    }
    // Iota inspects the constructor head of the major, not its surface
    // spelling. For example `n + 1` exposes `Nat.succ n` by kernel WHNF.
    // Only a constructor with a rule below authorizes a reduct; opaque or
    // stuck majors stay folded. Use the caller's goal, including simp's
    // temporary binder context, rather than the proof state's current goal.
    let major = state.whnf(goal, args[major_at]);
    let ExprKind::Const(ctor_name, _) = major.get_app_fn().kind() else {
        return None;
    };
    let rule = rec
        .rules
        .iter()
        .find(|rule| rule.constructor_name == *ctor_name)?;
    let ctor = state.env.get_constructor(ctor_name)?;
    let ctor_args = major.get_app_args();
    let ctor_params = ctor.num_params as usize;
    if ctor_args.len() != ctor_params + rule.num_fields as usize
        || rec.level_params.len() != levels.len()
    {
        return None;
    }
    let mut reduct = rule
        .rhs
        .instantiate_level_params_direct(&rec.level_params, levels);
    let prefix = args[..params + motives]
        .iter()
        .chain(&args[minors_from..minors_from + minors]);
    for arg in prefix.chain(&ctor_args[ctor_params..]) {
        reduct = Expr::app(reduct, (*arg).clone());
    }
    for arg in &args[rest_from..] {
        reduct = Expr::app(reduct, (*arg).clone());
    }
    let mut current = beta_reduce(&reduct);
    for _ in 0..BETA_ROUNDS {
        let next = beta_reduce(&current);
        if next == current {
            return Some(current);
        }
        current = next;
    }
    None
}
