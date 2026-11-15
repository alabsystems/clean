// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The derived `DecidableEq` instance for a type Clean's built-in prelude has
//! no instance of (`Option`, `Prod`, `Sum`, …), reducing the way Lean's does.
//!
//! Lean's derived instance takes one `DecidableEq` instance per type parameter
//! (`instance [DecidableEq α] : DecidableEq (Option α)`), found where the
//! equation is decided — a local `[DecidableEq Nat]` or a user instance of
//! higher priority included ([`parameter_instances`]). It matches both sides
//! to constructors: different constructors are different without touching a
//! leaf (`none = none` holds whatever the parameter instance does); the same
//! constructor compares the fields left to right, each leaf of a parameter
//! type by REDUCING that parameter's instance on the two leaves, and stops at
//! the first `isFalse`. A leaf whose instance does not reduce leaves the whole
//! comparison stuck, even when the two leaves are the same term (pinned
//! v4.30.0-rc2: `some five = some five` is stuck for `@[irreducible] def
//! five`, `some 1 = some 1` is stuck under `instance (priority := high) i2 :
//! DecidableEq Nat := stuckDec` with `stuckDec` irreducible).
//! [`decide_equation`] does exactly that once both sides reduce to values made
//! of constructors and literals.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, TypeChecker};

use super::super::core::{Goal, ProofState};
use super::plan::Verdict;
use super::{head_is, reducer, resolve_class, Reduction};

/// Most reduction steps one equation may spend reaching constructor values.
const GROUND_BUDGET: u32 = 100_000;

/// Most nested type arguments [`parameter_instances`] inspects.
const CARRIER_DEPTH: u32 = 8;

/// A type parameter's `DecidableEq` instance: the derived instance applies it
/// to every pair of leaves of type `ty`.
#[derive(Clone)]
pub(super) struct ParameterInstance {
    pub(super) ty: Expr,
    pub(super) instance: Expr,
}

/// `true` iff `e` is a proof (its type is a proposition): a proof field is
/// compared by proof irrelevance, never reduced.
fn is_proof(state: &ProofState, goal: &Goal, e: &Expr) -> bool {
    state
        .infer_type(goal, e)
        .and_then(|ty| state.infer_type(goal, &ty))
        .is_ok_and(|sort| {
            matches!(state.whnf(goal, &sort).kind(), ExprKind::Sort(level) if level.is_zero())
        })
}

/// `e` reduced to a literal or to a constructor application whose data fields
/// are themselves reduced (parameters and proof fields kept as they are), or
/// `None` when some part does not reduce.
fn ground_value(
    state: &ProofState,
    goal: &Goal,
    tc: &TypeChecker<'_>,
    e: &Expr,
    budget: &mut u32,
) -> Option<Expr> {
    *budget = budget.checked_sub(1)?;
    let value = tc.whnf(e);
    if matches!(value.kind(), ExprKind::Lit(_)) {
        return Some(value);
    }
    let head = value.get_app_fn();
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    let ctor = state.env().get_constructor(name)?;
    let args = value.get_app_args();
    let params = ctor.num_params as usize;
    if args.len() != params + ctor.num_fields as usize {
        return None;
    }
    let mut reduced: Vec<Expr> = args[..params].iter().map(|arg| (*arg).clone()).collect();
    for field in &args[params..] {
        if is_proof(state, goal, field) {
            reduced.push((*field).clone());
        } else {
            reduced.push(ground_value(state, goal, tc, field, budget)?);
        }
    }
    Some(Expr::apps(head.clone(), reduced))
}

/// How a pair of leaves (or of whole values) compared.
enum Comparison {
    Equal,
    Different,
    /// A parameter instance did not reduce; the payload is where it stopped.
    Stuck(Expr),
}

/// The fixed context of one derived-instance comparison.
struct Walk<'w, 'e> {
    state: &'w ProofState,
    goal: &'w Goal,
    tc: &'w TypeChecker<'e>,
    instances: &'w [ParameterInstance],
}

impl Walk<'_, '_> {
    /// Compare two values the way the derived instance does (see the module
    /// doc).
    fn compare(&self, left: &Expr, right: &Expr, ty: &Expr, budget: &mut u32) -> Comparison {
        let (state, goal) = (self.state, self.goal);
        let Some(rest) = budget.checked_sub(1) else {
            return Comparison::Stuck(left.clone());
        };
        *budget = rest;
        if let Some(parameter) = self
            .instances
            .iter()
            .find(|p| p.ty == *ty || state.is_def_eq(goal, &p.ty, ty))
        {
            let decision = self.tc.whnf(&Expr::apps(
                parameter.instance.clone(),
                [left.clone(), right.clone()],
            ));
            if head_is(&decision, "Decidable.isTrue") {
                return Comparison::Equal;
            }
            if head_is(&decision, "Decidable.isFalse") {
                return Comparison::Different;
            }
            return Comparison::Stuck(decision);
        }
        let (left_head, right_head) = (left.get_app_fn(), right.get_app_fn());
        let (ExprKind::Const(left_ctor, _), ExprKind::Const(right_ctor, _)) =
            (left_head.kind(), right_head.kind())
        else {
            // Literals (or a literal against a constructor spelling of the
            // same value): equality of values.
            return if left == right || state.is_def_eq(goal, left, right) {
                Comparison::Equal
            } else {
                Comparison::Different
            };
        };
        if left_ctor != right_ctor {
            return Comparison::Different;
        }
        let Some(ctor) = state.env().get_constructor(left_ctor) else {
            return Comparison::Stuck(left.clone());
        };
        let params = ctor.num_params as usize;
        let (left_args, right_args) = (left.get_app_args(), right.get_app_args());
        for (field_left, field_right) in left_args.iter().zip(&right_args).skip(params) {
            if is_proof(state, goal, field_left) {
                continue;
            }
            let Ok(field_ty) = state.infer_type(goal, field_left) else {
                return Comparison::Stuck((*field_left).clone());
            };
            match self.compare(field_left, field_right, &field_ty, budget) {
                Comparison::Equal => {}
                other => return other,
            }
        }
        Comparison::Equal
    }
}

/// Decide the equation `prop` (over a type Lean derives `DecidableEq` for,
/// `decide_eq::decidable_type_check`) as its derived instance does, with the
/// type parameters' `instances`, reducing at `reduction`: `Eq.refl` when
/// equal, false when not, stuck when a side does not reduce to constructors
/// and literals or a parameter instance does not reduce.
pub(super) fn decide_equation(
    state: &ProofState,
    goal: &Goal,
    prop: &Expr,
    instances: &[ParameterInstance],
    reduction: Reduction,
) -> Verdict {
    let shown = || crate::error_render::term(prop);
    let Ok((ty, lhs, rhs, levels)) = super::super::equality::match_equality(prop) else {
        return Verdict::Stuck("not an equation".into());
    };
    let tc = reducer(state, goal, reduction);
    let mut budget = GROUND_BUDGET;
    let sides = ground_value(state, goal, &tc, &lhs, &mut budget).zip(ground_value(
        state,
        goal,
        &tc,
        &rhs,
        &mut budget,
    ));
    let Some((left, right)) = sides else {
        return Verdict::Stuck(format!(
            "the derived `DecidableEq` instance of `{}` did not reduce to `isTrue` or \
             `isFalse`: a side does not reduce to constructors and literals",
            shown()
        ));
    };
    let walk = Walk {
        state,
        goal,
        tc: &tc,
        instances,
    };
    match walk.compare(&left, &right, &ty, &mut budget) {
        Comparison::Equal => Verdict::Proved(Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), levels),
            [ty, lhs],
        )),
        Comparison::Different => Verdict::False {
            refutation: None,
            why: format!(
                "the derived `DecidableEq` instance reduced `{}` to `isFalse`",
                shown()
            ),
        },
        Comparison::Stuck(at) => Verdict::Stuck(format!(
            "the derived `DecidableEq` instance of `{}` did not reduce to `isTrue` or \
             `isFalse`; reduction got stuck at `{}`",
            shown(),
            crate::error_render::term(&at)
        )),
    }
}

/// The `DecidableEq` instance of each of `ty`'s type parameters, found in the
/// goal's scope (local instances first, then the global ones by priority),
/// as Lean's derived instance takes them where the equation is decided; a
/// parameter with no instance of its own (`Option Nat` inside `Option (Option
/// Nat)`, whose instance Clean's prelude lacks) is searched inside.
pub(super) fn parameter_instances(
    state: &ProofState,
    goal: &Goal,
    ty: &Expr,
) -> Vec<ParameterInstance> {
    let mut found = Vec::new();
    collect_parameter_instances(state, goal, ty, CARRIER_DEPTH, &mut found);
    found
}

fn collect_parameter_instances(
    state: &ProofState,
    goal: &Goal,
    ty: &Expr,
    fuel: u32,
    found: &mut Vec<ParameterInstance>,
) {
    let Some(fuel) = fuel.checked_sub(1) else {
        return;
    };
    for arg in ty.get_app_args() {
        let Ok(sort) = state.infer_type(goal, arg) else {
            continue;
        };
        let sort = state.whnf(goal, &sort);
        let ExprKind::Sort(level) = sort.kind() else {
            continue;
        };
        let class = Expr::app(
            Expr::const_(Name::from_string("DecidableEq"), vec![level.clone()]),
            arg.clone(),
        );
        match resolve_class(state, goal, &class) {
            Some(instance) => found.push(ParameterInstance {
                ty: arg.clone(),
                instance,
            }),
            None => collect_parameter_instances(state, goal, arg, fuel, found),
        }
    }
}
