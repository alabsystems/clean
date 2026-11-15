// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What `native_decide` refuses before anything is evaluated.
//!
//! Lean's `native_decide` (`elabNativeDecideCore` → `Lean.Meta.nativeEqTrue`)
//! synthesizes `Decidable p` (local instances first, at every sub-goal),
//! refuses `decide p` when it mentions a free variable, then COMPILES
//! `decide p` and runs the code. Clean evaluates in the kernel instead
//! (DECISIONS R127, R109), which sees through code Lean's compiler would not
//! produce, and computes a reference body where Lean runs an implementation.
//! Measured on pinned v4.30.0-rc2 (2026-10-22):
//!
//! * `[Decidable (1 = 1)] ⊢ 1 = 1`, `[DecidableEq Nat] ⊢ ¬ (1 = 2)`,
//!   `(inst : ∀ n, Decidable (n = 1)) ⊢ 1 = 1 := by native_decide`: "Cannot
//!   native decide proposition with free variables" (the local instance is
//!   chosen first);
//! * `noncomputable def nc := 5; nc = 5 := by native_decide`: "failed to
//!   compile definition … depends on 'nc', which is 'noncomputable'";
//! * `axiom c : Nat; (fun _ => 1) c = 1 := by native_decide`: "`c` not
//!   supported by code generator" (`Classical.choice` likewise), while an
//!   axiom the code generator erases (a proof, a type) is no obstacle;
//! * `@[implemented_by impl] def ref (n) := n` with `impl n := n + 1`:
//!   `ref 1 = 1 := by native_decide` is evaluated FALSE (Lean runs `impl`)
//!   though the kernel computes `ref 1` to `1`.
//!
//! So the first three are refused with Lean's messages, and any reach of an
//! `@[implemented_by]` declaration by name: Clean evaluates no implementation,
//! so its verdict could only disagree with Lean's.

use std::collections::HashSet;

use clean_kernel::env::ConstantKind;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, ExprVisitor, FVarId, LevelVec};

use super::super::core::{Goal, ProofState, TacticError};
use super::plan::Plan;
use crate::unify::MetaState;

const TACTIC: &str = "native_decide";

/// Most constants the code-closure walk visits before it refuses.
const CLOSURE_LIMIT: usize = 200_000;

/// Every constant `expr` mentions.
fn constants(expr: &Expr, into: &mut Vec<Name>) {
    struct Collect<'v>(&'v mut Vec<Name>);
    impl ExprVisitor for Collect<'_> {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_const(&mut self, name: &Name, _levels: &LevelVec) {
            self.0.push(name.clone());
        }
    }
    Collect(into).visit_expr(expr);
}

/// Whether `expr` mentions a local of the goal: a free variable that is
/// neither a metavariable nor one of the `Bool` binders a stand-in opened
/// (those are bound in `decide p`).
fn mentions_goal_local(expr: &Expr, opened: &[FVarId]) -> bool {
    struct Find<'o> {
        opened: &'o [FVarId],
        found: bool,
    }
    impl ExprVisitor for Find<'_> {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_fvar(&mut self, id: FVarId) {
            if MetaState::from_fvar(id).is_none() && !self.opened.contains(&id) {
                self.found = true;
            }
        }
    }
    if !expr.has_fvar_quick() {
        return false;
    }
    let mut find = Find {
        opened,
        found: false,
    };
    find.visit_expr(expr);
    find.found
}

/// The refusal Lean's `native_decide` gives (or Clean's, by name) before any
/// evaluation, or `None`.
///
/// REQUIRES: `target` passed `preprocess_prop_to_decide`; `instance` is the
/// goal's `Decidable target` instance when one resolved, and `stand_in` the
/// stand-in plan otherwise.
pub(super) fn refusal(
    state: &ProofState,
    goal: &Goal,
    target: &Expr,
    instance: Option<&Expr>,
    stand_in: Option<&Plan>,
) -> Option<TacticError> {
    let mut instances: Vec<&Expr> = instance.into_iter().collect();
    let mut opened = Vec::new();
    if let Some(plan) = stand_in {
        let (more, bound) = plan.instances();
        instances.extend(more);
        opened = bound;
    }
    if let Some(local) = instances
        .iter()
        .find(|instance| mentions_goal_local(instance, &opened))
    {
        let decided = Expr::apps(
            Expr::const_(Name::from_string("Decidable.decide"), vec![]),
            [target.clone(), (*local).clone()],
        );
        return Some(TacticError::InvalidTarget {
            tactic: TACTIC.into(),
            detail: format!(
                "Tactic `{TACTIC}` failed: Cannot native decide proposition with free \
                 variables:\n  {}",
                crate::error_render::term(&decided)
            ),
        });
    }
    code_refusal(state, goal, target, &instances)
}

/// Whether Lean's code generator erases the axiom `name` of type `ty` rather
/// than compiling a reference to it: a proof (its type is a proposition), a
/// type former (its telescope ends in a sort), a quotient primitive, or a
/// primitive Clean's kernel evaluates natively (Lean implements those).
fn erased_or_builtin(state: &ProofState, goal: &Goal, name: &Name, ty: &Expr) -> bool {
    let env = state.env();
    if env.get_quot(name).is_some()
        || env.get_native_reducer(name).is_some()
        || env.get_inductive(name).is_some()
        || env.get_constructor(name).is_some()
        || env.get_recursor(name).is_some()
    {
        return true;
    }
    let mut codomain = ty;
    while let ExprKind::Pi(_, _, body) = codomain.kind() {
        codomain = body.as_ref();
    }
    if matches!(codomain.kind(), ExprKind::Sort(_)) {
        return true;
    }
    state.infer_type(goal, ty).is_ok_and(
        |sort| matches!(state.whnf(goal, &sort).kind(), ExprKind::Sort(level) if level.is_zero()),
    )
}

/// Walk the code `decide target` would run — definitions' values, never
/// theorems' — for a `noncomputable` declaration, an axiom Lean's code
/// generator would have to call, or an `@[implemented_by]` declaration.
fn code_refusal(
    state: &ProofState,
    goal: &Goal,
    target: &Expr,
    instances: &[&Expr],
) -> Option<TacticError> {
    let env = state.env();
    let mut pending = Vec::new();
    constants(target, &mut pending);
    for instance in instances {
        constants(instance, &mut pending);
    }
    let mut seen: HashSet<Name> = HashSet::new();
    while let Some(name) = pending.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        if seen.len() > CLOSURE_LIMIT {
            return Some(TacticError::InvalidTarget {
                tactic: TACTIC.into(),
                detail: format!(
                    "Tactic `{TACTIC}` failed: the code it would run reaches more than \
                     {CLOSURE_LIMIT} declarations, so Clean cannot check it compiles"
                ),
            });
        }
        if env.is_noncomputable(&name) {
            return Some(TacticError::InvalidTarget {
                tactic: TACTIC.into(),
                detail: format!(
                    "Tactic `{TACTIC}` failed. Error: failed to compile definition, consider \
                     marking it as 'noncomputable' because it depends on '{name}', which is \
                     'noncomputable'"
                ),
            });
        }
        if let Some(implementation) = env.get_implemented_by(&name) {
            return Some(TacticError::InvalidTarget {
                tactic: TACTIC.into(),
                detail: format!(
                    "Tactic `{TACTIC}` failed: `{name}` is `@[implemented_by {implementation}]`, \
                     so Lean's compiled evaluation runs `{implementation}`; Clean evaluates no \
                     implementation and refuses rather than decide by `{name}`'s own body"
                ),
            });
        }
        let Some(info) = env.get_const(&name) else {
            continue;
        };
        match info.kind {
            ConstantKind::Axiom if !erased_or_builtin(state, goal, &name, &info.type_) => {
                return Some(TacticError::InvalidTarget {
                    tactic: TACTIC.into(),
                    detail: format!(
                        "Tactic `{TACTIC}` failed. Error: `{name}` not supported by code \
                         generator; consider marking definition as `noncomputable`"
                    ),
                });
            }
            ConstantKind::Definition => {
                if let Some(value) = &info.value {
                    constants(value, &mut pending);
                }
            }
            ConstantKind::Axiom | ConstantKind::Theorem | ConstantKind::Opaque => {}
        }
    }
    None
}
