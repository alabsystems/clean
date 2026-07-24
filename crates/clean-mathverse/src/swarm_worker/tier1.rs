// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The tier-1 obligation filter: an honest, conservative gate that admits only
//! goals the in-repo hammer has any realistic chance of discharging.
//!
//! The filter is deliberately strict — a false ACCEPT just wastes a hammer
//! timeout, while a false REJECT only declines a goal we would almost certainly
//! have missed anyway. It rejects on the side of caution.
//!
//! A goal is **accepted** iff ALL hold:
//!
//! * Its TYPE is `Prop` — i.e. `inferType(goal)` whnf-reduces to `Sort 0`. This
//!   is the kernel's own verdict that the goal is a proposition (a thing that
//!   can have a proof), not a type / value.
//! * It is CLOSED at the top level: no top-level `∀` / `Π`. The hammer's
//!   propositional and equational lanes target quantifier-free goals; a
//!   leading binder is firmly tier-2.
//! * It is SHALLOW: structural depth within [`MAX_DEPTH`].
//! * It carries no obvious universe-polymorphism (`Sort`/`Const` mentioning a
//!   level `Param`) and no metavariable / free-variable leakage.
//!
//! Inference failures are rejected (`NotTypeable`) — fail closed, never admit a
//! goal we cannot even type.

use std::collections::HashSet;

use clean_kernel::{Environment, Expr, ExprKind, Level, Name, TypeChecker};

/// Maximum structural depth a tier-1 goal may have. Goals deeper than this are
/// rejected as out of scope for the propositional / equational hammer.
pub(crate) const MAX_DEPTH: u32 = 20;

/// The classification of a candidate goal by the tier-1 filter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tier1Outcome {
    /// The goal is in scope for the hammer.
    Accept,
    /// The goal's type could not be inferred (fail closed).
    NotTypeable,
    /// The goal is not a proposition (its type is not `Prop`).
    NotAProp,
    /// The goal has a top-level `∀` / `Π` binder.
    HasTopLevelPi,
    /// The goal is structurally deeper than [`MAX_DEPTH`].
    TooDeep,
    /// The goal mentions a universe-level `Param` (universe-polymorphic).
    UniversePolymorphic,
    /// The goal contains a metavariable or free variable (not a closed term).
    NotClosed,
}

/// Classify `goal` against `env` for tier-1 admission.
///
/// `env` is the environment the goal's constants resolve against; it is used
/// purely to infer the goal's type (the Prop check). The function never mutates
/// `env`.
#[must_use]
pub fn tier1_classify(env: &Environment, goal: &Expr) -> Tier1Outcome {
    // Cheap structural rejections first (no kernel work).
    if goal.is_pi() {
        return Tier1Outcome::HasTopLevelPi;
    }
    if let Some(reason) = structural_reject(goal) {
        return reason;
    }

    // Prop check: the goal is a proposition iff its type reduces to `Sort 0`.
    let tc = TypeChecker::new(env);
    let Ok(ty) = tc.infer_type(goal) else {
        return Tier1Outcome::NotTypeable;
    };
    if !tc.whnf(&ty).is_prop() {
        return Tier1Outcome::NotAProp;
    }

    Tier1Outcome::Accept
}

/// Walk the goal once, rejecting on the first structural disqualifier:
/// excessive depth, a universe `Param`, or a metavariable / free variable.
/// Returns `None` if the goal is structurally admissible.
///
/// Shared with the tier-2 filter, which runs the same walk over a `∀`-body
/// once it has been opened with fresh free variables (so the body's own FVars
/// are expected and must NOT be rejected as `NotClosed`). See
/// [`structural_reject_allowing_fvars_and_params`] for that variant.
pub(super) fn structural_reject(goal: &Expr) -> Option<Tier1Outcome> {
    structural_reject_inner(goal, false, None)
}

/// Like [`structural_reject`] but tolerates both the peeled `∀` binders' free
/// variables and the universe `Param`s in `allowed_params` (the type binders the
/// tier-3 path peeled — `{G : Type u}` introduces `u`). A `Sort` / `Const` whose
/// level mentions a
/// param OUTSIDE that set is still rejected as [`Tier1Outcome::UniversePolymorphic`];
/// an undeclared universe variable must never slip into a graduated theorem.
/// Every other disqualifier — depth, free-variable leakage (modulo the peeled
/// binders) — is reported identically.
pub(super) fn structural_reject_allowing_fvars_and_params(
    goal: &Expr,
    allowed_params: &HashSet<Name>,
) -> Option<Tier1Outcome> {
    structural_reject_inner(goal, true, Some(allowed_params))
}

/// Whether `level` mentions a `Param` NOT present in `allowed`. With
/// `allowed = None` ANY param is disallowed (the monomorphic tier-1/tier-2
/// contract); with `allowed = Some(set)` only params outside `set` are
/// disallowed (the tier-3 universe-polymorphic path's declared params).
fn level_has_unallowed_param(level: &Level, allowed: Option<&HashSet<Name>>) -> bool {
    match allowed {
        None => level.has_params(),
        Some(set) => {
            if !level.has_params() {
                return false;
            }
            let mut params = Vec::new();
            level.collect_params(&mut params);
            params.iter().any(|p| !set.contains(p))
        }
    }
}

fn structural_reject_inner(
    goal: &Expr,
    allow_fvars: bool,
    allowed_params: Option<&HashSet<Name>>,
) -> Option<Tier1Outcome> {
    let mut worst: Option<Tier1Outcome> = None;
    let mut consider = |outcome: Tier1Outcome| {
        // Preserve the first-seen rejection; depth is the lowest priority so a
        // genuine universe/closedness problem is reported in preference.
        if worst.is_none() || matches!(worst, Some(Tier1Outcome::TooDeep)) {
            worst = Some(outcome);
        }
    };

    // Explicit stack walk (de Bruijn-agnostic — we only inspect node kinds and
    // levels, never bind). Depth is the maximum nesting reached.
    let mut stack: Vec<(&Expr, u32)> = vec![(goal, 0)];
    while let Some((expr, depth)) = stack.pop() {
        if depth > MAX_DEPTH {
            consider(Tier1Outcome::TooDeep);
            continue;
        }
        match expr.kind() {
            ExprKind::Sort(level) if level_has_unallowed_param(level, allowed_params) => {
                consider(Tier1Outcome::UniversePolymorphic);
            }
            ExprKind::Const(_, levels)
                if levels
                    .iter()
                    .any(|l| level_has_unallowed_param(l, allowed_params)) =>
            {
                consider(Tier1Outcome::UniversePolymorphic);
            }
            ExprKind::FVar(_) if !allow_fvars => {
                consider(Tier1Outcome::NotClosed);
            }
            ExprKind::App(f, a) => {
                stack.push((f, depth + 1));
                stack.push((a, depth + 1));
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push((ty, depth + 1));
                stack.push((body, depth + 1));
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push((ty, depth + 1));
                stack.push((val, depth + 1));
                stack.push((body, depth + 1));
            }
            ExprKind::Proj(_, _, inner) => stack.push((inner, depth + 1)),
            ExprKind::MData(_, inner) => stack.push((inner, depth)),
            // BVar / Lit and the impredicative/extension kinds carry no level
            // params or sub-terms we admit; leave them be.
            _ => {}
        }
    }

    worst
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Expr, Level, Name};

    fn prelude() -> Environment {
        Environment::try_with_prelude_for_import().expect("prelude must build")
    }

    /// `@Eq.{1} Nat 0 0` — a closed proposition.
    fn refl_goal() -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
                    Expr::const_str("Nat"),
                ),
                Expr::nat_lit(0),
            ),
            Expr::nat_lit(0),
        )
    }

    #[test]
    fn test_tier1_accepts_closed_reflexive_equality() {
        assert_eq!(
            tier1_classify(&prelude(), &refl_goal()),
            Tier1Outcome::Accept
        );
    }

    #[test]
    fn test_tier1_rejects_top_level_pi() {
        // `∀ (p : Prop), p → p` — a Prop, but leads with a binder.
        let goal = Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        );
        assert_eq!(
            tier1_classify(&prelude(), &goal),
            Tier1Outcome::HasTopLevelPi
        );
    }

    #[test]
    fn test_tier1_rejects_non_prop_value() {
        // `Nat` is a type (`Sort 1`), not a proposition.
        assert_eq!(
            tier1_classify(&prelude(), &Expr::const_str("Nat")),
            Tier1Outcome::NotAProp
        );
    }

    #[test]
    fn test_tier1_rejects_untypeable_goal() {
        // A const that does not exist in the environment cannot be typed.
        let goal = Expr::const_str("SwarmWorker.NoSuchConstant");
        assert_eq!(tier1_classify(&prelude(), &goal), Tier1Outcome::NotTypeable);
    }

    #[test]
    fn test_tier1_rejects_free_variable() {
        // An fvar leak is not a closed term.
        let goal = Expr::fvar(clean_kernel::FVarId::new(7));
        assert_eq!(tier1_classify(&prelude(), &goal), Tier1Outcome::NotClosed);
    }

    #[test]
    fn test_tier1_rejects_universe_polymorphic_const() {
        // A const instantiated at a universe `Param` is universe-polymorphic.
        let goal = Expr::const_(
            Name::from_string("Eq"),
            vec![Level::param(Name::from_string("u"))],
        );
        assert_eq!(
            tier1_classify(&prelude(), &goal),
            Tier1Outcome::UniversePolymorphic
        );
    }
}
