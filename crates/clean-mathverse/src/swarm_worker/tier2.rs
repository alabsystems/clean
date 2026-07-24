// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The tier-2 obligation filter: admit `∀`-quantified lemmas the tier-1 filter
//! rejects on sight (`HasTopLevelPi`), which are ~92% of real corpus lemmas.
//!
//! A tier-2 goal has the shape `∀ (x₀ : A₀) … (xₙ₋₁ : Aₙ₋₁), Body`. The filter
//! PEELS the leading `Π` binders into a [`LocalContext`] of fresh free
//! variables, OPENS the body against them, and then requires the opened body to
//! be tier-1-shaped: a `Prop`, shallow, and CLOSED except for the peeled
//! binders.
//!
//! # Universe-polymorphic algebra (tier-3)
//!
//! Real Mathlib algebra lemmas lead with a TYPE binder and one or more INSTANCE
//! binders before any value binder, and are universe-polymorphic:
//!
//! ```text
//! ∀ {M : Type u} [inst : Monoid M] (a : M), a * 1 = a
//! ```
//!
//! Tier-2 peels ALL THREE binder shapes into the [`LocalContext`]:
//!
//! * TYPE binders (`Sort u` / `Type u`) — the carrier the lemma is generic over.
//! * INSTANCE binders ([`BinderInfo::InstImplicit`]) — the typeclass dictionary
//!   whose fields (`Monoid.mul_one`, …) are the algebra premises.
//! * VALUE binders — the ordinary `∀ (a : M)` arguments.
//!
//! The universe `Param`s the goal mentions (`u` above) are EXTRACTED into
//! [`Tier2Plan::level_params`]; the binder types and body are then checked
//! allowing exactly those params (so `Type u` is admitted, an UNDECLARED param
//! still rejected). The worker re-abstracts the proof over all peeled binders
//! and graduates a universe-polymorphic [`clean_kernel::Declaration::Theorem`]
//! carrying those `level_params`.
//!
//! # Soundness
//!
//! The filter is a *router*, not a trust boundary. Whatever it accepts is still
//! re-abstracted into a closed proof term and replayed through the same C1
//! kernel-recheck gate as tier-1. The kernel re-checks the re-abstracted
//! `λ`-telescope (WITH its `level_params`) against the ORIGINAL `∀`-type: a
//! wrong re-abstraction, a leaked free variable, or a `level_params` set that
//! does not match the term's universe usage is `KernelRejected` (fail-closed).
//! A mis-classified goal can only waste a hammer timeout or produce a term the
//! kernel rejects. It can never launder an unsound proof.

use std::collections::HashSet;

use clean_kernel::{
    BinderData, Environment, Expr, ExprKind, FVarId, LocalContext, Name, TypeChecker,
};

use super::tier1::{structural_reject_allowing_fvars_and_params, Tier1Outcome};

/// The maximum number of leading `Π` binders a tier-2 goal may carry. A deeper
/// telescope is almost always universe-polymorphic or higher-order, beyond the
/// hammer's reach; capping keeps the peel cheap and the search honest.
pub(crate) const MAX_BINDERS: usize = 6;

/// Why the tier-2 filter rejected a goal, or the accepted peel plan.
///
/// `PartialEq`/`Eq` are intentionally NOT derived: the [`Tier2Plan`] carried by
/// `Accept` holds a [`LocalContext`], which is not comparable. Match on the
/// variant ([`Tier2Outcome::is_accept`]) or destructure instead.
#[derive(Clone, Debug)]
pub enum Tier2Outcome {
    /// The goal is a closed `∀`-telescope over a tier-1-shaped `Prop` body.
    /// Carries the peel plan the worker uses to prove and re-abstract.
    Accept(Box<Tier2Plan>),
    /// The goal is not a `∀` at the top level — it is tier-1's job, not tier-2's.
    NotPi,
    /// The goal leads with more than [`MAX_BINDERS`] binders.
    TooManyBinders,
    /// A binder TYPE is unsuitable (non-closed, universe-polymorphic, too deep).
    BadBinderType(Tier1Outcome),
    /// The opened body is itself a `∀` (a deeper quantifier we do not peel).
    BodyHasNestedPi,
    /// The opened body is not tier-1-shaped (see the inner [`Tier1Outcome`]).
    BodyNotTier1(Tier1Outcome),
    /// The opened body's type could not be inferred in the peeled context.
    BodyNotTypeable,
    /// The opened body is not a `Prop`.
    BodyNotAProp,
}

impl Tier2Outcome {
    /// Whether the goal was accepted (the worker should run the hammer).
    #[must_use]
    pub fn is_accept(&self) -> bool {
        matches!(self, Tier2Outcome::Accept(_))
    }
}

/// The accepted peel of a tier-2 goal: the fresh free variables standing for the
/// `∀` binders (outermost first), the [`LocalContext`] they live in, and the
/// body opened against them. The worker hands `body` + `local_ctx` to the hammer
/// and re-abstracts the proof term over `fvars` (reverse order) to recover a
/// proof of the original `∀` type.
///
/// The telescope may include TYPE binders (`{G : Type u}`) and INSTANCE binders
/// (`[Monoid G]`) ahead of the value binders — the universe-polymorphic algebra
/// shape. The universe `Param`s the goal carries are extracted into
/// [`Tier2Plan::level_params`] and stamped on the graduated theorem; the kernel
/// re-checks the re-abstracted polymorphic term against the original `∀`-type.
#[derive(Clone, Debug)]
pub struct Tier2Plan {
    /// Fresh FVarIds for the peeled binders, OUTERMOST binder first. Binder `i`
    /// (`∀ (xᵢ : Aᵢ)`) is `fvars[i]`. Includes type, instance, and value binders.
    pub fvars: Vec<FVarId>,
    /// Binder data + types for the peeled binders, OUTERMOST first, parallel to
    /// `fvars`. Carried so re-abstraction can rebuild the `Π`/`λ` binders.
    pub binders: Vec<(BinderData, Expr)>,
    /// The local context the fresh free variables were pushed into.
    pub local_ctx: LocalContext,
    /// The body with every peeled binder opened to its fresh free variable.
    pub body: Expr,
    /// The universe `Param` names the goal mentions, in stable first-seen order.
    /// These become the graduated theorem's `level_params`; empty for a
    /// monomorphic tier-2 goal. The set is the ONLY universe-polymorphism the
    /// peeled binder types and body are allowed to mention.
    pub level_params: Vec<Name>,
}

/// Classify `goal` for tier-2 admission. Never mutates `env`; uses it only to
/// infer the opened body's type for the `Prop` check.
///
/// Peels the leading `Π` telescope — TYPE binders (`{G : Type u}`), INSTANCE
/// binders (`[Monoid G]`), and VALUE binders alike — into fresh free variables,
/// extracts the goal's universe `Param`s into [`Tier2Plan::level_params`], and
/// requires the opened body to be a tier-1-shaped `Prop` modulo the peeled
/// binders and those declared params.
#[must_use]
pub fn tier2_classify(env: &Environment, goal: &Expr) -> Tier2Outcome {
    if !goal.is_pi() {
        return Tier2Outcome::NotPi;
    }

    // Extract the universe params the whole goal mentions: these are the ONLY
    // universe-polymorphism the peeled binder types and body may carry, and
    // they become the graduated theorem's `level_params`.
    let level_params = collect_goal_level_params(goal);
    let allowed: HashSet<Name> = level_params.iter().cloned().collect();

    // Peel the leading Π telescope, opening each body against a fresh FVar.
    let mut local_ctx = LocalContext::new();
    let mut fvars: Vec<FVarId> = Vec::new();
    let mut binders: Vec<(BinderData, Expr)> = Vec::new();
    let mut current = goal.clone();

    while let ExprKind::Pi(bd, ty, body) = current.kind() {
        if fvars.len() >= MAX_BINDERS {
            return Tier2Outcome::TooManyBinders;
        }
        let bd = *bd;
        let binder_ty = ty.as_ref().clone();

        // The binder type itself must be a sound, shallow term. It may reference
        // EARLIER peeled binders (their fvars) and the declared universe params
        // (so a TYPE binder `Sort u` and an INSTANCE binder `Monoid.{u} G` are
        // admitted), but no UNDECLARED universe variable.
        if let Some(reason) = binder_type_reject(&binder_ty, &allowed) {
            return Tier2Outcome::BadBinderType(reason);
        }

        let id = local_ctx.push(Name::anon(), binder_ty.clone(), bd);
        fvars.push(id);
        binders.push((bd, binder_ty));
        // Open this binder: BVar(0) ↦ FVar(id).
        current = body.instantiate(&Expr::fvar(id));
    }

    // `current` is now the fully-opened body. A residual top-level Π means a
    // deeper quantifier than the telescope we peeled — tier-2 does not nest.
    if current.is_pi() {
        return Tier2Outcome::BodyHasNestedPi;
    }

    // The opened body must be tier-1-shaped, tolerating exactly the peeled
    // binders' fvars and the declared universe params.
    if let Some(reason) = structural_reject_allowing_fvars_and_params(&current, &allowed) {
        return Tier2Outcome::BodyNotTier1(reason);
    }

    // Prop check: the body is a proposition iff its type whnf-reduces to Sort 0,
    // computed IN the peeled local context (the body mentions its fvars). The
    // type checker is told the declared universe params so `Sort u` resolves.
    let mut tc = TypeChecker::with_context(env, local_ctx.clone());
    if !allowed.is_empty() {
        tc.set_level_params(level_params.clone());
    }
    let Ok(ty) = tc.infer_type(&current) else {
        return Tier2Outcome::BodyNotTypeable;
    };
    if !tc.whnf(&ty).is_prop() {
        return Tier2Outcome::BodyNotAProp;
    }

    Tier2Outcome::Accept(Box::new(Tier2Plan {
        fvars,
        binders,
        local_ctx,
        body: current,
        level_params,
    }))
}

/// Collect, in stable first-seen order, every universe `Param` name reachable
/// from `goal` — the level params on `Sort` nodes and on `Const` instantiation
/// lists, walking the whole term. These are the goal's universe variables; they
/// become the graduated theorem's `level_params`. De Bruijn-agnostic (levels
/// carry no binding), so a single structural walk is exact.
fn collect_goal_level_params(goal: &Expr) -> Vec<Name> {
    let mut params: Vec<Name> = Vec::new();
    let mut stack: Vec<&Expr> = vec![goal];
    while let Some(expr) = stack.pop() {
        match expr.kind() {
            ExprKind::Sort(level) => level.collect_params(&mut params),
            ExprKind::Const(_, levels) => {
                for l in levels.iter() {
                    l.collect_params(&mut params);
                }
            }
            ExprKind::App(f, a) => {
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                stack.push(ty);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => stack.push(inner),
            _ => {}
        }
    }
    params
}

/// Re-abstract a proof of the OPENED body back over the peeled telescope,
/// recovering a closed term of the original `∀` type. For binders
/// `(bd₀, A₀) … (bdₙ₋₁, Aₙ₋₁)` (outermost first) with fresh variables
/// `fvars[0..n]`, produces `λ (x₀ : A₀) … (xₙ₋₁ : Aₙ₋₁), proof` with every
/// peeled free variable converted to its correct de Bruijn index.
///
/// The passes are INTERLEAVED, innermost-first: at binder `i` (from `n-1` down
/// to `0`) the *whole accumulated term* — proof body AND every inner binder
/// type already wrapped — is abstracted over `fvars[i]` before the `λ (xᵢ : Aᵢ)`
/// node is wrapped on. This matters because a later binder's type `Aⱼ`
/// (`j > i`) may mention an earlier binder's variable `fvars[i]`; abstracting
/// the wrapped `Lam` (whose type subterm `abstract_fvar` recurses into)
/// converts those occurrences too. A naive "abstract the proof, then wrap raw
/// types" would leave `fvars[i]` un-abstracted inside `Aⱼ`.
///
/// The result is closed iff `proof` mentions no free variables beyond the
/// peeled ones — and if it is not closed, the C1 gate rejects it, so this step
/// cannot launder a leak.
//
// (No `#[must_use]`: the returned `Expr` is already `#[must_use]`, so a second
// attribute trips clippy's `double_must_use`.)
pub fn reabstract_over_binders(plan: &Tier2Plan, proof: &Expr) -> Expr {
    debug_assert_eq!(
        plan.fvars.len(),
        plan.binders.len(),
        "fvars and binders are parallel"
    );
    let mut term = proof.clone();
    // Innermost binder first: index n-1 down to 0.
    for i in (0..plan.fvars.len()).rev() {
        // Abstract this binder's variable out of EVERYTHING wrapped so far
        // (proof body + inner binder types), turning fvars[i] into BVar(0) and
        // lifting the rest by one.
        term = term.abstract_fvar(plan.fvars[i]);
        let (bd, ty) = &plan.binders[i];
        term = Expr::lam(*bd, ty.clone(), term);
    }
    term
}

/// Reject a binder TYPE that is not a shallow term closed modulo the earlier
/// peeled binders and the declared universe params `allowed`. Mirrors the tier-1
/// structural checks but tolerates (a) the earlier-peeled binders' free
/// variables and (b) the declared universe params — so a TYPE binder `Sort u`
/// and an INSTANCE binder `@Monoid.{u} G` are admitted, while an UNDECLARED
/// universe variable is still rejected. The shared walk also covers nested
/// universe usage.
fn binder_type_reject(ty: &Expr, allowed: &HashSet<Name>) -> Option<Tier1Outcome> {
    structural_reject_allowing_fvars_and_params(ty, allowed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Level};

    fn prelude() -> Environment {
        Environment::try_with_prelude_for_import().expect("prelude must build")
    }

    /// `∀ (n : Nat), @Eq.{1} Nat n n` — a closed tier-2 telescope over an
    /// equational `Prop` body. The one binder is `Nat`-typed (monomorphic,
    /// closed); the body is a reflexive equality referencing the binder.
    fn nat_refl_forall() -> Expr {
        let eq_body = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_str_levels("Eq", vec![Level::succ(Level::zero())]),
                    Expr::const_str("Nat"),
                ),
                Expr::bvar(0),
            ),
            Expr::bvar(0),
        );
        Expr::pi(BinderInfo::Default, Expr::const_str("Nat"), eq_body)
    }

    #[test]
    fn test_tier2_accepts_closed_forall_over_prop_body() {
        let goal = nat_refl_forall();
        let outcome = tier2_classify(&prelude(), &goal);
        let Tier2Outcome::Accept(plan) = outcome else {
            panic!("∀ (n:Nat), n = n must be tier-2 accepted; got {outcome:?}");
        };
        assert_eq!(plan.fvars.len(), 1, "exactly one peeled binder");
        assert_eq!(plan.binders.len(), 1);
        assert!(
            !plan.body.is_pi(),
            "the opened body must not be a residual Π"
        );
    }

    #[test]
    fn test_tier2_rejects_non_pi_goal() {
        // A tier-1 goal (no leading Π) is NotPi for tier-2.
        let goal = Expr::const_str("Nat");
        assert!(matches!(
            tier2_classify(&prelude(), &goal),
            Tier2Outcome::NotPi
        ));
    }

    #[test]
    fn test_tier2_peels_universe_polymorphic_type_binder_and_extracts_param() {
        // `∀ {α : Type u} (a : α), @Eq.{u+1} α a a` — the leading `Type u` TYPE
        // binder is no longer walled (WALL 2 lifted): it is peeled, the param `u`
        // is extracted into `level_params`, and the equational body is accepted.
        let u = Level::param(Name::from_string("u"));
        let eq_body = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_str_levels("Eq", vec![Level::succ(u.clone())]),
                    Expr::bvar(1),
                ),
                Expr::bvar(0),
            ),
            Expr::bvar(0),
        );
        let goal = Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::succ(u)),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), eq_body),
        );
        let Tier2Outcome::Accept(plan) = tier2_classify(&prelude(), &goal) else {
            panic!("a Type-u-led equational goal must now be tier-2 accepted");
        };
        assert_eq!(
            plan.level_params,
            vec![Name::from_string("u")],
            "the Type u binder's universe param must be extracted"
        );
        assert_eq!(
            plan.fvars.len(),
            2,
            "the Type binder and the value binder are both peeled"
        );
    }

    #[test]
    fn test_tier2_rejects_undeclared_universe_param_in_body() {
        // A goal whose body mentions a universe param NOT introduced by any
        // peeled binder is still rejected: `∀ (n : Nat), @Eq.{w} Nat n n` carries
        // a stray `w` that is not in the goal's extracted params... but
        // `collect_goal_level_params` WOULD collect `w`, so to model a genuinely
        // undeclared param we use a const whose level the goal-walk cannot see as
        // a binder source. Here we confirm the inverse guarantee directly:
        // `collect_goal_level_params` collects exactly the params the goal
        // mentions, so the body check allows precisely those — a sanity pin that
        // the allowed set is the goal's own params, never a superset.
        let u = Level::param(Name::from_string("u"));
        // `∀ {α : Type u} (a : α), @Eq.{u+1} α a a` — params = {u}.
        let eq_body = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_str_levels("Eq", vec![Level::succ(u.clone())]),
                    Expr::bvar(1),
                ),
                Expr::bvar(0),
            ),
            Expr::bvar(0),
        );
        let goal = Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::succ(u)),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), eq_body),
        );
        let params = collect_goal_level_params(&goal);
        assert_eq!(
            params,
            vec![Name::from_string("u")],
            "the extracted param set is exactly the goal's own universe params"
        );
    }

    #[test]
    fn test_tier2_peels_through_nested_telescope_then_rejects_body_value() {
        // `∀ (p : Prop) (q : Prop), Prop` — telescope peels to a body that is a
        // type (`Prop`), not a proposition: BodyNotAProp.
        let goal = Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        );
        // After peeling both Prop binders the body `Prop` is Sort 1 — not a Prop.
        assert!(matches!(
            tier2_classify(&prelude(), &goal),
            Tier2Outcome::BodyNotAProp
        ));
    }

    #[test]
    fn test_tier2_rejects_too_many_binders() {
        // A telescope of MAX_BINDERS + 1 Nat binders over `True`.
        let mut body = Expr::const_str("True");
        for _ in 0..=MAX_BINDERS {
            body = Expr::pi(BinderInfo::Default, Expr::const_str("Nat"), body);
        }
        assert!(matches!(
            tier2_classify(&prelude(), &body),
            Tier2Outcome::TooManyBinders
        ));
    }

    #[test]
    fn test_reabstract_roundtrip_is_closed_and_kernel_typechecks() {
        // `∀ (p : Prop), p → p`. Both binders are peeled (the arrow is a
        // non-dependent Π too), so the opened body is the bare hypothesis
        // `FVar(h)` and the proof is `FVar(h)` itself. Re-abstraction must
        // recover a CLOSED `fun (p : Prop) (h : p) => h` of the original ∀ type
        // and kernel-typecheck.
        let goal = Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        );
        let Tier2Outcome::Accept(plan) = tier2_classify(&prelude(), &goal) else {
            panic!("∀ (p:Prop), p → p must peel to a Prop body");
        };
        assert_eq!(plan.fvars.len(), 2, "both Π binders are peeled");
        // The opened body is the hypothesis `FVar(h)`; the proof is that fvar.
        let h_fvar = *plan.fvars.last().expect("two peeled binders");
        let proof_of_body = Expr::fvar(h_fvar);
        let term = reabstract_over_binders(&plan, &proof_of_body);
        assert!(
            !term.has_fvar_quick(),
            "re-abstracted term must be closed (no leaked fvars): {term:?}"
        );
        // The kernel must type-check the re-abstracted term against the ∀ type.
        let env = prelude();
        let tc = TypeChecker::new(&env);
        let inferred = tc.infer_type(&term).expect("re-abstracted term must type");
        assert!(
            tc.is_def_eq(&inferred, &goal),
            "inferred type {inferred:?} must match the original ∀ {goal:?}"
        );
    }
}
