// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The registered `decide` and `native_decide` tactics, following Lean's
//! procedure (`Lean/Elab/Tactic/Decide.lean` at the pin, v4.30.0-rc2).
//!
//! Lean's `decide`:
//!
//! 1. `preprocessPropToDecide`: instantiate the goal's metavariables,
//!    zeta-delta-reduce let-bound locals, then refuse a goal that still
//!    mentions a metavariable or a free variable. This runs before anything
//!    is evaluated, so `example (x : Nat) (h : x < 3) : x < 5 := by decide` is
//!    refused even though `x < 3` would make the goal true.
//! 2. Synthesize `Decidable p` and reduce it to weak head normal form at
//!    DEFAULT transparency (`withAtLeastTransparency .default <| whnf s`), so
//!    an `@[irreducible]` head stays folded and the instance is stuck.
//! 3. On `isTrue`, close with `of_decide_eq_true (Eq.refl true)` behind an
//!    expected-type hint (`mkDecideProof`): the kernel recomputes the decision
//!    while checking the term; the reduction's own payload is never embedded.
//!
//! Clean's internal `eval_decide` ladder (`decide.rs`) is not this tactic. It
//! stays as the decision rung of `omega`, `norm_num`, `linarith`, `nlinarith`,
//! `norm_cast` and `positivity`, SMT fallback included (plan item
//! `tactics-decide-lean-faithful` (d); `decide_fallback_routing.rs`).
//!
//! `native_decide` shares step 1 with Lean (the same message). Lean then
//! compiles `decide p`, runs it, and asserts the result through a per-use
//! auxiliary axiom `<decl>._native.native_decide.ax_N_M` (`nativeEqTrue`).
//! Clean keeps `native_decide` axiom-free: the native oracle (when admitted)
//! only chooses the verdict, and an accepted goal is closed by a term the
//! kernel re-checks. Native code does not respect reducibility, so its kernel
//! rung reduces the instance at ALL transparency. The `of_decide_eq_true`
//! term it closes with is still re-checked at the elaboration boundary at
//! default transparency (B14, `verify_tactic_proof`), so `five = 5 :=
//! by native_decide` for `@[irreducible] def five := 5` is REFUSED where
//! pinned Lean accepts it through its per-use `_native` axiom (DECISIONS
//! R127 (e); pinned in `tests/decide_lean_faithful_e2e.rs`). What Lean's
//! compiler would not compile (`noncomputable` code, an axiom it does not
//! erase) or would run elsewhere (`@[implemented_by]`) is refused before
//! anything is evaluated, as is an instance that mentions a local
//! (`decide_lean/native.rs`).
//!
//! Instance search is Clean's resolver, queried in the goal's scope
//! ([`resolve_decidable`]): local instances first at every sub-goal, matched
//! at instance transparency (`infer/instance/locals_first.rs`). A `have`
//! local is opaque, in the goal and in the instance alike ([`reducer`]).
//!
//! Where Clean's built-in prelude lacks a core instance Lean declares (a `∀`
//! over `Bool`, `p → q`, the derived `DecidableEq` of `Option`, `Prod`, …),
//! `decide_lean/plan.rs` assembles what Lean's instance search would — every
//! sub-instance found with the binders above it free — and reduces it as
//! Lean reduces it.

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, ExprVisitor, FVarId, Level, TypeChecker};

use super::core::{Goal, ProofState, TacticError, TacticResult};
use crate::unify::MetaState;

mod native;
mod plan;
mod standins;

/// How far the `Decidable` instance is reduced before its constructor is read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Reduction {
    /// Lean's `decide`: default transparency, `@[irreducible]` stays folded.
    Default,
    /// Native evaluation (`native_decide`'s kernel rung): everything unfolds.
    All,
}

/// What reducing the goal's `Decidable` instance established.
pub(super) enum InstanceVerdict {
    /// The instance reduced to `isTrue`; the goal is closed with
    /// `of_decide_eq_true`, re-checked by the kernel.
    Closed,
    /// The instance reduced to `isFalse`: the proposition is false.
    IsFalse,
    /// The instance resolved but did not reduce to a constructor.
    Stuck {
        /// The resolved `Decidable p` instance.
        instance: Expr,
        /// Its weak head normal form, where reduction stopped.
        reduced: Expr,
    },
    /// No `Decidable p` instance resolved.
    NoInstance,
}

/// Which occurrences of free variables an expression has.
#[derive(Debug, Default, Clone, Copy)]
struct FreeVars {
    metas: bool,
    locals: bool,
}

/// Classify the free variables of `expr`: elaborator metavariables are FVars
/// carrying [`MetaState`]'s tag, everything else is a local.
fn free_vars(expr: &Expr) -> FreeVars {
    struct Classify(FreeVars);
    impl ExprVisitor for Classify {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_fvar(&mut self, id: FVarId) {
            if MetaState::from_fvar(id).is_some() {
                self.0.metas = true;
            } else {
                self.0.locals = true;
            }
        }
    }
    if !expr.has_fvar_quick() {
        return FreeVars::default();
    }
    let mut classify = Classify(FreeVars::default());
    classify.visit_expr(expr);
    classify.0
}

/// Replace every `let`-bound local of `goal`'s context by its value (Lean's
/// `zetaReduce`). Values only mention earlier locals, so one pass from the
/// innermost declaration outwards removes a whole chain. A `have` local is
/// opaque in Lean (no value), so it stays: Clean keeps a value for it, marked
/// as a `have`'s (`LocalDecl::is_have`; pinned v4.30.0-rc2: `have x : Nat :=
/// 5` then `x = 5 := by decide` is "must not contain free variables").
fn zeta_delta(state: &ProofState, goal: &Goal, target: &Expr) -> Expr {
    let mut target = target.clone();
    for decl in goal.local_ctx.iter().rev() {
        let Some(value) = decl.reduction_value() else {
            continue;
        };
        if MetaState::from_fvar(decl.fvar).is_none() {
            target = target.subst_fvar(decl.fvar, &state.metas().instantiate(value));
        }
    }
    target
}

/// Lean's `preprocessPropToDecide`, with its v4.30.0-rc2 messages. Returns the
/// goal proposition, metavariables instantiated and let-locals unfolded.
///
/// # Errors
/// `InvalidTarget` when the proposition mentions a metavariable or a free
/// variable; the metavariable check comes first, as in Lean.
pub(super) fn preprocess_prop_to_decide(
    state: &ProofState,
    goal: &Goal,
    tactic: &str,
) -> Result<Expr, TacticError> {
    let mut target = state.metas().instantiate(&goal.target);
    if free_vars(&target).locals {
        target = zeta_delta(state, goal, &target);
    }
    let found = free_vars(&target);
    let shown = crate::error_render::term(&target);
    if found.metas {
        return Err(TacticError::InvalidTarget {
            tactic: tactic.into(),
            detail: format!("Expected type must not contain metavariables\n  {shown}"),
        });
    }
    if found.locals {
        return Err(TacticError::InvalidTarget {
            tactic: tactic.into(),
            detail: format!(
                "Expected type must not contain free variables\n  {shown}\n\n\
                 Hint: Use the `+revert` option to automatically clean up and revert \
                 free variables"
            ),
        });
    }
    Ok(target)
}

/// `@of_decide_eq_true p s (@id (decide p = true) (@Eq.refl Bool true))`:
/// Lean's `mkDecideProof` with its expected-type hint (`mkExpectedPropHint`).
fn of_decide_eq_true_proof(target: &Expr, instance: &Expr) -> Expr {
    let one = Level::succ(Level::zero());
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let decided = Expr::apps(
        Expr::const_(Name::from_string("Decidable.decide"), vec![]),
        [target.clone(), instance.clone()],
    );
    let decided_eq_true = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
        [bool_ty.clone(), decided, bool_true.clone()],
    );
    let refl = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![one]),
        [bool_ty, bool_true],
    );
    let hinted = Expr::apps(
        Expr::const_(Name::from_string("id"), vec![Level::zero()]),
        [decided_eq_true, refl],
    );
    Expr::apps(
        Expr::const_(Name::from_string("of_decide_eq_true"), vec![]),
        [target.clone(), instance.clone(), hinted],
    )
}

/// Synthesize `class_ty` the way Lean's `synthInstance` does inside the goal:
/// the goal's class-typed locals are local instances, tried first at every
/// sub-goal (a `∀`-typed local and a `DecidableEq` local included), and the
/// file's instance state applies — an `attribute [-instance]` erasure,
/// `local instance`s of an open section, `scoped instance`s of an open
/// namespace. This is the query simp's `synthesizeArgs` makes
/// (`simp/instance_slot.rs`).
///
/// ENSURES: on `Some(s)`, `s` mentions no unassigned metavariable.
pub(super) fn resolve_class(state: &ProofState, goal: &Goal, class_ty: &Expr) -> Option<Expr> {
    let scope = crate::infer::TacticInstanceScope {
        instances: state.instances.as_ref(),
        namespace_state: state.namespace_state(),
        visibility: state.instance_visibility.as_deref(),
        rigid_levels: state.metas.rigid_level_params_snapshot(),
        locals: state
            .meta_scope_for_context(&goal.local_ctx)
            .into_iter()
            .map(|(name, fvar, ty)| {
                let ty = state.metas.instantiate(&ty);
                (name, fvar, ty)
            })
            .collect(),
        next_fvar: state.next_fvar,
        level_mint: state.level_mint.clone(),
    };
    crate::ElabCtx::synthesize_in_tactic_scope(&state.env, &scope, class_ty)
}

/// [`resolve_class`] for `Decidable target`.
pub(super) fn resolve_decidable(state: &ProofState, goal: &Goal, target: &Expr) -> Option<Expr> {
    let class_ty = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        target.clone(),
    );
    resolve_class(state, goal, &class_ty)
}

/// A fresh kernel checker for `goal` that reduces as `reduction` says, with
/// every `have` local bound WITHOUT its value, as in Lean's local context: a
/// `have`-bound instance stays stuck where its `let` twin unfolds (pinned
/// v4.30.0-rc2: `have inst : Decidable (1 = 1) := isTrue rfl; decide` is
/// stuck at `inst`). Fresh, so a default-transparency verdict never enters
/// the full-transparency caches the other tactics share. Honouring
/// reducibility at `Default` keeps exactly `@[irreducible]` folded (the
/// kernel's B14 gate), which is Lean's `canUnfold` at `.default` for
/// definitions.
pub(super) fn reducer<'s>(
    state: &'s ProofState,
    goal: &Goal,
    reduction: Reduction,
) -> TypeChecker<'s> {
    let tc = TypeChecker::with_context(state.env(), state.build_local_ctx(goal));
    tc.set_honor_reducibility(reduction == Reduction::Default);
    tc
}

/// `instance` in weak head normal form at `reduction` ([`reducer`]).
pub(super) fn reduce_instance(
    state: &ProofState,
    goal: &Goal,
    instance: &Expr,
    reduction: Reduction,
) -> Expr {
    reducer(state, goal, reduction).whnf(instance)
}

/// Head constant name of `expr`, if it is a constant application.
fn head_is(expr: &Expr, name: &str) -> bool {
    matches!(expr.get_app_fn().kind(), ExprKind::Const(head, _) if head == &Name::from_string(name))
}

/// Resolve `Decidable target`, reduce it as `reduction` says, and on `isTrue`
/// close the front goal with Lean's `of_decide_eq_true` term.
///
/// REQUIRES: `goal` is the front goal of `state`; `target` is its proposition
/// with no metavariables and no free variables (see
/// [`preprocess_prop_to_decide`]).
/// ENSURES: `Closed` iff the goal was closed by a term `close_goal` re-checked;
/// every other verdict leaves the goal open.
///
/// # Errors
/// The kernel's refusal of the assembled term, which would mean the
/// elaborator's reduction and the kernel's disagree.
pub(super) fn decide_by_instance(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    reduction: Reduction,
) -> Result<InstanceVerdict, TacticError> {
    let Some(instance) = resolve_decidable(state, goal, target) else {
        return Ok(InstanceVerdict::NoInstance);
    };
    let reduced = reduce_instance(state, goal, &instance, reduction);
    if head_is(&reduced, "Decidable.isTrue") {
        state.close_goal(goal, of_decide_eq_true_proof(target, &instance))?;
        return Ok(InstanceVerdict::Closed);
    }
    if head_is(&reduced, "Decidable.isFalse") {
        return Ok(InstanceVerdict::IsFalse);
    }
    Ok(InstanceVerdict::Stuck { instance, reduced })
}

/// Lean's refusal of a proposition its instance reduced to `isFalse`.
fn proved_false(tactic: &str, verb: &str, target: &Expr, detail: Option<&str>) -> TacticError {
    let shown = crate::error_render::term(target);
    let mut message = format!("Tactic `{tactic}` {verb} that the proposition\n  {shown}\nis false");
    if let Some(detail) = detail {
        message.push_str(&format!("\n({detail})"));
    }
    TacticError::InvalidTarget {
        tactic: tactic.into(),
        detail: message,
    }
}

/// Lean's refusal when no `Decidable` instance is found.
fn no_instance(tactic: &str, target: &Expr) -> TacticError {
    TacticError::InvalidTarget {
        tactic: tactic.into(),
        detail: format!(
            "failed to synthesize\n  Decidable ({})",
            crate::error_render::term(target)
        ),
    }
}

/// Lean's refusal when the instance does not reduce to a constructor.
fn stuck(tactic: &str, target: &Expr, instance: &Expr, reduced: &Expr) -> TacticError {
    TacticError::InvalidTarget {
        tactic: tactic.into(),
        detail: format!(
            "Tactic `{tactic}` failed for proposition\n  {}\nbecause its `Decidable` \
             instance\n  {}\ndid not reduce to `isTrue` or `isFalse`.\n\nReduction got \
             stuck at the `Decidable` instance\n  {}",
            crate::error_render::term(target),
            crate::error_render::term(instance),
            crate::error_render::term(reduced)
        ),
    }
}

/// Lean's verdict on a [`plan::Plan`]: close the goal with the assembled
/// proof (re-checked by the kernel), or refuse as Lean does.
fn decide_by_plan(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    plan: &plan::Plan,
    tactic: &str,
    verb: &str,
    reduction: Reduction,
) -> TacticResult {
    match plan::evaluate(state, goal, plan, reduction) {
        plan::Verdict::Proved(proof) => state.close_goal(goal, proof),
        plan::Verdict::False { why, .. } => Err(proved_false(tactic, verb, target, Some(&why))),
        plan::Verdict::Stuck(why) => Err(TacticError::InvalidTarget {
            tactic: tactic.into(),
            detail: format!(
                "Tactic `{tactic}` failed for proposition\n  {}\n({why})",
                crate::error_render::term(target)
            ),
        }),
    }
}

/// Lean's verdict when no `Decidable` instance resolved for the whole goal:
/// the core instances Clean's built-in prelude lacks, assembled and reduced
/// as Lean's (`plan.rs`), or "failed to synthesize".
fn without_instance(
    state: &mut ProofState,
    goal: &Goal,
    target: &Expr,
    tactic: &str,
    verb: &str,
    reduction: Reduction,
) -> TacticResult {
    match plan::synthesize(state, goal, target) {
        Some(plan) => decide_by_plan(state, goal, target, &plan, tactic, verb, reduction),
        None => Err(no_instance(tactic, target)),
    }
}

/// The registered `decide` (Lean's `evalDecideCore` with the default config).
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On Ok, the front goal is closed by `of_decide_eq_true` (or, where
/// Clean's built-in prelude lacks a core instance Lean declares, by a
/// kernel-checked case split whose leaves are, or by `Eq.refl` for an equation
/// definitionally true at default transparency), every term re-checked by the
/// kernel.
///
/// # Errors
/// Lean's refusals: metavariables, free variables, no instance, an instance
/// stuck at default transparency, or one that reduced to `isFalse`. No SMT
/// solver is consulted.
pub(crate) fn decide(state: &mut ProofState) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = preprocess_prop_to_decide(state, &goal, "decide")?;
    match decide_by_instance(state, &goal, &target, Reduction::Default)? {
        InstanceVerdict::Closed => Ok(()),
        InstanceVerdict::IsFalse => Err(proved_false("decide", "proved", &target, None)),
        InstanceVerdict::Stuck { instance, reduced } => {
            Err(stuck("decide", &target, &instance, &reduced))
        }
        InstanceVerdict::NoInstance => without_instance(
            state,
            &goal,
            &target,
            "decide",
            "proved",
            Reduction::Default,
        ),
    }
}

/// The registered `native_decide` (Lean's `evalNativeDecide`), axiom-free.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On Ok, the front goal is closed by a kernel-checked term,
/// `of_decide_eq_true` from the instance reduced at ALL transparency (the
/// native rung's payload only when that fails). No auxiliary axiom is added.
///
/// # Errors
/// Lean's refusals (metavariables, free variables, no instance, evaluated to
/// false), or a kernel rung that could not evaluate the instance.
pub(crate) fn native_decide(state: &mut ProofState) -> TacticResult {
    const TACTIC: &str = "native_decide";
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = preprocess_prop_to_decide(state, &goal, TACTIC)?;
    let instance = resolve_decidable(state, &goal, &target);
    let stand_in = match instance {
        Some(_) => None,
        // Lean synthesizes before it compiles anything: no instance, no run
        // (pinned v4.30.0-rc2: `Pd 1 := by native_decide` for a semireducible
        // `def Pd n : Prop := n = 1` fails to synthesize).
        None => Some(
            plan::synthesize(state, &goal, &target).ok_or_else(|| no_instance(TACTIC, &target))?,
        ),
    };
    if let Some(error) =
        native::refusal(state, &goal, &target, instance.as_ref(), stand_in.as_ref())
    {
        return Err(error);
    }
    match super::native_decide_eval::execute_native_decide(state, &goal) {
        Ok(super::native_decide_eval::NativeDecideExecOutcome::Proved(proof)) => {
            // The verdict is true. Close with Lean's term shape, which the
            // kernel recomputes; the reduction's payload is typed at the
            // reduced proposition (`5 = 5` for `five = 5` with `five`
            // irreducible), which the elaborator's `close_goal` comparison
            // does not unfold, so it is only the fallback.
            if let InstanceVerdict::Closed =
                decide_by_instance(state, &goal, &target, Reduction::All)?
            {
                return Ok(());
            }
            return state.close_goal(&goal, proof);
        }
        Ok(super::native_decide_eval::NativeDecideExecOutcome::Refuted) => {
            return Err(proved_false(TACTIC, "evaluated", &target, None));
        }
        Err(error) => tracing::debug!(
            tactic = TACTIC,
            %error,
            "native execution unavailable; the kernel evaluates the Decidable instance"
        ),
    }
    match decide_by_instance(state, &goal, &target, Reduction::All)? {
        InstanceVerdict::Closed => Ok(()),
        InstanceVerdict::IsFalse => Err(proved_false(TACTIC, "evaluated", &target, None)),
        InstanceVerdict::Stuck { reduced, .. } => Err(TacticError::InvalidTarget {
            tactic: TACTIC.into(),
            detail: format!(
                "Tactic `{TACTIC}` failed: Could not evaluate decidable instance. Error: \
                 its reduction stopped at\n  {}",
                crate::error_render::term(&reduced)
            ),
        }),
        InstanceVerdict::NoInstance => match &stand_in {
            Some(plan) => decide_by_plan(
                state,
                &goal,
                &target,
                plan,
                TACTIC,
                "evaluated",
                Reduction::All,
            ),
            None => Err(no_instance(TACTIC, &target)),
        },
    }
}
