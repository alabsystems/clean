// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Grind tactic — congruence closure + E-matching + case splitting.
//!
//! `grind` is a powerful automation tactic being adopted by Mathlib. It combines:
//! - Preprocessing via `simp` to normalize the goal and hypotheses
//! - Congruence closure (CC) to discover equalities from hypotheses
//! - E-matching to apply rewrite lemmas from the environment
//! - Case splitting on disjunctions and if-then-else expressions
//! - Recursive descent with bounded depth and split limits
//!
//! This is an MVP implementation (~400 LOC) that delegates heavily to existing
//! tactics (`simp`, `cc`, `cases`, `by_cases`, `tauto`, `assumption`).
//!
//! Reference: Lean 4 `Lean.Elab.Tactic.Grind` (45K LOC in C++).

use std::time::Duration;

use clean_auto::AutomationEngine;
use clean_kernel::expr::ExprKind;
use clean_kernel::Expr;

use super::cc::{cc_with_config, CCConfig};
use super::combinator::try_tactic_preserving_state;
use super::connective::contradiction;
use super::grind_bridges::{
    grind_normalize, try_exfalso_then_grind, try_ext_then_grind, try_funext_propext_bridge,
    try_heq_bridge, try_iff_split_then_grind, try_propext_bridge,
};
use super::grind_split::{collect_ite_conditions, try_split_disjunction, try_split_ite};
use super::proof_term::{apply, assumption, exact, rfl};
use super::simp::{simp, SimpConfig};
use super::tauto::tauto;
use super::{
    cert_mathverse, dec_trivial, decide, omega, solve_by_elim, trivial, Goal, ProofState,
    TacticError, TacticResult,
};
use crate::stack_safe;
use crate::unify::MetaState;

pub use super::grind_config::GrindConfig;

pub(super) const GRIND_NO_PROGRESS: &str = "grind";
const GRIND_MAX_DEPTH_EXHAUSTED: &str = "grind/max-depth";
const GRIND_SPLIT_LIMIT_EXHAUSTED: &str = "grind/split-limit";
pub(super) const GRIND_FUNEXT_NO_PROGRESS: &str = "grind/funext";

// ============================================================================
// Main entry points
// ============================================================================

/// Grind tactic — congruence closure + E-matching + case splitting.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, the current goal is closed.
/// ENSURES: On `Err(NoProgress)`, the goal could not be closed within the
///   configured depth and split limits.
pub fn grind(state: &mut ProofState) -> TacticResult {
    grind_with_params(state, &[], false)
}

/// `grind [f, g]` — grind with the tactic's own parameter list.
///
/// Lean routes `grind`'s bracketed parameters into the same E-matching
/// machinery `@[grind]` registers into
/// (`Lean/Meta/Tactic/Grind/EMatchTheoremParam.lean`). Clean seeds them into
/// grind's preprocessing `simp`, which unfolds a parameter naming a definition
/// and rewrites with one naming an equation.
///
/// TWO PASSES, and the order is the whole soundness-of-behaviour argument.
/// Pass one runs with the caller's parameters only — exactly what grind did
/// before this existed, so no goal that closed before can stop closing. Only
/// when that fails does pass two widen preprocessing with the ENVIRONMENT's
/// `@[grind]` set, which is what `Function.update`-shaped rows need (the
/// definition must be unfolded to its `dite` before `try_split_ite` can see a
/// condition to split on). Widening on the first pass would unfold definitions
/// that `@[simp]` lemmas are stated over in their folded form, and those
/// lemmas would stop matching.
///
/// `only` is Lean's `grind only`, and it SUPPRESSES the second pass. Measured
/// on pinned v4.30.0-rc2: with `@[grind] def pickG … := if P then a else b`,
/// `by grind` closes `pickG P a a = a` and `by grind only` FAILS on it, so a
/// `grind only` that consulted the environment set would close goals Lean
/// rejects. The caller's own `[...]` parameters are unaffected — `grind only
/// [f]` still uses `f`, which is the whole point of the form.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, the current goal is closed.
/// ENSURES: On `Err`, the goal remains open (state may be partially modified).
pub(crate) fn grind_with_params(
    state: &mut ProofState,
    params: &[clean_parser::SurfaceName],
    only: bool,
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }
    let base = GrindConfig::default().with_extra_lemmas(params.to_vec());

    if only || env_grind_rewrite_names(state).is_empty() {
        return grind_with_config(state, base);
    }

    let saved_goals = state.goals.clone();
    state.metas_mut().push_scope();
    if grind_with_config(state, base.clone()).is_ok() {
        state.metas_mut().commit();
        return Ok(());
    }
    state.invalidate_tc_cache();
    state.goals = saved_goals;
    state.metas_mut().pop_scope();

    grind_with_config(state, base.with_env_grind_lemmas(true))
}

/// Every `@[grind]` name the preprocessing `simp` may use LEFT TO RIGHT.
///
/// Lean's grind kinds are not interchangeable — `@[grind ←]` is a backward
/// rule, `@[grind cases]` a case-split rule — so only the two kinds that mean
/// "this equation reads left to right" are handed to a left-to-right rewriter
/// (`GrindAttrKind::is_left_to_right_equation`). Everything else stays
/// registered and unused, which is why an unmodeled modifier is recorded
/// rather than rejected.
fn env_grind_rewrite_names(state: &ProofState) -> Vec<clean_parser::SurfaceName> {
    state
        .env()
        .grind_lemmas()
        .iter()
        .filter(|(_, kind)| kind.is_left_to_right_equation())
        .map(|(name, _)| clean_parser::SurfaceName::from_name(name.clone()))
        .collect()
}

/// Grind with custom configuration.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On `Ok(())`, the current goal is closed.
/// ENSURES: On `Err(NoProgress)`, no solution found within resource limits.
/// ENSURES: State may be partially modified (goals reduced) even on failure.
pub fn grind_with_config(state: &mut ProofState, config: GrindConfig) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let mut splits_remaining = config.max_splits;
    let trace = std::env::var_os("CLEAN_GRIND_TRACE").is_some();
    macro_rules! gtrace {
        ($msg:expr) => {
            if trace {
                eprintln!("grind-trace: {}", $msg);
            }
        };
    }

    // Phase 0: Normalize — substitute known equalities (e.g., x = 5 → replace x)
    if trace {
        let target = state
            .goals
            .front()
            .map(|g| format!("{:?}", g.target))
            .unwrap_or_default();
        let head: String = target.chars().take(120).collect();
        eprintln!("grind-trace: phase0 normalize goal={head}");
    }
    stack_safe(|| grind_normalize(state));

    if state.is_complete() {
        return Ok(());
    }

    // Phase 1: Preprocessing — simplify goal and hypotheses
    let target_was_pi = goal_target_is_pi(state);
    if config.use_simp {
        gtrace!("phase1 simp preprocess");
        stack_safe(|| grind_preprocess(state, &config));
    }

    if state.is_complete() {
        return Ok(());
    }

    // Phase 1b: an implication that PREPROCESSING made is introduced, as
    // Lean's grind introduces its goal's binders. simp's default set turns
    // `(if P then x else y) = y` into `P → x = y` (`ite_eq_right_iff`, G39),
    // and the core loop's closers, bridges and splits all read an equation
    // goal; a goal that already was an implication keeps its old route.
    if !target_was_pi {
        let mut introduced = 0usize;
        while introduced < GRIND_PREPROCESS_INTRO_LIMIT && goal_target_is_pi(state) {
            let name = clean_parser::SurfaceName::generated_path("h_grind_intro");
            if super::proof_term::intro(state, &name).is_err() {
                break;
            }
            introduced += 1;
        }
    }

    // Phase 2: Core grind loop — CC + E-matching + case splitting
    gtrace!("phase2 core");
    stack_safe(|| grind_core(state, &config, 0, &mut splits_remaining, &[]))
}

// ============================================================================
// Preprocessing
// ============================================================================

/// At most this many binders are introduced after preprocessing (Phase 1b).
const GRIND_PREPROCESS_INTRO_LIMIT: usize = 16;

/// Whether the current goal's target is syntactically a `∀`/`→`.
fn goal_target_is_pi(state: &ProofState) -> bool {
    state
        .current_goal()
        .is_some_and(|g| matches!(state.metas.instantiate(&g.target).kind(), ExprKind::Pi(..)))
}

/// Run simp to normalize the goal. Non-fatal — swallows errors.
fn grind_preprocess(state: &mut ProofState, config: &GrindConfig) {
    grind_preprocess_with(state, config, &[]);
}

pub(super) fn grind_preprocess_with(
    state: &mut ProofState,
    config: &GrindConfig,
    case_hyps: &[clean_parser::SurfaceName],
) {
    let simp_config = SimpConfig {
        max_steps: config.simp_max_steps,
        beta: true,
        eta: true,
        extra_lemmas: preprocess_extra_lemmas(state, config, case_hyps),
        ..SimpConfig::new()
    };

    // Try simp; if it fails, that is fine — we proceed with the unnormalized goal.
    let _ = simp(state, simp_config.clone());

    // propext bridge: a goal `@Eq Prop p q` is provable exactly when `p ↔ q`
    // is, but every propositional closer in the fan below (tauto, cc, the
    // automation engine) matches on `Iff`/`And`/`Or` and none of them can see
    // through the `Eq`-at-Prop spelling — so `(a ∨ b) = (b ∨ a)` failed with
    // "no progress" while the hand-written `apply propext; tauto` closes it.
    // Applying `propext` HERE, in preprocessing, hands the whole fan the `Iff`
    // form. `apply` type-checks the term and `close_goal` re-checks it, so a
    // wrong bridge fails closed; on failure the goal is left untouched.
    let propext_bridged = try_propext_bridge(state).is_ok();

    // funext bridge: the same blindness one binder up. A Prop-VALUED function
    // equality `@Eq ((x : α) → … → Prop) f g` (Logic/Basic's `xor_false`:
    // `Xor' False = id`) never matches `@Eq Prop`, so the bridge above skips
    // it and the closer fan still cannot see an `Iff`. Applying `funext` once
    // per binder and THEN the propext bridge hands the fan the pointwise
    // `Iff` — the measured hand route is `funext p; apply propext; tauto`.
    // Fail-closed like the bridge above: any failure rolls the goal back.
    let funext_bridged = try_funext_propext_bridge(state).is_ok();

    // RE-NORMALIZE what a bridge produced. simp ran ONCE, BEFORE the bridges,
    // so a goal the bridges REPLACED went to the closer fan unnormalized:
    // `xor_true`'s bridge output is `(True ∧ ¬p) ∨ (p ∧ ¬True) ↔ ¬p`, with
    // `True ∧ …` and `¬True` still standing, and handing that same goal to
    // grind directly closes it. Lean has no one-shot pass to miss — it
    // re-normalizes every fact it asserts (`assertAt` → `preprocess prop`,
    // `Lean/Meta/Tactic/Grind/Intro.lean`).
    //
    // BOUNDED at one extra round, not a fixpoint: the bridges do not run
    // again after this, so a second round has nothing new to bridge, and a
    // loop here would be unbounded simp work inside every grind branch.
    if (propext_bridged || funext_bridged) && !state.is_complete() {
        let _ = simp(state, simp_config.clone());
    }

    // Hypotheses, not only the target. `simp` reads `goal.target` and nothing
    // else, and `SimpConfig` has no location field at all, so a decided
    // `ite`/`dite` sitting in a HYPOTHESIS was never collapsed — the branch
    // context of `Function.Injective.ite` already holds `hx : p x`, `hy : p y`
    // and the `ite` equation, and grind reported no progress on a context that
    // contained everything needed. Lean asserts EVERY hypothesis into the
    // E-graph, normalized (`addHypothesis` → `assertAt` → `preprocess prop`,
    // `Lean/Meta/Tactic/Grind/Intro.lean`).
    grind_normalize_hypotheses(state, config, &simp_config);
}

/// Simplify the hypotheses this normalization can actually move.
///
/// SCOPE, deliberately narrow and stated rather than implied: only a
/// Prop-typed hypothesis whose type CARRIES an `ite`/`dite`. Lean normalizes
/// every fact; Clean's `simp` is expensive enough that doing so would multiply
/// simp work by the size of the local context, and grind has already cost
/// 19.86 GB on one row of this class. The rows this exists for are exactly the
/// conditional ones, so the gate is the class rather than a budget guess.
///
/// Each hypothesis is rewritten through the existing `simp at` path, which
/// rebuilds the fvar and re-checks the transported proof; mutating `decl.ty`
/// in place would invalidate every proof term already referring to it. A
/// hypothesis is never handed ITSELF as a rewrite rule — that would rewrite it
/// to `True` and destroy the fact the branch was split to obtain.
fn grind_normalize_hypotheses(
    state: &mut ProofState,
    config: &GrindConfig,
    simp_config: &SimpConfig,
) {
    let Some(goal) = state.current_goal().cloned() else {
        return;
    };
    // Split the context in two: the CONDITIONAL hypotheses this can move, and
    // the DECIDED facts it moves them with. A `p x` or a `¬p x` is what
    // collapses the `ite` inside the other one — `Function.Injective.ite`'s
    // branch reaches grind through `rcases em (p x)`, so its deciding facts
    // are ordinary locals, not the `h_grind.*` names a split minted.
    let mut conditional = Vec::new();
    let mut decided = Vec::new();
    for decl in &goal.local_ctx {
        let ty = state.metas.instantiate(&decl.ty);
        if !hypothesis_is_a_fact(state, &goal, &ty) {
            continue;
        }
        if collect_ite_conditions(&ty).is_empty() {
            decided.push(decl.fvar);
        } else {
            conditional.push(decl.fvar);
        }
    }

    for hyp in conditional {
        if state.is_complete() {
            return;
        }
        let mut hyp_config = simp_config.clone();
        // Type-selected facts retain their identities even when hidden behind
        // a newer local of the same spelling.
        if let Some(goal) = state.current_goal() {
            for decl in &goal.local_ctx {
                if decided.contains(&decl.fvar) {
                    hyp_config.aesop_simp_lemmas.extend(
                        super::simp::collect_local_extra_lemma_for_decl(state, goal, decl),
                    );
                }
            }
        }
        hyp_config.max_steps = config.simp_max_steps;
        let _ = super::simp::simp_at_fvar_with_config(state, hyp, hyp_config);
    }
}

/// Is this hypothesis type a PROPOSITION — a fact simp may rewrite — rather
/// than data?
fn hypothesis_is_a_fact(state: &ProofState, goal: &Goal, ty: &Expr) -> bool {
    state
        .infer_type(goal, ty)
        .is_ok_and(|sort| crate::tactic::proof_cert_verify::is_prop_type(&sort))
}

/// The names the branch's preprocessing `simp` rewrites with: the case
/// hypotheses this branch was split on, then the tactic's own `[...]`
/// parameters, then — only on the widened retry — the environment's
/// `@[grind]` set.
///
/// Duplicates are dropped so a name written by the caller AND registered
/// `@[grind]` is not offered twice; order is preserved because simp consumes
/// the list in order.
fn preprocess_extra_lemmas(
    state: &ProofState,
    config: &GrindConfig,
    case_hyps: &[clean_parser::SurfaceName],
) -> Vec<clean_parser::SurfaceName> {
    let mut out: Vec<clean_parser::SurfaceName> = Vec::new();
    let env_names = if config.use_env_grind_lemmas {
        env_grind_rewrite_names(state)
    } else {
        Vec::new()
    };
    for name in case_hyps
        .iter()
        .chain(config.extra_lemmas.iter())
        .chain(env_names.iter())
    {
        if !out.contains(name) {
            out.push(name.clone());
        }
    }
    out
}

// ============================================================================
// Core algorithm
// ============================================================================

/// Recursive core of grind: try closers, then CC, then case-split and recurse.
///
/// REQUIRES: `state.goals` is non-empty (caller checks).
/// ENSURES: On `Ok(())`, the current goal is closed.
/// ENSURES: On `Err`, the goal remains open (state may be partially modified).
pub(super) fn grind_core(
    state: &mut ProofState,
    config: &GrindConfig,
    depth: usize,
    splits_remaining: &mut usize,
    case_hyps: &[clean_parser::SurfaceName],
) -> TacticResult {
    if state.is_complete() {
        return Ok(());
    }

    if grind_max_depth_exceeded(depth, config) {
        return Err(grind_no_progress_at(state, GRIND_MAX_DEPTH_EXHAUSTED));
    }

    // Every core step (the root and every case-split branch) is charged to the
    // declaration's automation work budget — Lean's grind polls
    // `checkSystem` the same way — and a spent budget ends grind at once
    // instead of fanning the remaining branches out over closers that would
    // each give up immediately.
    if !crate::decl_work_budget::charge("grind") {
        return Err(grind_budget_exhausted());
    }

    let trace = std::env::var_os("CLEAN_GRIND_TRACE").is_some();
    // Step 1: Try immediate closers (stack_safe: closers may call whnf/is_def_eq)
    if trace {
        eprintln!("grind-trace: core depth={depth} step1 closers");
    }
    if stack_safe(|| try_closers(state, config)) {
        return Ok(());
    }

    // Step 1b: Extensionality and the `Eq`/`HEq` spelling.
    //
    // AFTER the closer fan, never before it. A function equality that `rfl`
    // or `assumption` already closes (`h : f = g ⊢ f = g` at `Nat → Nat`)
    // must keep closing that way: replacing it with a pointwise goal first
    // would leave `assumption` nothing to match. Both steps are speculative
    // and roll the goal back whole.
    if trace {
        eprintln!("grind-trace: core depth={depth} step1b ext/heq");
    }
    if stack_safe(|| try_ext_then_grind(state, config, depth, splits_remaining, case_hyps)) {
        return Ok(());
    }
    if stack_safe(|| try_heq_bridge(state, config)) {
        return Ok(());
    }

    // Step 1c: open the GOAL's own structure — `exfalso` when the context can
    // reach a contradiction, `Iff.intro` on a biconditional. Both after the
    // closer fan, both speculative.
    if trace {
        eprintln!("grind-trace: core depth={depth} step1c exfalso/iff");
    }
    if stack_safe(|| try_exfalso_then_grind(state, config, depth, splits_remaining, case_hyps)) {
        return Ok(());
    }
    if stack_safe(|| try_iff_split_then_grind(state, config, depth, splits_remaining, case_hyps)) {
        return Ok(());
    }

    // Step 2: Congruence closure (stack_safe: CC may trigger deep type checker calls)
    if trace {
        eprintln!("grind-trace: core depth={depth} step2 cc");
    }
    if config.use_cc && stack_safe(|| try_cc(state, config)) {
        return Ok(());
    }

    // Step 3: Automation engine (SMT + superposition via clean-auto)
    if trace {
        eprintln!("grind-trace: core depth={depth} step3 automation");
    }
    if config.use_automation && stack_safe(|| try_automation_engine(state, config)) {
        return Ok(());
    }

    // Step 4: Case splitting — find a disjunction or ite to split on
    if *splits_remaining == 0 {
        return Err(grind_no_progress_at(state, GRIND_SPLIT_LIMIT_EXHAUSTED));
    }

    if trace {
        eprintln!("grind-trace: core depth={depth} step4 splits");
    }
    // Try splitting on disjunctions in hypotheses
    if config.split_disjunctions {
        if let Some(result) =
            try_split_disjunction(state, config, depth, splits_remaining, case_hyps)
        {
            return result;
        }
    }

    // Try splitting on ite/dite conditions in the goal
    if config.split_ite {
        if let Some(result) = try_split_ite(state, config, depth, splits_remaining, case_hyps) {
            return result;
        }
    }

    Err(grind_no_progress_at(state, GRIND_NO_PROGRESS))
}

fn grind_max_depth_exceeded(depth: usize, config: &GrindConfig) -> bool {
    depth > config.max_depth
}

/// The error `grind` fails with once the declaration's automation work budget
/// is spent (see `crate::decl_work_budget`).
fn grind_budget_exhausted() -> TacticError {
    TacticError::BudgetExceeded {
        tactic: "grind".to_owned(),
        detail: crate::decl_work_budget::exhausted_detail(),
    }
}

pub(super) fn grind_no_progress(tactic: &'static str) -> TacticError {
    TacticError::no_progress(tactic)
}

/// The same diagnostic, carrying the goal `grind` gave up on.
///
/// Use this at the four `grind_core` exits, whose error propagates out of
/// `grind_with_config` to the user; `grind_no_progress` stays for the sites
/// swallowed as control flow (`try_propext_bridge`, `try_funext_propext_bridge`
/// and the automation engine inside `try_tactic_preserving_state`), which never
/// reach a human and must not pay to format a goal.
///
/// After a case split this reports the BRANCH grind actually died on, not the
/// goal the user wrote — which is what the message says, and is the more useful
/// of the two: the branch is the blocker. `grind_with_config` documents that
/// state may be partially modified on failure, so no site here can report the
/// original goal anyway.
pub(super) fn grind_no_progress_at(state: &ProofState, tactic: &'static str) -> TacticError {
    crate::tactic::display::no_progress_with_goal(state, tactic)
}

// ============================================================================
// Closers
// ============================================================================

/// Try lightweight tactics to close the goal immediately.
/// Returns `true` if the goal was closed.
fn try_closers(state: &mut ProofState, config: &GrindConfig) -> bool {
    let trace = std::env::var_os("CLEAN_GRIND_TRACE").is_some();
    // One automation work unit per closer attempted, and no further closer
    // once the declaration's budget is spent: each would give up at once, and
    // the ones that do not charge the budget themselves (`solve_by_elim`,
    // `tauto`) would still run their own searches.
    macro_rules! closer_step {
        ($msg:expr) => {
            if trace {
                eprintln!("grind-trace: closer {}", $msg);
            }
            if !crate::decl_work_budget::charge("grind") {
                return false;
            }
        };
    }
    // Reflexivity
    closer_step!("rfl");
    if try_tactic_preserving_state(state, rfl) {
        return true;
    }

    // Assumption
    closer_step!("assumption");
    if try_tactic_preserving_state(state, assumption) {
        return true;
    }

    // Trivial (True, empty goals)
    closer_step!("trivial");
    if try_tactic_preserving_state(state, trivial) {
        return true;
    }

    // Contradiction
    closer_step!("contradiction");
    if try_tactic_preserving_state(state, contradiction) {
        return true;
    }

    // Solve by elim with bounded depth
    let sbe_depth = config.solve_by_elim_depth;
    closer_step!("triggered_solve_by_elim");
    if try_triggered_solve_by_elim(state, sbe_depth) {
        return true;
    }
    closer_step!("solve_by_elim");
    if try_tactic_preserving_state(state, |s| solve_by_elim(s, sbe_depth)) {
        return true;
    }

    // Tauto for propositional reasoning
    closer_step!("tauto");
    if config.use_tauto && try_tactic_preserving_state(state, tauto) {
        return true;
    }

    // Arithmetic closers: project normalization, raw mathverse, decide, dec_trivial.
    closer_step!("arithmetic");
    if config.use_arithmetic_closers && try_arithmetic_closers(state) {
        return true;
    }

    false
}

fn try_arithmetic_closers(state: &mut ProofState) -> bool {
    let trace = std::env::var_os("CLEAN_GRIND_TRACE").is_some();
    macro_rules! atrace {
        ($msg:expr) => {
            if trace {
                eprintln!("grind-trace: arith-closer {}", $msg);
            }
        };
    }
    // `cert_mathverse` (certified omega) and `omega` decide linear
    // arithmetic; on a goal with no arithmetic in it they only cost — the
    // diagnosis measured `cert_mathverse` at 19.86 GB and 4 minutes on
    // `dite_dite_comm` without terminating. Now that grind actually splits
    // `ite`/`dite`, every branch reaches this fan, so they run only when the
    // goal or a hypothesis mentions a numeral or an arithmetic operator.
    let arithmetic = state.current_goal().is_some_and(|g| {
        mentions_arithmetic(&state.metas.instantiate(&g.target))
            || g.local_ctx
                .iter()
                .any(|d| mentions_arithmetic(&state.metas.instantiate(&d.ty)))
    });
    if arithmetic {
        atrace!("cert_mathverse");
        if try_closer_without_env_growth(state, cert_mathverse) {
            return true;
        }
        atrace!("omega");
        if try_tactic_preserving_state(state, omega) {
            return true;
        }
    }
    atrace!("decide");
    if try_tactic_preserving_state(state, decide) {
        return true;
    }
    atrace!("dec_trivial");
    try_tactic_preserving_state(state, dec_trivial)
}

/// [`try_tactic_preserving_state`], refusing an attempt that GREW the
/// environment.
///
/// `cert_mathverse` normalizes casts through `rewrite_target_with_cast_lemmas`,
/// which installs its lemma overlay (`Nat.cast_eq_prop`, … — axioms) into the
/// PROOF STATE's environment. A proof built on them checks there and fails the
/// declaration's own check ("Unknown constant: Nat.cast_eq_prop"), so grind
/// took a closer that could never land and stopped looking. Once simp could
/// rewrite under a binder (`forall_congr` in the prelude, G39), the overlay
/// started firing on `a = b → b = a` and `iffEq` lost its `omega` route. An
/// attempt that needed new constants is rolled back like a failed one.
fn try_closer_without_env_growth(
    state: &mut ProofState,
    tactic: fn(&mut ProofState) -> TacticResult,
) -> bool {
    let saved = state.clone();
    let before = state.env.num_constants();
    if !try_tactic_preserving_state(state, tactic) {
        return false;
    }
    if state.env.num_constants() == before {
        return true;
    }
    *state = saved;
    false
}

/// Does `e` mention a numeral or an arithmetic operator — the goals the
/// omega-family closers can decide?
fn mentions_arithmetic(e: &Expr) -> bool {
    const ARITH: &[&str] = &[
        "HAdd.hAdd",
        "HSub.hSub",
        "HMul.hMul",
        "HDiv.hDiv",
        "HMod.hMod",
        "HPow.hPow",
        "LE.le",
        "LT.lt",
        "GE.ge",
        "GT.gt",
        "OfNat.ofNat",
        "Nat.succ",
        "Nat.add",
        "Nat.sub",
        "Nat.mul",
        "Int.add",
        "Int.sub",
        "Int.mul",
        "Neg.neg",
        "Dvd.dvd",
        "Nat",
        "Int",
    ];
    stack_safe(|| match e.kind() {
        ExprKind::Lit(_) => true,
        ExprKind::Const(n, _) => ARITH.contains(&n.to_string().as_str()),
        ExprKind::App(f, a) => mentions_arithmetic(f) || mentions_arithmetic(a),
        ExprKind::Lam(_, d, b) | ExprKind::Pi(_, d, b) => {
            mentions_arithmetic(d) || mentions_arithmetic(b)
        }
        ExprKind::Let(_, t, v, b, _) => {
            mentions_arithmetic(t) || mentions_arithmetic(v) || mentions_arithmetic(b)
        }
        ExprKind::MData(_, i) | ExprKind::Proj(_, _, i) => mentions_arithmetic(i),
        _ => false,
    })
}

pub(super) fn try_triggered_solve_by_elim(state: &mut ProofState, max_depth: usize) -> bool {
    let Some(goal) = state.current_goal().cloned() else {
        return false;
    };
    let candidates = collect_ematch_trigger_candidates(&goal, &state.metas);

    for fvar in candidates {
        let saved_goals = state.goals.clone();
        state.metas_mut().push_scope();

        if apply(state, Expr::fvar(fvar)).is_ok() && solve_by_elim(state, max_depth).is_ok() {
            state.metas_mut().commit();
            return true;
        }

        state.invalidate_tc_cache();
        state.goals = saved_goals;
        state.metas_mut().pop_scope();
    }

    false
}

fn collect_ematch_trigger_candidates(goal: &Goal, metas: &MetaState) -> Vec<clean_kernel::FVarId> {
    let Some(target_head) = trigger_head(&metas.instantiate(&goal.target)) else {
        return vec![];
    };

    goal.local_ctx
        .iter()
        .filter_map(|decl| {
            let conclusion = pi_conclusion(metas.instantiate(&decl.ty));
            let conclusion_head = trigger_head(&conclusion)?;
            (conclusion_head == target_head).then_some(decl.fvar)
        })
        .collect()
}

fn pi_conclusion(mut ty: Expr) -> Expr {
    while let ExprKind::Pi(_, _, body) = ty.kind() {
        ty = body.as_ref().clone();
    }
    ty
}

fn trigger_head(expr: &Expr) -> Option<Expr> {
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Const(_, _) | ExprKind::FVar(_) => Some(head.clone()),
        _ => None,
    }
}

/// Try congruence closure to close an equality goal.
/// Returns `true` if the goal was closed.
fn try_cc(state: &mut ProofState, config: &GrindConfig) -> bool {
    let cc_config = CCConfig {
        max_iterations: config.cc_max_iterations,
        verbose: false,
    };
    try_tactic_preserving_state(state, |s| cc_with_config(s, cc_config.clone()))
}

// ============================================================================
// Automation engine (SMT + superposition via clean-auto)
// ============================================================================

/// Try the clean-auto automation engine to close the goal via SMT or superposition.
///
/// The engine collects hypotheses from the local context, translates the goal to
/// an SMT query, and attempts proof reconstruction. This covers goals that require
/// combinations of equality reasoning, propositional logic, and arithmetic that
/// the simpler closers miss.
///
/// REQUIRES: `state` has at least one open goal.
/// ENSURES: Returns `true` if the goal was closed; `false` otherwise.
/// ENSURES: On `false`, state is fully restored.
fn try_automation_engine(state: &mut ProofState, config: &GrindConfig) -> bool {
    let timeout = Duration::from_millis(config.automation_timeout_ms);

    try_tactic_preserving_state(state, |s| {
        let goal = s.current_goal().ok_or(TacticError::NoGoals)?.clone();
        let local_ctx = s.build_local_ctx(&goal);
        let target = s.metas.instantiate(&goal.target);

        let engine = AutomationEngine::new();
        let proof_result = engine
            .auto_prove(s.env(), &target, timeout, Some(&local_ctx))
            .ok_or_else(|| TacticError::no_progress("grind/automation"))?;

        exact(s, proof_result.proof_term().clone())
    })
}

#[cfg(test)]
#[path = "grind_tests.rs"]
mod grind_tests;
