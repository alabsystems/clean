// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lightweight `decide` tactic for decidable propositions.
//!
//! Closes goals that are decidable propositions by evaluation:
//! synthesizes a `Decidable` instance for the goal type, evaluates the
//! decision procedure via WHNF reduction, and extracts the proof from
//! `Decidable.isTrue`.
//!
//! This is the kernel-reduction-based decide path. For the full SMT-backed
//! decide, see `smt/decide/mod.rs`.
//!
//! Part of #3082.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use super::core::{ProofState, TacticError, TacticResult};
use super::equality::match_equality;
use super::nat_expr_eval::eval_nat_expr;
use super::norm_num::{eval_int_expr, try_eval_comparison};
use super::proof_term::rfl;
use crate::ElabCtx;

/// Synthesize a `Decidable` expression for the given proposition.
///
/// Attempts to build a `Decidable p` term by recognizing common decidable
/// forms:
/// - `True` → `Decidable.isTrue True.intro`
/// - `False` → `Decidable.isFalse id`
/// - `@Eq T a b` where T has `DecidableEq` → `T.decEq a b`
/// - Boolean operations → structural
///
/// # Contract
///
/// REQUIRES: `target` is a well-formed Prop expression
/// ENSURES: On `Some(d)`, `d` has type `Decidable target`
/// ENSURES: On `None`, no decidable instance could be synthesized
fn synthesize_decidable(state: &ProofState, target: &Expr) -> Option<Expr> {
    // True
    if matches!(target.kind(), ExprKind::Const(name, _) if name == &Name::from_string("True")) {
        return Some(Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                target.clone(),
            ),
            Expr::const_(Name::from_string("True.intro"), vec![]),
        ));
    }

    // False
    if matches!(target.kind(), ExprKind::Const(name, _) if name == &Name::from_string("False")) {
        return Some(Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Decidable.isFalse"), vec![]),
                target.clone(),
            ),
            // id : False → False
            Expr::lam(BinderInfo::Default, target.clone(), Expr::bvar(0)),
        ));
    }

    // Equality: @Eq T a b → T.decEq a b
    if let Ok((ty, lhs, rhs, _levels)) = match_equality(target) {
        let type_head = ty.get_app_fn();
        if let ExprKind::Const(type_name, _) = type_head.kind() {
            let dec_eq_name = Name::from_string(&format!("{type_name}.decEq"));
            if state.env().get_const(&dec_eq_name).is_some() {
                return Some(Expr::apps(Expr::const_(dec_eq_name, vec![]), [lhs, rhs]));
            }
        }
    }

    // Bool comparisons
    if let ExprKind::Const(name, _) = target.get_app_fn().kind() {
        let name_str = name.to_string();
        // BEq.beq, decide for Bool-valued operations
        if name_str.contains("BEq") || name_str.contains("Bool") {
            // Try to evaluate as a decidable Bool operation via native reduction
            return None; // Fall through to WHNF evaluation
        }
    }

    None
}

/// Try to evaluate a Decidable expression to its constructor via WHNF.
///
/// Returns `Some(proof)` if the expression reduces to `Decidable.isTrue proof`,
/// `None` if it reduces to `Decidable.isFalse` or does not reduce.
fn eval_decidable(
    state: &ProofState,
    goal: &super::core::Goal,
    decidable_expr: &Expr,
) -> Option<Expr> {
    let reduced = state.whnf(goal, decidable_expr);
    let head = reduced.get_app_fn();

    if let ExprKind::Const(name, _) = head.kind() {
        if name == &Name::from_string("Decidable.isTrue") {
            // Extract the proof payload (last argument)
            let args = reduced.get_app_args();
            return args.last().map(|p| (*p).clone());
        }
    }

    None
}

/// What kernel evaluation of a resolved `Decidable target` instance produced.
enum KernelReduction {
    /// The instance reduced to `Decidable.isTrue h`; carries `h : target`.
    IsTrue(Expr),
    /// The instance reduced to `Decidable.isFalse _`: the proposition is false.
    IsFalse,
    /// An instance resolved but WHNF did not expose `isTrue` / `isFalse`.
    Stuck,
    /// No `Decidable target` instance resolved.
    NoInstance,
}

/// Try to decide `target` by resolving a `Decidable target` instance through
/// the proper recursive resolver (`ElabCtx::resolve_instance`) and reducing it
/// via kernel WHNF.
///
/// This is the kernel-reduction `decide` lane: it closes ground decidable goals
/// (`List`/`Int` equality, concrete `select`/`store`, …) with a kernel-checked
/// proof term, BYPASSING `super::smt::decide` (which can embed `trustedAy`
/// axioms — a TCB hole). `resolve_instance` does the full recursive class
/// search the ad-hoc `synthesize_decidable` cannot.
///
/// # Contract
/// REQUIRES: `target` is the (instantiated) goal proposition.
/// ENSURES: On `IsTrue(h)`, `h` is the `isTrue` payload (`h : target`), which
/// the caller re-checks through the kernel in `close_goal`; a false goal cannot
/// produce a witness here. `IsFalse` / `Stuck` / `NoInstance` never close
/// anything — they only select the refusal message.
fn try_decide_by_kernel_reduction(
    state: &mut ProofState,
    goal: &super::core::Goal,
    target: &Expr,
) -> KernelReduction {
    let decidable_target = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        target.clone(),
    );
    // Scope `ctx` so its `&Environment` borrow of `state` ends before the
    // `state.whnf(…)` call below. Crucially, INSTANTIATE the resolved
    // instance's metavariables: `resolve_instance` assigns the deferred
    // dependent-instance args (e.g. the `[DecidableEq α]` of
    // `instDecidableEqList`) as metavars in `ctx.metas` but leaves them
    // un-substituted in the returned term. A metavar-bearing instance is an
    // opaque redex that WHNF cannot reduce to `Decidable.isTrue`, so the lane
    // would silently fall through to SMT. The instantiated term is ground and
    // owned, so nothing borrowed from `ctx` escapes the block.
    let inst_expr = {
        let mut ctx = ElabCtx::new(state.env());
        let Some(resolved) = ctx.resolve_instance(&decidable_target) else {
            return KernelReduction::NoInstance;
        };
        ctx.metas.instantiate(&resolved)
    };
    let reduced = state.whnf(goal, &inst_expr);
    if let ExprKind::Const(name, _) = reduced.get_app_fn().kind() {
        if name == &Name::from_string("Decidable.isTrue") {
            return match reduced.get_app_args().last() {
                Some(proof) => KernelReduction::IsTrue((*proof).clone()),
                None => KernelReduction::Stuck,
            };
        }
        if name == &Name::from_string("Decidable.isFalse") {
            return KernelReduction::IsFalse;
        }
    }
    KernelReduction::Stuck
}

/// Why the kernel-evaluation rungs of `decide` did not close a goal.
///
/// Every variant is a REFUSAL: none of them closes anything. The variant only
/// chooses what `decide` tells the user, so the message says what evaluation
/// actually established rather than what an SMT abstraction guessed.
#[derive(Debug, Clone)]
enum Refusal {
    /// Kernel evaluation established that the proposition is false (a
    /// `Decidable` instance reduced to `isFalse`, possibly inside a finite
    /// case split, whose path the payload names).
    False(String),
    /// No `Decidable target` instance resolved.
    NoInstance,
    /// An instance resolved, or a finite case split applied, but evaluation
    /// did not reach `isTrue` / `isFalse`.
    Stuck(String),
}

impl Refusal {
    /// The detail of a refusal kernel evaluation established: the proposition
    /// is false.
    fn false_detail(prop: &str, why: &str) -> String {
        format!("proved that the proposition `{prop}` is false ({why})")
    }

    /// The error for a proposition kernel evaluation proved FALSE. Final: no
    /// proof of it exists, so nothing — the SMT fallback included — is asked
    /// for one.
    fn false_error(target: &Expr, why: &str) -> TacticError {
        let prop = crate::error_render::term(target);
        TacticError::InvalidTarget {
            tactic: "decide".into(),
            detail: Self::false_detail(&prop, why),
        }
    }

    /// The user-facing error once the SMT fallback has also failed to produce
    /// a kernel-checked proof.
    ///
    /// The SMT verdict is reported only as "no kernel-checked proof": a
    /// satisfying assignment of the bridge's abstraction (where every operation
    /// outside the solver's theories is an uninterpreted function) is not a
    /// counterexample to the goal, so it is never presented as one.
    fn into_error(self, target: &Expr, smt_error: &TacticError) -> TacticError {
        let prop = crate::error_render::term(target);
        let smt = match smt_error {
            TacticError::SmtFailed { detail, .. } => detail.clone(),
            other => other.to_string(),
        };
        let detail = match self {
            Refusal::False(why) => Self::false_detail(&prop, &why),
            Refusal::NoInstance => format!(
                "failed to synthesize `Decidable ({prop})`, and the SMT fallback \
                 produced no kernel-checked proof ({smt})"
            ),
            Refusal::Stuck(why) => format!(
                "failed to reduce `Decidable ({prop})` to `isTrue` or `isFalse` \
                 ({why}), and the SMT fallback produced no kernel-checked proof ({smt})"
            ),
        };
        TacticError::InvalidTarget {
            tactic: "decide".into(),
            detail,
        }
    }
}

/// Result of the kernel-evaluation rungs of `decide` (every rung except the
/// SMT fallback).
enum EvalOutcome {
    /// The goal was closed with a kernel-checked proof term.
    Closed,
    /// NESTED case splits only (`depth > 0`): a proof of the sub-goal
    /// ASSEMBLED from kernel-checked case proofs, not yet re-checked as a
    /// whole and NOT assigned to the sub-goal. The outermost case split
    /// re-checks the entire assembled term once, in `close_goal` (and
    /// `add_decl` checks the declaration again); re-checking every internal
    /// node as well cost `N·2^N` leaf re-checks instead of `2^N` for `N`
    /// nested `Bool` binders. Never returned at `depth == 0`.
    ///
    /// MEASURED (debug build, 2026-09-28, `∀ x1 … xN : Bool, conj = rev-conj`):
    /// this saved 1.5–1.7x at N = 8 and 1.09x at N = 12 (1003 s -> 921 s).
    /// The internal re-checks were NOT the dominant cost the review
    /// suspected: a sample of N = 10 puts ~77% of the time in the LEAVES,
    /// `decide_eq` -> `rfl` -> `apply` (general unification per leaf).
    Assembled(Expr),
    /// Direct ground numeric evaluation showed the proposition is false.
    /// Top-level `decide` reports this at once, without consulting SMT.
    Disproved(String),
    /// Evaluation did not close the goal; top-level `decide` then tries the
    /// SMT fallback and, if that also fails, reports this refusal.
    Refused(Refusal),
}

/// Most nested finite cases (`Bool` binders and decided implications) one
/// `decide` call will evaluate. `N` nested `Bool` binders evaluate `2^N`
/// leaves, so this bounds the work at 4096 leaf evaluations.
const MAX_DECIDE_EVAL_DEPTH: usize = 12;

/// A sub-proposition decided on the way to a finite case split.
enum SubDecision {
    /// Kernel-checked proof of the sub-proposition (metavariables instantiated).
    Proved(Expr),
    /// Evaluation did not prove it.
    Refused(Refusal),
}

/// Decide `target` as a fresh sub-goal of `parent` (same local context) with
/// the kernel-evaluation rungs only, and return its proof term.
///
/// REQUIRES: `state` is a scratch copy the caller discards unless the whole
/// case split closes (see `with_scratch`).
/// ENSURES: the pushed sub-goal is popped whatever the outcome, so `parent`
/// is the front goal again on return.
fn decide_subgoal(
    state: &mut ProofState,
    parent: &super::core::Goal,
    target: Expr,
    depth: usize,
) -> SubDecision {
    let meta_id = state.fresh_meta_in_context(target.clone(), &parent.local_ctx);
    let sub_goal = super::core::Goal {
        meta_id,
        target: target.clone(),
        local_ctx: parent.local_ctx.clone(),
        tag: parent.tag.clone(),
        case_binders: parent.case_binders.clone(),
    };
    state.goals.push_front(sub_goal.clone());
    let outcome = decide_by_evaluation(state, &sub_goal, &target, depth);
    let still_open = state
        .goals
        .front()
        .is_some_and(|goal| goal.meta_id == meta_id);
    if still_open {
        state.goals.pop_front();
    }
    match outcome {
        Ok(EvalOutcome::Closed) if !still_open => match state.metas().get_assignment(meta_id) {
            Some(proof) => {
                let proof = proof.clone();
                SubDecision::Proved(state.metas.instantiate(&proof))
            }
            None => SubDecision::Refused(Refusal::Stuck(
                "a case closed without assigning a proof term".into(),
            )),
        },
        Ok(EvalOutcome::Closed) => SubDecision::Refused(Refusal::Stuck(
            "a case reported closed but its goal is still open".into(),
        )),
        // A nested split's assembled term: its sub-goal was never assigned
        // (popped above), and the outermost split re-checks the whole tree.
        Ok(EvalOutcome::Assembled(proof)) if still_open => {
            SubDecision::Proved(state.metas.instantiate(&proof))
        }
        Ok(EvalOutcome::Assembled(_)) => SubDecision::Refused(Refusal::Stuck(
            "a case assembled a proof but its goal was closed".into(),
        )),
        Ok(EvalOutcome::Disproved(why)) => SubDecision::Refused(Refusal::False(format!(
            "`{}`: {why}",
            crate::error_render::term(&target)
        ))),
        Ok(EvalOutcome::Refused(refusal)) => SubDecision::Refused(refusal),
        Err(error) => SubDecision::Refused(Refusal::Stuck(format!(
            "`{}`: {error}",
            crate::error_render::term(&target)
        ))),
    }
}

/// Run a finite case split on a scratch copy of `state` and commit it only if
/// it closes the goal, so a refusal leaves `state` exactly as it was.
///
/// Nested case splits (`depth > 0`) already run on the outermost split's
/// scratch copy and work in place: one clone per `decide` call, not per case.
fn with_scratch<F>(state: &mut ProofState, depth: usize, split: F) -> EvalOutcome
where
    F: FnOnce(&mut ProofState) -> EvalOutcome,
{
    if depth > 0 {
        return split(state);
    }
    let mut work = state.clone();
    let outcome = split(&mut work);
    if matches!(outcome, EvalOutcome::Closed) {
        // The split closed exactly the one goal it was given; anything else
        // means a case left stray goals behind, which must not be committed.
        if work.goals.len() + 1 != state.goals.len() {
            return EvalOutcome::Refused(Refusal::Stuck(
                "a finite case split left stray goals".into(),
            ));
        }
        *state = work;
    }
    outcome
}

/// Close `goal` in `state` with an assembled case-split proof, re-checked by
/// the kernel (`close_goal` infers strictly and compares against the target).
///
/// Only the OUTERMOST split (`depth == 0`) closes and re-checks; a nested one
/// hands its assembled term up as [`EvalOutcome::Assembled`], so the whole
/// tree is re-checked exactly once, at the root, where it covers every
/// internal node.
fn close_case_split(
    state: &mut ProofState,
    goal: &super::core::Goal,
    proof: Expr,
    what: &str,
    depth: usize,
) -> EvalOutcome {
    if depth > 0 {
        return EvalOutcome::Assembled(proof);
    }
    match state.close_goal(goal, proof) {
        Ok(()) => EvalOutcome::Closed,
        Err(error) => EvalOutcome::Refused(Refusal::Stuck(format!(
            "the kernel rejected the assembled {what} proof: {error}"
        ))),
    }
}

/// Lead-in of a Bool case split's validated counterexample.
const BOOL_COUNTEREXAMPLE_PREFIX: &str = "counterexample (Bool binders, outermost first): ";

/// `true` iff `ty` is the `Bool` type constant.
fn is_bool_type(ty: &Expr) -> bool {
    matches!(ty.strip_mdata().kind(), ExprKind::Const(name, _) if name == &Name::from_string("Bool"))
}

/// Finite `∀` over `Bool`: evaluate `∀ x : Bool, P x` the way Lean's
/// `decide` evaluates core's `Decidable (∀ x : Bool, p x)` instance — decide
/// `P false` and `P true` and combine them.
///
/// Clean's prelude has no `Decidable (∀ x : Bool, p x)` instance, so without
/// this lane every such goal fell through to `smt::decide`, whose bridge
/// treats `&&`, `^^^`, … as uninterpreted functions: the negated goal is then
/// satisfiable in the abstraction and `decide` used to report a
/// "counterexample" for VALID goals such as `∀ a : Bool, (a && true) = a`.
///
/// The proof is `fun x => @Bool.casesOn.{0} (fun x => P x) x h_false h_true`,
/// with each `h_b` produced by the kernel-evaluation rungs (recursively, so
/// nested binders split again) and the whole term re-checked in `close_goal`.
/// Returns `None` when `target` is not a `∀` over `Bool`.
fn try_decide_bool_forall(
    state: &mut ProofState,
    goal: &super::core::Goal,
    target: &Expr,
    depth: usize,
) -> Option<EvalOutcome> {
    let ExprKind::Pi(binder, domain, body) = target.strip_mdata().kind() else {
        return None;
    };
    if !is_bool_type(domain) {
        return None;
    }
    let (domain, body): (&Expr, &Expr) = (domain, body);
    if depth >= MAX_DECIDE_EVAL_DEPTH {
        return Some(EvalOutcome::Refused(Refusal::Stuck(format!(
            "more than {MAX_DECIDE_EVAL_DEPTH} nested finite cases"
        ))));
    }
    Some(with_scratch(state, depth, |work| {
        let mut case_proofs = Vec::with_capacity(2);
        for (ctor, label) in [("Bool.false", "false"), ("Bool.true", "true")] {
            let case_target = body.instantiate(&Expr::const_(Name::from_string(ctor), vec![]));
            match decide_subgoal(work, goal, case_target, depth + 1) {
                SubDecision::Proved(proof) => case_proofs.push(proof),
                SubDecision::Refused(Refusal::False(why)) => {
                    // Nested Bool binders extend one assignment list,
                    // outermost binder first.
                    let assignment = match why.strip_prefix(BOOL_COUNTEREXAMPLE_PREFIX) {
                        Some(inner) => format!("{label}, {inner}"),
                        None => format!("{label}; {why}"),
                    };
                    return EvalOutcome::Refused(Refusal::False(format!(
                        "{BOOL_COUNTEREXAMPLE_PREFIX}{assignment}"
                    )));
                }
                SubDecision::Refused(Refusal::NoInstance) => {
                    return EvalOutcome::Refused(Refusal::Stuck(format!(
                        "case Bool binder := {label}: no `Decidable` instance for `{}`",
                        crate::error_render::term(
                            &body.instantiate(&Expr::const_(Name::from_string(ctor), vec![]))
                        )
                    )));
                }
                SubDecision::Refused(Refusal::Stuck(why)) => {
                    return EvalOutcome::Refused(Refusal::Stuck(format!(
                        "case Bool binder := {label}: {why}"
                    )));
                }
            }
        }
        let (Some(proof_true), Some(proof_false)) = (case_proofs.pop(), case_proofs.pop()) else {
            return EvalOutcome::Refused(Refusal::Stuck("missing Bool case proof".into()));
        };
        // `target` is closed, so `body` has exactly one loose bound variable
        // (the Bool binder) and the motive `fun x => body` is closed. The case
        // proofs are closed too (they live in the goal's local context), so
        // none of them needs lifting under the new binder.
        let motive = Expr::lam(BinderInfo::Default, domain.clone(), body.clone());
        let split = Expr::apps(
            Expr::const_(Name::from_string("Bool.casesOn"), vec![Level::zero()]),
            [motive, Expr::bvar(0), proof_false, proof_true],
        );
        let proof = Expr::lam(*binder, domain.clone(), split);
        close_case_split(work, goal, proof, "Bool case split", depth)
    }))
}

/// `true` iff `ty : Prop` in `goal`'s context.
fn is_proposition(state: &ProofState, goal: &super::core::Goal, ty: &Expr) -> bool {
    state
        .infer_type(goal, ty)
        .map(|sort| {
            matches!(state.whnf(goal, &sort).kind(), ExprKind::Sort(level) if level.is_zero())
        })
        .unwrap_or(false)
}

/// Decidable implication `p → q`: Lean's `decide` evaluates core's
/// `[Decidable p] [Decidable q] : Decidable (p → q)` instance. Decide `q`
/// (then `fun _ => hq`), else decide `¬p` (then `fun h => False.elim (hnp h)`),
/// and report the implication false only when `p` is proved and `q` was
/// evaluated to false. Needed for finite `∀` bodies such as
/// `∀ a b : Bool, a = true → b = true → (a && b) = true`.
///
/// Returns `None` when `target` is not a non-dependent arrow out of a `Prop`.
fn try_decide_implication(
    state: &mut ProofState,
    goal: &super::core::Goal,
    target: &Expr,
    depth: usize,
) -> Option<EvalOutcome> {
    let ExprKind::Pi(binder, hypothesis, conclusion) = target.strip_mdata().kind() else {
        return None;
    };
    let (hypothesis, conclusion): (&Expr, &Expr) = (hypothesis, conclusion);
    if conclusion.has_loose_bvars() || !is_proposition(state, goal, hypothesis) {
        return None;
    }
    if depth >= MAX_DECIDE_EVAL_DEPTH {
        return Some(EvalOutcome::Refused(Refusal::Stuck(format!(
            "more than {MAX_DECIDE_EVAL_DEPTH} nested finite cases"
        ))));
    }
    Some(with_scratch(state, depth, |work| {
        let conclusion_refusal = match decide_subgoal(work, goal, conclusion.clone(), depth + 1) {
            SubDecision::Proved(proof) => {
                // `proof` is closed, so it does not mention the new binder.
                let proof = Expr::lam(*binder, hypothesis.clone(), proof);
                return close_case_split(work, goal, proof, "implication", depth);
            }
            SubDecision::Refused(refusal) => refusal,
        };
        let not_hypothesis = Expr::app(
            Expr::const_(Name::from_string("Not"), vec![]),
            hypothesis.clone(),
        );
        if let SubDecision::Proved(refutation) =
            decide_subgoal(work, goal, not_hypothesis, depth + 1)
        {
            let absurd = Expr::apps(
                Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
                [conclusion.clone(), Expr::app(refutation, Expr::bvar(0))],
            );
            let proof = Expr::lam(*binder, hypothesis.clone(), absurd);
            return close_case_split(work, goal, proof, "implication", depth);
        }
        if let Refusal::False(why) = &conclusion_refusal {
            if let SubDecision::Proved(_) =
                decide_subgoal(work, goal, hypothesis.clone(), depth + 1)
            {
                return EvalOutcome::Refused(Refusal::False(format!(
                    "the hypothesis holds but the conclusion is false: {why}"
                )));
            }
        }
        EvalOutcome::Refused(Refusal::Stuck(format!(
            "neither the conclusion nor the negated hypothesis of `{}` evaluated to true",
            crate::error_render::term(target)
        )))
    }))
}

/// Check if a goal can be closed by ground numeric evaluation.
///
/// Returns `true` if the proposition evaluates to `true` by numeric
/// computation (equality, comparisons for Nat and Int).
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
fn is_numerically_decidable(target: &Expr) -> bool {
    // Comparisons
    if try_eval_comparison(target).is_some() {
        return true;
    }

    // Equalities
    if let Ok((_ty, lhs, rhs, _levels)) = match_equality(target) {
        if eval_nat_expr(&lhs).is_some() && eval_nat_expr(&rhs).is_some() {
            return true;
        }
        if eval_int_expr(&lhs).is_some() && eval_int_expr(&rhs).is_some() {
            return true;
        }
    }

    false
}

/// Lightweight decide tactic for decidable propositions.
///
/// Closes goals that are decidable propositions by:
/// 1. Synthesizing a `Decidable` instance for the goal type
/// 2. Evaluating the decision procedure via WHNF reduction
/// 3. Extracting the proof from `Decidable.isTrue`
///
/// # Supported propositions
///
/// - `True`, `False`
/// - `a = b` where the type has `DecidableEq` (Bool, Nat, Int, finite enums)
/// - Nat/Int comparisons (`<`, `<=`, `>`, `>=`)
/// - Bool operations (via WHNF reduction)
/// - `∀ x : Bool, P x` (finite case split) and `p → q` over decidable parts
///
/// # Algorithm
///
/// 1. Kernel-evaluation rungs (`decide_by_evaluation`): ground numeric fast
///    paths, finite `Bool` case splits, decidable implications, noConfusion
///    disequalities, and a resolved `Decidable` instance reduced by WHNF.
///    Anything these close is closed by a kernel-checked term.
/// 2. Unless evaluation proved the proposition false (then the refusal is
///    final), the SMT `decide` bridge may still close the goal, but only with
///    a kernel-validated proof term.
/// 3. If neither closes it, the error states what evaluation established:
///    the proposition is false (an instance reduced to `isFalse`, or a finite
///    case split found a false case), or no `Decidable` instance resolved,
///    or the instance did not reduce. An SMT satisfying assignment is NEVER
///    reported as a counterexample: the bridge abstracts every operation
///    outside its theories (`&&`, `^^^`, `UInt32` arithmetic, …) as an
///    uninterpreted function, so its models do not witness `¬goal`.
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the current goal is closed with a type-checked proof term
/// ENSURES: On Err, the goal stays open and the error names the refusal reason
pub fn eval_decide(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target = state.metas.instantiate(&goal.target);

    let refusal = match decide_by_evaluation(state, &goal, &target, 0)? {
        EvalOutcome::Closed => return Ok(()),
        // Not produced at depth 0; if it ever is, the term is closed CHECKED.
        EvalOutcome::Assembled(proof) => return state.close_goal(&goal, proof),
        EvalOutcome::Disproved(detail) => {
            return Err(TacticError::InvalidTarget {
                tactic: "decide".into(),
                detail,
            })
        }
        // Kernel evaluation PROVED the proposition false (an instance reduced
        // to `isFalse`, or a finite case split found a false case). No proof
        // exists, so the SMT fallback is not consulted: it could only return
        // a term the kernel must reject. It did exactly that for
        // `∀ b c : Bool, b = true → c = true` — the bridge merged `b` and `c`
        // and reconstructed a proof of `b = true → b = true`, which only
        // `validate_proof_term` stopped (decide review, 2026-09-28).
        EvalOutcome::Refused(Refusal::False(why)) => {
            return Err(Refusal::false_error(&target, &why));
        }
        EvalOutcome::Refused(refusal) => refusal,
    };

    // Fall back to SMT decide (non-decidable / arithmetic goals, or instances
    // that do not kernel-reduce to `isTrue`). It can only CLOSE the goal with a
    // kernel-validated proof term; its failure is reported through `refusal`,
    // never as an SMT "counterexample".
    match super::smt::decide(state) {
        Ok(()) => Ok(()),
        Err(smt_error) => Err(refusal.into_error(&target, &smt_error)),
    }
}

/// The kernel-evaluation rungs of `decide`: every rung except the SMT
/// fallback. `depth` counts enclosing finite case splits (0 at the top).
///
/// REQUIRES: `goal` is the front goal of `state` and `target` its instantiated
/// target.
/// ENSURES: `Closed` iff the goal was closed with a kernel-checked term;
/// `Disproved` / `Refused` leave it open. `Err` is a hard tactic failure.
fn decide_by_evaluation(
    state: &mut ProofState,
    goal: &super::core::Goal,
    target: &Expr,
    depth: usize,
) -> Result<EvalOutcome, TacticError> {
    let goal = goal.clone();
    let target = target.clone();

    // Fast path: True
    if matches!(target.kind(), ExprKind::Const(name, _) if name == &Name::from_string("True")) {
        let proof = Expr::const_(Name::from_string("True.intro"), vec![]);
        return state.close_goal(&goal, proof).map(|()| EvalOutcome::Closed);
    }

    // Finite `∀` over `Bool` and decidable implications: case-split and
    // evaluate each case. A validated false case is final; any other refusal
    // is kept and reported only if no later rung decides the goal.
    type FiniteLane = fn(&mut ProofState, &super::core::Goal, &Expr, usize) -> Option<EvalOutcome>;
    let mut pending_refusal = None;
    for lane in [try_decide_bool_forall as FiniteLane, try_decide_implication] {
        match lane(state, &goal, &target, depth) {
            Some(EvalOutcome::Refused(refusal @ (Refusal::NoInstance | Refusal::Stuck(_)))) => {
                pending_refusal.get_or_insert(refusal);
            }
            Some(outcome) => return Ok(outcome),
            None => {}
        }
    }

    // Fast path: ground numeric equality — try rfl
    if let Ok((_ty, lhs, rhs, _levels)) = match_equality(&target) {
        // Nat equality
        if let (Some(l), Some(r)) = (eval_nat_expr(&lhs), eval_nat_expr(&rhs)) {
            if l == r {
                return rfl(state).map(|()| EvalOutcome::Closed);
            }
            return Ok(EvalOutcome::Disproved(format!(
                "equality is false: {l} != {r}"
            )));
        }
        // Int equality
        if let (Some(l), Some(r)) = (eval_int_expr(&lhs), eval_int_expr(&rhs)) {
            if l == r {
                return rfl(state).map(|()| EvalOutcome::Closed);
            }
            return Ok(EvalOutcome::Disproved(format!(
                "equality is false: {l} != {r}"
            )));
        }
    }

    // Fast path: ground numeric comparisons
    if let Some(result) = try_eval_comparison(&target) {
        if !result {
            return Ok(EvalOutcome::Disproved("comparison is false".into()));
        }
        // Comparison is true — close ground Int `<=` / `<` goals with a
        // constructive `Int.NonNeg.mk` witness. The Int decidability instances
        // (`instDecidableIntLe` / `instDecidableIntLt`) are non-computational
        // axioms, so the WHNF-reduction path below cannot extract a sound proof
        // for Int; without this the goal would fall through to SMT `decide`.
        // Nat comparisons are handled by the existing reduction path.
        if super::norm_num_ext::try_close_int_ground_comparison(state, &goal).is_some() {
            return Ok(EvalOutcome::Closed);
        }
        // Ground Nat `<=` / `<` / `>=` / `>` goals are closed with a
        // constant-size `Nat.le_of_ble_eq_true` witness. The native
        // `Nat.decLe` / `Nat.decLt` reducers emit `Decidable.isTrue sorryAx`,
        // so the WHNF-reduction path below would extract `sorryAx`; the `>` /
        // bare `Nat.gt` / bare `Nat.ge` shapes also have no sound decide path.
        if super::norm_num_ext::try_close_nat_ground_comparison(state, &goal).is_some() {
            return Ok(EvalOutcome::Closed);
        }
        // Otherwise need a proof term from the decide instance (Nat path).
    }

    // Ground disequality `a ≠ b`: Lean's `decide` closes these. Route through
    // the noConfusion disequality builder so the proof stays kernel-checkable
    // and axiom-free (the native `Nat.decEq` reducer only yields
    // `Decidable.isFalse sorryAx`, which is unsound to extract). On failure,
    // fall through to the remaining paths. Part of the tactic-divergence
    // parity work.
    if super::decide_eq::match_ne(&target).is_some()
        && super::decide_eq::try_close_ne_by_noconfusion(state).is_ok()
    {
        return Ok(EvalOutcome::Closed);
    }

    // `Not (Eq α a b)` is definitionally the same proposition as `Ne α a b`,
    // but the surface `Not (a = b)` form does not match the `Ne` head, so the
    // noConfusion lane above is skipped. Route it through the same builder when
    // the operands are distinct decidable constructors. The proof has type
    // `Eq α a b → False`, which is def-eq to `Not (Eq α a b)`; `close_goal`
    // re-checks it against the goal so a true equality cannot be closed here.
    if let Some((ne_ty, lhs, rhs)) = match_not_eq(&target) {
        if super::decide_eq::decidable_type_check(&ne_ty) {
            let eq_level = state
                .infer_type(&goal, &ne_ty)
                .ok()
                .and_then(|sort| match sort.kind() {
                    ExprKind::Sort(level) => Some(level.clone()),
                    _ => None,
                })
                .unwrap_or_else(|| Level::succ(Level::zero()));
            if let Some(ne_proof) = super::decide_eq_noconfusion::build_noconfusion_ne_proof(
                state.env(),
                &ne_ty,
                &lhs,
                &rhs,
                &eq_level,
            ) {
                if state.close_goal(&goal, ne_proof).is_ok() {
                    return Ok(EvalOutcome::Closed);
                }
            }
        }
    }

    // Plain decidable equality `a = b` (e.g. `some 3 = some 3`): route through
    // `decide_eq`, which closes a true equality reflexively / by reduction and
    // builds a kernel-checkable `Decidable.isFalse` (noConfusion) term for a
    // genuinely-false one. For a false equality this returns Err and we fall
    // through to the kernel-reduction lane, whose `isFalse` becomes the
    // refusal reason — the goal stays unproved (sound).
    if let Ok((eq_ty, _lhs, _rhs, _levels)) = match_equality(&target) {
        if super::decide_eq::decidable_type_check(&eq_ty)
            && super::decide_eq::decide_eq(state).is_ok()
        {
            return Ok(EvalOutcome::Closed);
        }
    }

    // BEq shape `(a == b) = true` / `(a == b) = false`: reduce the `BEq.beq`
    // application via WHNF and check it matches the asserted Bool literal. For
    // the supported decidable types `==` δι-reduces to a `Bool` constructor, so
    // the goal becomes a ground `Bool` equality closed reflexively. A mismatch
    // (e.g. `(some 3 == some 4) = true`) leaves the goal for the SMT fallback.
    if try_close_beq_eq_bool(state, &goal, &target).is_ok() {
        return Ok(EvalOutcome::Closed);
    }

    // Try to synthesize a Decidable instance
    if let Some(decidable_expr) = synthesize_decidable(state, &target) {
        // Evaluate via WHNF
        if let Some(proof) = eval_decidable(state, &goal, &decidable_expr) {
            return state.close_goal(&goal, proof).map(|()| EvalOutcome::Closed);
        }
    }

    // Kernel-reduction lane: resolve a `Decidable target` instance via the proper
    // recursive resolver and extract the `isTrue` witness by WHNF. This closes
    // ground decidable goals with a kernel-checked term BEFORE any SMT call,
    // removing `super::smt::decide` (which can embed `trustedAy`) from the TCB for
    // this class. `close_goal` re-checks the witness, so a false goal cannot slip
    // through. An `isFalse` reduction is recorded as the refusal reason; it
    // closes nothing.
    let refusal = match try_decide_by_kernel_reduction(state, &goal, &target) {
        KernelReduction::IsTrue(proof) => {
            return state.close_goal(&goal, proof).map(|()| EvalOutcome::Closed);
        }
        KernelReduction::IsFalse => Refusal::False(format!(
            "its `Decidable` instance reduced to `isFalse` for `{}`",
            crate::error_render::term(&target)
        )),
        KernelReduction::Stuck => pending_refusal
            .unwrap_or_else(|| Refusal::Stuck("the resolved instance did not reduce".into())),
        KernelReduction::NoInstance => pending_refusal.unwrap_or(Refusal::NoInstance),
    };
    Ok(EvalOutcome::Refused(refusal))
}

/// Match `Not (@Eq α a b)` and return `(α, a, b)`.
///
/// REQUIRES: `expr` is a well-formed expression.
/// ENSURES: Returns `Some((α, a, b))` iff `expr` is `Not p` with `p = @Eq α a b`.
fn match_not_eq(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    if let ExprKind::Const(name, _) = head.kind() {
        if name == &Name::from_string("Not") && args.len() == 1 {
            if let Ok((ty, lhs, rhs, _levels)) = match_equality(args[0]) {
                return Some((ty, lhs, rhs));
            }
        }
    }
    None
}

/// Close a `(a == b) = bool_lit` goal by reducing the `BEq.beq` application and
/// comparing against the asserted `Bool` literal.
///
/// Returns `Ok(())` on success (goal closed reflexively after WHNF), and an
/// error otherwise so the caller can fall through to the SMT path.
fn try_close_beq_eq_bool(
    state: &mut ProofState,
    goal: &super::core::Goal,
    target: &Expr,
) -> TacticResult {
    let Ok((_bool_ty, lhs, rhs, _levels)) = match_equality(target) else {
        return Err(TacticError::GoalMismatch("not an equality".into()));
    };
    // One side must be a literal Bool constant; the other the `==` application.
    let is_bool_lit = |e: &Expr| {
        matches!(e.kind(), ExprKind::Const(n, _)
            if n == &Name::from_string("Bool.true") || n == &Name::from_string("Bool.false")
            || n == &Name::from_string("true") || n == &Name::from_string("false"))
    };
    let (beq_app, bool_lit) = if is_bool_lit(&rhs) {
        (lhs, rhs)
    } else if is_bool_lit(&lhs) {
        (rhs, lhs)
    } else {
        return Err(TacticError::GoalMismatch("no Bool literal side".into()));
    };
    // The non-literal side must be a `BEq.beq` / `==` application.
    let head = beq_app.get_app_fn();
    let is_beq = matches!(head.kind(), ExprKind::Const(n, _)
        if n.to_string().contains("BEq.beq") || n.to_string() == "beq");
    if !is_beq {
        return Err(TacticError::GoalMismatch("not a BEq application".into()));
    }
    // Reduce the `==` application and require it to converge with the asserted
    // Bool literal. `rfl` re-derives a kernel-checked proof of the whole
    // `(a == b) = lit` goal; the kernel re-checks it in `close_goal`, so a
    // false claim (where `==` reduces to the other literal) is rejected.
    let reduced = state.whnf(goal, &beq_app);
    if state.is_def_eq(goal, &reduced, &bool_lit) {
        return rfl(state);
    }
    Err(TacticError::GoalMismatch(
        "BEq did not reduce to literal".into(),
    ))
}
