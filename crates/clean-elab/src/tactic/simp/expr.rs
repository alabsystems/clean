// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core simplification engine and expression matching.
//!
//! Contains the recursive `simp_expr` engine, equality extraction, and lemma
//! application with unification. BVar-to-meta conversion is in `pattern.rs`.

use std::collections::HashMap;
use std::sync::LazyLock;

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprFolder, ExprKind, Level, LevelVec, LocalContext};

use crate::stack_safe;
use crate::unify::{MetaState, Unifier, UnifyResult};

/// Pre-interned `Eq` name (avoids repeated allocation in equality extraction).
static EQ_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Eq"));

/// Pre-interned `Iff` name (avoids repeated allocation in iff extraction).
static IFF_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Iff"));

use super::binder::open_binder;
use super::budget::SimpBudget;
use super::match_target::{collapse_nat_ofnat_literals, MatchTarget};
use super::pattern::{convert_bvars_to_metas, substitute_bvars_with_metas};
use super::proof::{
    mk_congr, mk_congr_arg, mk_congr_fun, mk_eq_trans, mk_forall_congr, mk_funext,
    mk_pi_domain_congr,
};
use super::reduce::{beta_reduce, eta_reduce};
use super::simproc::{try_simprocs, SimprocSet};
use super::types::{SimpConfig, SimpLemma, SimpLemmaSet, SimpResult};
use crate::tactic::core::{Goal, ProofState};
use crate::tactic::op_projection::{is_hetero_op_projection, reduce_op_projection_head};

/// Extract lhs = rhs from a lemma type (handles forall quantifiers)
///
/// ENSURES: On Some, returns `(lhs, rhs)` from `@Eq _ lhs rhs` at any Pi-nesting depth
/// ENSURES: On None, `ty` does not contain an equality at any depth
pub fn extract_equality_from_type(ty: &Expr) -> Option<(Expr, Expr)> {
    extract_equality_full(ty).map(|(_, lhs, rhs)| (lhs, rhs))
}

/// Extract (eq_type, lhs, rhs) from a lemma type: `@Eq eq_type lhs rhs`.
/// Handles forall/pi quantifiers by recursing into the body.
///
/// ENSURES: On Some, returns `(α, lhs, rhs)` where `ty` contains `@Eq α lhs rhs`
/// ENSURES: On None, no equality found at any Pi-nesting depth
pub(crate) fn extract_equality_full(ty: &Expr) -> Option<(Expr, Expr, Expr)> {
    stack_safe(|| match ty.kind() {
        ExprKind::App(f, arg) => {
            // Check if this is Eq ty lhs rhs
            if let ExprKind::App(f2, lhs) = f.kind() {
                if let ExprKind::App(eq, eq_ty) = f2.kind() {
                    if let ExprKind::Const(name, _) = eq.kind() {
                        if *name == *EQ_NAME {
                            return Some((
                                eq_ty.as_ref().clone(),
                                lhs.as_ref().clone(),
                                arg.as_ref().clone(),
                            ));
                        }
                    }
                }
            }
            None
        }
        ExprKind::Pi(_bi, _ty, body) => {
            // Recurse into forall/pi body
            extract_equality_full(body)
        }
        _ => None,
    })
}

/// Count a lemma type's leading `Pi` binders without allocating.
///
/// The allocation-free counterpart to [`collect_binder_types_in_conclusion`],
/// used to skip that (cloning, lifting) walk entirely for the overwhelmingly
/// common case of an unconditional lemma whose every binder the LHS match
/// already determined.
///
/// ENSURES: agrees with `collect_binder_types_in_conclusion(ty).len()`.
pub(crate) fn leading_pi_binder_count(ty: &Expr) -> usize {
    let mut count = 0;
    let mut current = ty;
    while let ExprKind::Pi(_bi, _domain, body) = current.kind() {
        count += 1;
        current = body;
    }
    count
}

/// Collect the types of a lemma's leading `Pi` binders, re-expressed in the
/// **conclusion's** de Bruijn context.
///
/// `extract_equality_full` strips every leading `Pi` before reading off
/// `@Eq α lhs rhs`, so the indices in the returned `lhs`/`rhs` count binders
/// from the innermost outwards: with `∀ (a b : Nat) (h : b ≤ a), a - b + b = a`,
/// `h` is `BVar 0`, `b` is `BVar 1` and `a` is `BVar 2`. This function returns
/// the binder *types* under the SAME indexing, so `result[i]` is the type of
/// `BVar i` as it appears in the conclusion — which is exactly the indexing
/// `convert_bvars_to_metas` / `substitute_bvars_with_metas` use.
///
/// Each binder's declared type lives in its own (shorter) context, so it is
/// lifted: binder `k` counted from the OUTSIDE, of `n` total, is `BVar n-1-k`
/// in the conclusion and its domain must be lifted by `n - k`. For the example
/// above, `h`'s domain `b ≤ a` is stored as `BVar 0 ≤ BVar 1` at its own binder
/// and becomes `BVar 1 ≤ BVar 2` here.
///
/// ENSURES: `result.len()` equals the number of leading `Pi` binders of `ty`
///   — the same count `extract_equality_full` / `extract_iff_with_binders`
///   strip, so the two are always in agreement.
/// ENSURES: `result[i]` has no BVar referring to a binder this lemma does not
///   have (every loose index is `< result.len()`).
pub(crate) fn collect_binder_types_in_conclusion(ty: &Expr) -> Vec<Expr> {
    // Outermost-first, each domain in its own context.
    let mut outer = Vec::with_capacity(leading_pi_binder_count(ty));
    let mut current = ty;
    while let ExprKind::Pi(_bi, domain, body) = current.kind() {
        outer.push(domain.as_ref().clone());
        current = body;
    }

    let total = outer.len();
    // `total - k` never underflows (`k < total`); reversing turns the
    // outermost-first walk into the innermost-first (= BVar-index) order.
    outer
        .into_iter()
        .enumerate()
        .map(|(k, domain)| domain.lift((total - k) as u32))
        .rev()
        .collect()
}

/// Extract `(lhs, rhs)` from a lemma type whose conclusion is `Iff lhs rhs`.
///
/// Handles forall/pi quantifiers by recursing into the body, mirroring
/// `extract_equality_full`. In Lean 4 an `@[simp]` lemma whose conclusion is a
/// biconditional `a ↔ b` is usable as a rewrite from `a` to `b`: the iff is
/// symmetric, so rewriting `a` to `b` is sound and matches upstream
/// `Lean/Meta/Tactic/Simp/SimpTheorems.lean`, which converts an `Iff`
/// conclusion into an `Eq` rewrite via `propext`.
///
/// ENSURES: On Some, returns `(lhs, rhs)` where `ty` concludes in `Iff lhs rhs`
///   at some Pi-nesting depth.
/// ENSURES: On None, no top-level `Iff` application is found at any depth.
pub(crate) fn extract_iff_full(ty: &Expr) -> Option<(Expr, Expr)> {
    stack_safe(|| match ty.kind() {
        // Iff lhs rhs is represented as App(App(Iff, lhs), rhs).
        ExprKind::App(f, rhs) => {
            if let ExprKind::App(iff, lhs) = f.kind() {
                if let ExprKind::Const(name, _) = iff.kind() {
                    if *name == *IFF_NAME {
                        return Some((lhs.as_ref().clone(), rhs.as_ref().clone()));
                    }
                }
            }
            None
        }
        ExprKind::Pi(_bi, _ty, body) => extract_iff_full(body),
        _ => None,
    })
}

/// Extract `(binder_count, lhs, rhs)` from a lemma type concluding in
/// `Iff lhs rhs` under `binder_count` leading forall/pi binders.
///
/// The de Bruijn indices in the returned `lhs`/`rhs` refer to the same binders,
/// so the count is exactly what `mk_iff_rewrite_proof_template` needs to
/// reconstruct the lemma application.
///
/// ENSURES: On Some, `ty` strips `binder_count` leading `Pi`s to reach an
///   `Iff lhs rhs` application.
/// ENSURES: On None, the (binder-stripped) conclusion is not an `Iff`.
pub(crate) fn extract_iff_with_binders(ty: &Expr) -> Option<(u32, Expr, Expr)> {
    let mut binder_count = 0u32;
    let mut current = ty;
    while let ExprKind::Pi(_, _, body) = current.kind() {
        binder_count += 1;
        current = body;
    }
    let (lhs, rhs) = extract_iff_full(current)?;
    Some((binder_count, lhs, rhs))
}

/// Build an `Eq`-typed rewrite proof template for a simp lemma whose conclusion
/// is `Iff lhs rhs` (possibly under `binder_count` leading forall binders).
///
/// The resulting expression has type `lhs = rhs` (a `Prop` equality) and is
/// stored as the lemma's `proof_expr`, so the rest of the simp engine — which
/// only knows how to consume `Eq` proofs — can use the iff lemma uniformly.
///
/// Construction (de Bruijn indices `0..binder_count` refer to the lemma's
/// universally-quantified arguments, matching `lemma.lhs`/`lemma.rhs`):
///
/// ```text
/// let h    := name (BVar binder_count-1) ... (BVar 0)   -- h : lhs ↔ rhs
/// propext lhs rhs (Iff.mp lhs rhs h) (Iff.mpr lhs rhs h) : lhs = rhs
/// ```
///
/// where Clean's `propext : {a b : Prop} → (a → b) → (b → a) → a = b`.
///
/// # Soundness
///
/// `propext` applied to the two directions extracted from a real `Iff` witness
/// yields a genuine `Eq` proof; no axiom beyond the foundational `propext` is
/// introduced. The rewrite is symmetric (iff/eq), so registering `lhs → rhs` is
/// valid. We never synthesize a reverse direction for one-directional
/// implications: only conclusions that are actually `Iff` reach this path.
///
/// REQUIRES: `lhs` and `rhs` are the iff sides extracted from the lemma type,
///   expressed over the same `binder_count` de Bruijn binders as `lemma.lhs`.
/// ENSURES: The returned template, after bvar→meta substitution and
///   instantiation, type-checks to `lhs = rhs`.
pub(crate) fn mk_iff_rewrite_proof_template(
    lemma_name: &Name,
    binder_count: u32,
    lhs: &Expr,
    rhs: &Expr,
    level_params: &[Name],
) -> Expr {
    // h := name applied to its binder arguments (outermost binder first).
    //
    // The head MUST carry one level argument per declared level parameter:
    // emitting `Expr::const_(name, vec![])` for a universe-polymorphic `Iff`
    // lemma (`forall_const.{u} (α : Sort u) …`) produced
    // `LevelCountMismatch { expected: 1, got: 0 }`, and where the counts
    // happened to line up it landed a `Sort u` domain in a `Prop` binder slot
    // — the `forall₂_true_iff` failure. Spelling each parameter by its own
    // name keeps the template a faithful stand-in for the declaration; the
    // rewrite path instantiates them from the match (see
    // `resolve_lemma_level`) and any that stay unsolved are refused there.
    let levels: Vec<Level> = level_params.iter().cloned().map(Level::param).collect();
    let mut h = Expr::const_(lemma_name.clone(), levels);
    for idx in (0..binder_count).rev() {
        h = Expr::app(h, Expr::bvar(idx));
    }

    // propext lhs rhs h : lhs = rhs
    //
    // `propext : {a b : Prop} → (a ↔ b) → a = b` takes the `Iff` proof `h`
    // directly (see `clean-kernel/src/env/logic.rs::init_propext`). The previous
    // form extracted `Iff.mp`/`Iff.mpr` and applied `propext` to both as if its
    // signature were `(a → b) → (b → a) → a = b`; the resulting term was ill-typed,
    // so `proof_matches_rewrite` rejected it and simp reported NoProgress for
    // `Iff` lemmas.
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("propext"), vec![]),
                lhs.clone(),
            ),
            rhs.clone(),
        ),
        h,
    )
}

/// Extract LHS and RHS from an equality expression (Eq T lhs rhs)
///
/// This is used for transitivity rewriting where we want to rewrite
/// just the LHS of an equality goal.
///
/// ENSURES: On Some, returns `(lhs, rhs)` from `@Eq _ lhs rhs` (top-level only, no Pi recursion)
/// ENSURES: On None, `expr` is not a top-level equality application
pub(crate) fn extract_eq_sides(expr: &Expr) -> Option<(Expr, Expr)> {
    extract_eq_parts(expr).map(|(_, lhs, rhs)| (lhs, rhs))
}

/// Extract the equality type, LHS, and RHS from a top-level equality expression.
///
/// Returns `(eq_type, lhs, rhs)` from `@Eq eq_type lhs rhs`.
/// Unlike `extract_equality_full`, does NOT recurse into Pi bodies.
///
/// ENSURES: On Some, returns `(α, lhs, rhs)` where `expr` is `@Eq α lhs rhs`
/// ENSURES: On None, `expr` is not a top-level equality application
pub(crate) fn extract_eq_parts(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    // Eq T lhs rhs is represented as App(App(App(Eq, T), lhs), rhs)
    if let ExprKind::App(f, rhs) = expr.kind() {
        if let ExprKind::App(f2, lhs) = f.kind() {
            if let ExprKind::App(eq, ty) = f2.kind() {
                if let ExprKind::Const(name, _) = eq.kind() {
                    if *name == *EQ_NAME {
                        return Some((
                            ty.as_ref().clone(),
                            lhs.as_ref().clone(),
                            rhs.as_ref().clone(),
                        ));
                    }
                }
            }
        }
    }
    None
}

/// Construct an equality expression with new LHS
///
/// REQUIRES: `original` is `@Eq α old_lhs old_rhs`
/// ENSURES: Returns `@Eq α new_lhs rhs` preserving the type from `original`
/// ENSURES: If `original` is not an equality, returns `original` unchanged (fallback)
pub(crate) fn make_eq_expr(original: &Expr, new_lhs: &Expr, rhs: &Expr) -> Expr {
    // Extract type and Eq constant from original
    if let ExprKind::App(f, _old_rhs) = original.kind() {
        if let ExprKind::App(f2, _old_lhs) = f.kind() {
            if let ExprKind::App(eq_const, ty) = f2.kind() {
                // Reconstruct: Eq ty new_lhs rhs
                // Note: eq_const and ty are Arc<Expr>, need to dereference
                return Expr::app(
                    Expr::app(
                        Expr::app((**eq_const).clone(), (**ty).clone()),
                        new_lhs.clone(),
                    ),
                    rhs.clone(),
                );
            }
        }
    }
    // Fallback: return original if structure doesn't match
    original.clone()
}

/// Simplify an expression using simp lemmas, under a fresh per-call budget.
///
/// This is the entry point for callers that own a whole traversal and have no
/// budget of their own to charge it to (`simp at`, `simp_rw`, the cast-lemma
/// rewriter, tests). Each call gets its own [`SimpBudget`] sized from `expr`,
/// so a runaway inside ONE traversal is bounded here rather than only between
/// top-level `simp` steps — see [`super::budget`] for the measurement that
/// motivated it.
///
/// A budget trip unwinds to `SimpResult::refl(expr)`: the caller sees "no
/// change", which every one of them already reports as `NoProgress`. Callers
/// that want to distinguish "nothing to do" from "refused, out of budget" —
/// [`super::simp`] does — must own the budget and use
/// [`simp_expr_budgeted`].
///
/// ENSURES: identical to [`simp_expr_budgeted`] with a fresh
///   `SimpBudget::for_target(expr)`.
pub(crate) fn simp_expr(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
) -> SimpResult {
    let budget = SimpBudget::for_target(expr);
    simp_expr_budgeted(state, goal, expr, lemmas, config, &budget)
}

/// One frame of the simp traversal, charged to `budget`.
///
/// Every recursive descent, every re-entrant condition/discharge simp, and the
/// top-level step in [`super::simp`] go through here, so one budget object sees
/// the whole traversal.
///
/// # Fail-closed unwind
///
/// A tripped budget is answered with `SimpResult::refl(expr)` — the frame's own
/// INPUT, with no proof — at three points: before any work is done, after the
/// body returns, and when the body's own result is too large. Since the check
/// runs on the way out of every frame, a trip deep in the recursion unwinds the
/// entire traversal to the original term: no partial rewrite survives, no
/// congruence proof is assembled over a term the budget refused, and the
/// caller's `state` is untouched. [`super::simp`] then turns the trip into
/// [`crate::tactic::TacticError::BudgetExceeded`].
///
/// ENSURES: on a budget trip, `result.expr == *expr` and `result.proof` is
///   `None`.
/// ENSURES: when the budget does not trip, the result is exactly what the
///   unbudgeted traversal produced.
pub(crate) fn simp_expr_budgeted(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
    budget: &SimpBudget,
) -> SimpResult {
    // (1) Refuse to start a frame we cannot pay for.
    if !budget.tick() {
        return SimpResult::refl(expr.clone());
    }

    let result = simp_expr_inner(state, goal, expr, lemmas, config, budget);

    // (2) A trip anywhere below unwinds this frame to its own input.
    if budget.is_tripped() {
        return SimpResult::refl(expr.clone());
    }

    // (3) The growth check, at the frame that produced the growth. `admit`
    // trips the budget on failure, so every enclosing frame unwinds too.
    if result.expr != *expr && !budget.admit(&result.expr) {
        return SimpResult::refl(expr.clone());
    }

    result
}

/// The body of one simp traversal frame. Call [`simp_expr_budgeted`], never
/// this: the budget checks that make a runaway fail closed live in the wrapper.
///
/// Returns a `SimpResult` where:
/// - `expr` is the simplified expression
/// - `proof` is `Some(p)` with `p : original = expr` for propositional changes
///   (lemma rewrites, congruence), or `None` for definitional-only changes
///   (beta/eta reduction) or no change at all.
///
/// # Contract
///
/// REQUIRES: `goal` is a valid goal with correct local context
/// REQUIRES: `lemmas` contains well-typed simp lemmas with valid LHS/RHS patterns
/// REQUIRES: `config` specifies which reduction strategies to apply (beta, eta)
/// ENSURES: `result.expr` is definitionally equal to `expr` (modulo lemma rewrites)
/// ENSURES: If `result.proof` is `Some(p)`, then `p : expr = result.expr`
/// ENSURES: If `result.proof` is `None`, changes are definitional only (beta/eta)
/// ENSURES: Recursion terminates via `stack_safe` guards on subexpression traversal
fn simp_expr_inner(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
    budget: &SimpBudget,
) -> SimpResult {
    // First try beta/eta reduction (definitional — no proof term needed)
    let mut result = SimpResult::refl(expr.clone());

    // Delta-unfold user-requested definitions (#3518).
    //
    // `simp [foo]` where `foo : α → β → γ := <body>` is a `Declaration::Definition`
    // should unfold each occurrence of `foo` to its body. The substitution is
    // definitional (by `Declaration::Definition` semantics) so `proof: None`
    // is correct. Beta reduction below then collapses the resulting redexes so
    // monadic unfolds like `StateT.bind` settle to a normal form.
    // The three definitional rewrites below are the ones the traversal
    // RECURSES THROUGH (everything else returns immediately and is size-checked
    // by `simp_expr_budgeted` on the way out). A `simp [f]` whose unfold body
    // mentions `f` again re-exposes `f` in the children this frame is about to
    // descend into, so a term that grows here grows once per level for as long
    // as the descent lasts. Charging each of them to the budget BEFORE
    // descending is what stops that at the size limit instead of at the
    // machine's memory.
    if !config.unfold_defs.is_empty() {
        let unfolded = unfold_named_consts(&result.expr, &config.unfold_defs);
        if unfolded != result.expr {
            if !budget.admit(&unfolded) {
                return SimpResult::refl(expr.clone());
            }
            result = SimpResult {
                expr: unfolded,
                proof: None,
            };
        }
    }

    if config.beta {
        let beta_reduced = beta_reduce(&result.expr);
        if beta_reduced != result.expr {
            if !budget.admit(&beta_reduced) {
                return SimpResult::refl(expr.clone());
            }
            result = SimpResult {
                expr: beta_reduced,
                proof: None,
            };
        }
    }

    if config.eta {
        let eta_reduced = eta_reduce(&result.expr);
        if eta_reduced != result.expr {
            if !budget.admit(&eta_reduced) {
                return SimpResult::refl(expr.clone());
            }
            result = SimpResult {
                expr: eta_reduced,
                proof: None,
            };
        }
    }

    // POST-ORDER REWRITE (Lean parity, 2026-08-28): node-level lemma rewriting
    // runs AFTER the node's children are simplified, matching Lean's
    // post-method rewriting. Measured against real Lean v4.30.0-rc2
    // (`trace.Meta.Tactic.simp.rewrite`, g_simp probe 30): on
    // `(a && (a && b)) = (a && b)` Lean fires `Bool.and_self_left` INSIDE the
    // equation and never applies the root-level `Bool.and_eq_right_iff_imp`,
    // while node-first order fired the root iff lemma the moment the
    // subtree-aware star skip made it visible, driving the goal into an
    // implication normal form that neither Lean's simp nor Clean's can close.
    // Children-first is the order that makes the two agree.
    let result = simp_children(state, goal, result, lemmas, config, budget);
    if budget.is_tripped() {
        return result;
    }

    // Try to apply simp lemmas at the top level (produces a real proof term).
    // Guard: skip matches that produce the same expression — this can happen when the
    // unifier WHNF-reduces the pattern (e.g. `Nat.add ?n 0` → `?n`) and the meta
    // absorbs the entire target, yielding an identity rewrite.
    let match_target = MatchTarget::new(state, goal, &result.expr);
    for lemma in lemmas.candidates(state, goal, &result.expr) {
        if let Some((new_expr, proof)) = try_apply_simp_lemma_with_proof(
            state,
            goal,
            &match_target,
            lemma,
            lemmas,
            config,
            budget,
        ) {
            if new_expr != result.expr {
                // Diagnostic sibling of `CLEAN_SIMP_HEAD_GUARD_TRACE`: print
                // every FIRED lemma rewrite (stderr), so a non-converging
                // fixpoint can be read as a sequence instead of inferred from
                // refusal counts. Trace-only; never changes the verdict.
                if std::env::var_os("CLEAN_SIMP_REWRITE_TRACE").is_some() {
                    eprintln!(
                        "simp-rewrite: lemma={} from={:?} to={new_expr:?}",
                        lemma.name, result.expr
                    );
                }
                let step = SimpResult {
                    expr: new_expr,
                    proof: Some(proof),
                };
                return mk_eq_trans(result, step, state, goal);
            }
        }
    }

    // Try simprocs (simplification procedures) at the top level.
    // Simprocs evaluate ground expressions like `2 + 3 → 5`.
    // They fire after lemma rewrites but before recursing into subexpressions.
    if config.use_simprocs {
        // Use a thread-local cached simproc set to avoid rebuilding on every call.
        thread_local! {
            static BUILTIN_SIMPROCS: SimprocSet = super::simproc::builtin_simprocs();
        }
        let simproc_result =
            BUILTIN_SIMPROCS.with(|simprocs| try_simprocs(state, goal, &result.expr, simprocs));
        if let Some(sp_result) = simproc_result {
            if sp_result.expr != result.expr {
                return mk_eq_trans(result, sp_result, state, goal);
            }
        }
    }

    result
}

/// The child-recursion phase of one simp frame: recurse into subexpressions,
/// building congruence proofs. Returns the frame's input `result` untouched
/// when no child changed. Split out of `simp_expr_inner` so the node-level
/// lemma/simproc rewriting can run AFTER it (post-order, Lean parity).
fn simp_children(
    state: &ProofState,
    goal: &Goal,
    result: SimpResult,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
    budget: &SimpBudget,
) -> SimpResult {
    match result.expr.kind() {
        ExprKind::App(f, arg) => {
            // ite-condition congruence (dependent-`Decidable` aware). When the
            // App spine is a fully-applied `@ite α c inst t e` and simp rewrites
            // the condition `c` to `True`/`False`, collapse to the taken branch
            // via the kernel-checked `if_pos`/`if_neg` (keeping the ORIGINAL
            // symbolic `inst` on the LHS). This MUST run before the generic
            // `(f, arg)` split: the generic congrArg path would rewrite only the
            // condition arg and leave the sibling `inst : Decidable c` stale at
            // `Decidable c` while the condition moved to `True`, producing an
            // ill-typed `@congrArg` equation the kernel later rejects. See
            // `try_simp_ite` for the soundness argument.
            if let Some(ite_step) = try_simp_ite(state, goal, &result.expr, lemmas, config, budget)
            {
                return mk_eq_trans(result, ite_step, state, goal);
            }

            let f_result =
                stack_safe(|| simp_expr_budgeted(state, goal, f, lemmas, config, budget));
            let arg_result =
                stack_safe(|| simp_expr_budgeted(state, goal, arg, lemmas, config, budget));
            let f_changed = f_result.expr != **f;
            let arg_changed = arg_result.expr != **arg;

            if f_changed || arg_changed {
                let app_expr = Expr::app(f_result.expr.clone(), arg_result.expr.clone());
                // Build congruence proof from sub-proofs
                let app_proof = match (&f_result.proof, &arg_result.proof) {
                    (Some(h_f), Some(h_a)) => mk_congr(
                        state,
                        goal,
                        f,
                        &f_result.expr,
                        arg,
                        &arg_result.expr,
                        h_f,
                        h_a,
                    ),
                    (Some(h_f), None) => mk_congr_fun(state, goal, f, &f_result.expr, arg, h_f),
                    (None, Some(h_a)) => mk_congr_arg(state, goal, f, arg, &arg_result.expr, h_a),
                    (None, None) => None, // definitional change only
                };
                // Defense-in-depth: a generic App-congruence proof can be
                // ill-typed when the App head is dependently typed in the
                // rewritten argument (e.g. an `ite` whose `Decidable`-instance
                // sibling goes stale — the exact `ite_congruence_gap` defect).
                // `try_simp_ite` above already handles the `ite` case soundly,
                // but for any other dependent head we must not emit a congrArg
                // proof the kernel would reject. Gate the assembled proof through
                // `proof_matches_rewrite` on closed terms; on mismatch fall back
                // to refl (proof: None) so the App-recursion fails closed inside
                // simp (NoProgress) instead of relying on the downstream kernel
                // re-check. Open terms (loose BVars under a binder) keep the
                // baseline behaviour since `infer_type` is unreliable there.
                let app_proof = match app_proof {
                    Some(p)
                        if !app_expr.has_loose_bvars()
                            && !p.has_loose_bvars()
                            && !proof_matches_rewrite(state, goal, &p, &result.expr, &app_expr) =>
                    {
                        None
                    }
                    other => other,
                };
                // If the guard dropped the proof but the expression genuinely
                // changed, the change must be definitional for the result to be
                // sound; if it is not (proof was required), `mk_eq_trans` will
                // carry `None` and `close_goal`/the kernel re-check remains the
                // backstop. We never emit the rejected proof.
                let app_result = SimpResult {
                    expr: app_expr,
                    proof: app_proof,
                };
                return mk_eq_trans(result, app_result, state, goal);
            }
        }
        ExprKind::Lam(bi, ty, body) => {
            // Open the binder with a fresh fvar (see `simp::binder`): every
            // congruence builder below needs `infer_type`, and the kernel
            // cannot type a term with loose BVars. Without this, any redex
            // mentioning an enclosing binder rewrote with `proof: None` and
            // `replace_target_def_eq` then rejected the whole simp step.
            let opened = open_binder(goal, ty, body);
            let body_result = stack_safe(|| {
                simp_expr_budgeted(state, &opened.goal, &opened.body, lemmas, config, budget)
            });
            if body_result.expr != opened.body {
                let new_body = body_result.expr.abstract_fvar(opened.fvar);
                // Build funext proof when body has a proof term
                let lam_proof = body_result
                    .proof
                    .as_ref()
                    .map(|bp| bp.abstract_fvar(opened.fvar))
                    .and_then(|bp| mk_funext(state, goal, ty, body, &new_body, &bp));
                let lam_result = SimpResult {
                    expr: Expr::lam(*bi, ty.as_ref().clone(), new_body),
                    proof: lam_proof,
                };
                return mk_eq_trans(result, lam_result, state, goal);
            }
        }
        ExprKind::Pi(bi, ty, body) => {
            let ty_result =
                stack_safe(|| simp_expr_budgeted(state, goal, ty, lemmas, config, budget));
            if ty_result.expr != **ty {
                let pi_proof = ty_result.proof.as_ref().and_then(|tp| {
                    mk_pi_domain_congr(state, goal, *bi, ty, &ty_result.expr, body, tp)
                });
                let pi_result = SimpResult {
                    expr: Expr::pi(*bi, ty_result.expr, body.as_ref().clone()),
                    proof: pi_proof,
                };
                return mk_eq_trans(result, pi_result, state, goal);
            }

            // Same binder discipline as the Lam arm: `mk_forall_congr` needs
            // `infer_type` on the body, which is open until the binder is
            // replaced by a fresh fvar in an extended local context.
            let opened = open_binder(goal, ty, body);
            let body_result = stack_safe(|| {
                simp_expr_budgeted(state, &opened.goal, &opened.body, lemmas, config, budget)
            });
            if body_result.expr != opened.body {
                let new_body = body_result.expr.abstract_fvar(opened.fvar);
                // Build forall_congr + propext proof when body has a proof term
                // and the Pi type is Prop-valued. Falls back to proof: None
                // (definitional) for non-Prop Pi or when body proof is absent.
                let pi_proof = body_result
                    .proof
                    .as_ref()
                    .map(|bp| bp.abstract_fvar(opened.fvar))
                    .and_then(|bp| mk_forall_congr(state, goal, ty, body, &new_body, &bp));
                let pi_result = SimpResult {
                    expr: Expr::pi(*bi, ty.as_ref().clone(), new_body),
                    proof: pi_proof,
                };
                return mk_eq_trans(result, pi_result, state, goal);
            }
        }
        ExprKind::Let(name, ty, val, body, non_dep) => {
            let val_result =
                stack_safe(|| simp_expr_budgeted(state, goal, val, lemmas, config, budget));
            let body_result =
                stack_safe(|| simp_expr_budgeted(state, goal, body, lemmas, config, budget));
            if val_result.expr != **val || body_result.expr != **body {
                let let_result = SimpResult {
                    expr: Expr::let_named(
                        name.clone(),
                        ty.as_ref().clone(),
                        val_result.expr,
                        body_result.expr,
                        *non_dep,
                    ),
                    proof: None,
                };
                return mk_eq_trans(result, let_result, state, goal);
            }
        }
        ExprKind::Proj(name, idx, inner) => {
            let inner_result =
                stack_safe(|| simp_expr_budgeted(state, goal, inner, lemmas, config, budget));
            if inner_result.expr != **inner {
                // Build congruence: f = (fun x : T => Proj(name, idx, x)), then congrArg f h
                let proj_proof = inner_result.proof.as_ref().and_then(|h| {
                    let inner_ty = state.infer_type(goal, inner).ok()?;
                    let f = Expr::lam(
                        BinderInfo::Default,
                        inner_ty,
                        Expr::proj(name.clone(), *idx, Expr::bvar(0)),
                    );
                    mk_congr_arg(state, goal, &f, inner, &inner_result.expr, h)
                });
                let proj_result = SimpResult {
                    expr: Expr::proj(name.clone(), *idx, inner_result.expr),
                    proof: proj_proof,
                };
                return mk_eq_trans(result, proj_result, state, goal);
            }
        }
        ExprKind::MData(_mdata, inner) => {
            // MData is semantically transparent (def-eq to inner via WHNF).
            // Recurse into the inner expression; proof carries through unchanged.
            let inner_result =
                stack_safe(|| simp_expr_budgeted(state, goal, inner, lemmas, config, budget));
            let strip_result = SimpResult {
                expr: inner_result.expr,
                proof: inner_result.proof,
            };
            return mk_eq_trans(result, strip_result, state, goal);
        }
        _ => {}
    }

    result
}

/// Peel a fully-applied `@ite.{u} α c inst t e` into its five arguments plus the
/// universe level `u` carried by the `ite` head constant.
///
/// Returns `Some((u, α, c, inst, t, e))` when `expr` is exactly the 5-argument
/// `ite` spine (head `Const("ite", [u])`), else `None`. Partial applications and
/// non-`ite` heads return `None`, so the caller never mistakes a curried `ite`
/// for a fully-decided one.
fn peel_ite(expr: &Expr) -> Option<(Level, Expr, Expr, Expr, Expr, Expr)> {
    // @ite α c inst t e = App(App(App(App(App(ite, α), c), inst), t), e)
    let ExprKind::App(f4, e) = expr.kind() else {
        return None;
    };
    let ExprKind::App(f3, t) = f4.kind() else {
        return None;
    };
    let ExprKind::App(f2, inst) = f3.kind() else {
        return None;
    };
    let ExprKind::App(f1, c) = f2.kind() else {
        return None;
    };
    let ExprKind::App(head, alpha) = f1.kind() else {
        return None;
    };
    let ExprKind::Const(name, levels) = head.kind() else {
        return None;
    };
    if name.to_string() != "ite" {
        return None;
    }
    let u = levels.first().cloned()?;
    Some((
        u,
        alpha.as_ref().clone(),
        c.as_ref().clone(),
        inst.as_ref().clone(),
        t.as_ref().clone(),
        e.as_ref().clone(),
    ))
}

/// ite-condition congruence under a dependent `Decidable` instance.
///
/// When `expr` is a fully-applied `@ite.{u} α c inst t e` and simp rewrites the
/// condition `c` to `True` (resp. `False`), collapse the `ite` to its taken
/// branch `t` (resp. `e`) via the kernel-checked, axiom-free `if_pos`/`if_neg`
/// lemmas. Returns the branch value paired with the collapse proof, or `None`
/// when no sound collapse applies.
///
/// # Why not generic congruence
///
/// `ite` is dependently typed in its condition: `@ite α c : Decidable c → α → α
/// → α`, so `@ite α c` and `@ite α True` have DIFFERENT Pi types. Rewriting only
/// the condition argument via `congrArg` (as the generic App recursion does)
/// leaves the sibling `inst : Decidable c` stale, yielding an ill-typed term the
/// kernel rejects. `if_pos`/`if_neg` instead keep the ORIGINAL symbolic `c` and
/// `inst` on the equation's LHS (`@ite α c inst t e = t`) and collapse straight
/// to the branch value on the RHS, so no fresh `Decidable c'` is ever needed.
///
/// # Soundness
///
/// `if_pos`/`if_neg` are real prelude theorems with empty domain-axiom closure.
/// - `if_pos` fires only when the condition provably rewrites to `True`
///   (witnessed by `h₁ : c = True`), from which `hc := @Eq.mpr.{0} c True h₁
///   True.intro : c` is a genuine proof of the condition.
/// - `if_neg` fires only when `h₁ : c = False`, from which `hnc := @Eq.mp.{0} c
///   False h₁ : c → False` is a genuine refutation.
/// The assembled equation is re-checked by `close_goal` and the final kernel
/// `add_decl`, so a wrong instance/branch/cast cannot pass. A false goal such as
/// `if n = n then False else True` (= `False`) collapses to its THEN-branch
/// `False`, leaving an unprovable `⊢ False` — simp makes progress but cannot
/// close it.
///
/// REQUIRES: `expr` is the expression at a `simp_expr` `ExprKind::App` arm.
/// ENSURES: On `Some(r)`, `r.proof = Some(p)` with `p : expr = r.expr` where
///   `r.expr` is the taken branch; `r.expr` is `t` (then) or `e` (else).
/// ENSURES: On `None`, `expr` is not a collapsible `ite` (not a 5-arg `ite`
///   spine, or the condition does not simp to `True`/`False`).
fn try_simp_ite(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
    budget: &SimpBudget,
) -> Option<SimpResult> {
    let (u, alpha, c, inst, t, e) = peel_ite(expr)?;

    // Simplify ONLY the condition. A genuine rewrite to True/False always
    // carries a proof `h₁ : c = c'`; if the condition is already syntactically
    // `True`/`False` the top-level `ite_true`/`ite_false` lemma handles it, so
    // requiring `Some(h1)` here loses no coverage and avoids fabricating a proof
    // for a non-change.
    let cond_result = stack_safe(|| simp_expr_budgeted(state, goal, &c, lemmas, config, budget));
    let h1 = cond_result.proof.as_ref()?;

    let true_c = Expr::const_(Name::from_string("True"), vec![]);
    let false_c = Expr::const_(Name::from_string("False"), vec![]);

    // Universe level for `if_pos`/`if_neg` is the level of α (the result type),
    // exactly the `u` carried by the `@ite.{u}` head. `Eq.mp`/`Eq.mpr` operate
    // on `c`/`True`/`False : Prop = Sort 0`, so they are instantiated at level 0.
    if cond_result.expr == true_c {
        // hc := @Eq.mpr.{0} c True h₁ True.intro : c
        let hc = Expr::apps(
            Expr::const_(Name::from_string("Eq.mpr"), vec![Level::zero()]),
            [
                c.clone(),
                true_c.clone(),
                h1.clone(),
                Expr::const_(Name::from_string("True.intro"), vec![]),
            ],
        );
        // @if_pos.{u} {c} {inst} hc {α} {t} {e} : @ite α c inst t e = t  (Lean order)
        let proof = Expr::apps(
            Expr::const_(Name::from_string("if_pos"), vec![u]),
            [c, inst, hc, alpha, t.clone(), e],
        );
        return Some(SimpResult {
            expr: t,
            proof: Some(proof),
        });
    }

    if cond_result.expr == false_c {
        // hnc := @Eq.mp.{0} c False h₁ : c → False
        let hnc = Expr::apps(
            Expr::const_(Name::from_string("Eq.mp"), vec![Level::zero()]),
            [c.clone(), false_c.clone(), h1.clone()],
        );
        // @if_neg.{u} {c} {inst} hnc {α} {t} {e} : @ite α c inst t e = e  (Lean order)
        let proof = Expr::apps(
            Expr::const_(Name::from_string("if_neg"), vec![u]),
            [c, inst, hnc, alpha, t, e.clone()],
        );
        return Some(SimpResult {
            expr: e,
            proof: Some(proof),
        });
    }

    // Condition changed but not to True/False: no sound non-dependent
    // congruence on the condition exists, so leave the ite untouched.
    None
}

/// Peel the LEMMA PATTERN's heterogeneous-operator projection layer when — and
/// only when — doing so makes its head agree with the (already peeled) match
/// target's head.
///
/// `simp` peels the projection layer off the GOAL subterm so a bare-head lemma
/// (`Nat.add ?n 0`) can match `n + 0`. That peel is one-sided, so the mirror
/// configuration never matched: a lemma whose own statement is written in
/// NOTATION (`n - m + m = n`, i.e. `@HAdd.hAdd … (@instHSub …) …`) keeps its
/// `HAdd.hAdd` head while the goal subterm has just been reduced to `Nat.add`.
/// Head-keyed unification then fails on the head constant alone. Every imported
/// Lean lemma stated over `+ - * / % ^ ++ &&& ||| ^^^ <<< >>>` is in that
/// configuration, which is why `simp only [Nat.sub_add_cancel]` reported
/// `NoProgress` while `exact Nat.sub_add_cancel h` (which goes through def-eq,
/// not head-keyed matching) succeeded on the same goal.
///
/// This is the mirror of the pattern-side arm `rw` already has in
/// `equality/rewrite.rs::keyed_head_unify`, and it is guarded the same way: the
/// peel is used ONLY if the reduced head is the same constant as the target's
/// head. So it can never change a case that already matches — it only rescues
/// cases whose heads currently disagree, where unification fails today.
///
/// Also collapses `@OfNat.ofNat Nat k (instOfNatNat k)` operand leaves in the
/// pattern to the raw literal, mirroring what the target already gets: without
/// it a peeled `Nat.div ?n (@OfNat.ofNat Nat 1 …)` still would not meet the
/// target's `Nat.div n 1`, because the `OfNat` instance does not unfold at
/// `withReducible` transparency.
///
/// SOUNDNESS: peeling is definitional (the instance's own ι/δ-reduction), and
/// nothing downstream is restated over the peeled form — `lhs_inst` is still
/// built from the ORIGINAL `lemma.lhs`, still checked def-eq to `expr`, the
/// assembled proof still goes through `proof_matches_rewrite`, and the kernel
/// `add_decl` re-check remains the backstop. This only decides which candidate
/// is *selected*.
///
/// ENSURES: on `Some(p)`, `p` is def-eq to `pattern` and `p`'s head constant is
///   the same `Name` as `match_target`'s head constant.
/// ENSURES: `None` whenever the heads already agree, the pattern head is not a
///   hetero-op projection, or the peel does not reach the target's head — in
///   every such case the caller keeps the unpeeled pattern.
fn peel_pattern_to_target_head(
    state: &ProofState,
    goal: &Goal,
    pattern: &Expr,
    match_target: &Expr,
) -> Option<Expr> {
    let ExprKind::Const(pat_name, _) = pattern.get_app_fn().kind() else {
        return None;
    };
    let ExprKind::Const(target_name, _) = match_target.get_app_fn().kind() else {
        return None;
    };
    if pat_name == target_name || !is_hetero_op_projection(pat_name) {
        return None;
    }
    let reduced = reduce_op_projection_head(state, goal, pattern)?;
    let reduced = collapse_nat_ofnat_literals(&reduced).unwrap_or(reduced);
    match reduced.get_app_fn().kind() {
        ExprKind::Const(reduced_name, _) if reduced_name == target_name => Some(reduced),
        _ => None,
    }
}

/// Head-agreement guard against the star-pattern whnf-rewrite NOISE class
/// (the B102/B103 residue documented by the B7 permutative lane).
///
/// Mechanism, measured (see `test_simp_star_noise_guard_*`): a star-keyed
/// builtin whose literal-operand pattern ι-collapses to a bare variable
/// (`Nat.sub_zero : Nat.sub ?n 0`, whose LHS WHNFs to `?n`) is offered at
/// EVERY subterm, and the unifier — reducing wherever discriminants disagree —
/// legally matches it against an ARBITRARY subterm by binding `?n` to the
/// subterm's WHNF. The rewrite is sound and kernel-accepted, but it re-spells
/// e.g. `Nat.add a b` into its stuck `Nat.rec` WHNF: unreadable goals, and the
/// spelling round-trips the B7 ordered-rewriting guard had to be immunized
/// against (its 4-cycle `unfold → flip → unfold → flip` measurement).
///
/// The rule, purely RESTRICTIVE (refuses matches, never enables one): a lemma
/// whose STORED pattern head is a constant `C` is only matched against a
/// subterm whose own head — after the SAME normalization the matcher already
/// performs for instance chains ([`MatchTarget`]: hetero-op projection peel +
/// `OfNat` literal collapse) — is that same `C`. A `Nat.sub`-headed lemma can
/// then never fire on a `Nat.add`-headed subterm merely because def-eq can
/// bend one into the other.
///
/// Deliberately NOT refused (each would break a legitimate match):
/// * either head a hetero-op projection (`HAdd.hAdd`, …): the matcher's own
///   [`peel_pattern_to_target_head`] bridges pattern-side projections, and a
///   polymorphic pattern whose instance is a metavariable cannot be peeled at
///   all — the unifier must keep deciding those;
/// * a non-`Const` head on either side (`Lit`, FVar/meta, `Lam`, `MData`, …):
///   literal↔constructor bridging (`Lit 5` vs `Nat.succ …`, `Lit 0` vs
///   `Nat.zero`) and hypothesis-lemma FVar patterns keep full unifier
///   semantics.
///
/// This is a match-time guard, NOT an offer-time filter: star-keyed lemmas
/// stay in every candidate set (`test_simp_star_tier_identity_siblings_…`
/// pins that), and legitimate uses — `Nat.sub_zero` on `a - 0` in surface or
/// bare spelling — still fire because the target's peeled head IS `Nat.sub`.
///
/// The head test alone is NOT the whole guard: the same absorption also
/// happens head-to-head (`Nat.sub_zero` on `Nat.sub a a` binds
/// `?n := whnf(Nat.sub a a)`, the stuck `Nat.rec` spelling, after the `0 =?= a`
/// argument mismatch sends the unifier down its reduction fallback). That
/// residue is caught by the binding-hygiene half,
/// [`binding_is_whnf_absorption`], at the one place the binding is visible.
fn star_noise_head_guard_refuses(lemma: &SimpLemma, match_target: &Expr) -> bool {
    let ExprKind::Const(pattern_head, _) = lemma.lhs.get_app_fn().kind() else {
        return false;
    };
    let ExprKind::Const(target_head, _) = match_target.get_app_fn().kind() else {
        return false;
    };
    pattern_head != target_head
        && !is_hetero_op_projection(pattern_head)
        && !is_hetero_op_projection(target_head)
}

/// Binding-hygiene half of the star-noise guard: did this pattern-variable
/// binding come from the unifier ABSORBING a re-spelling of the WHOLE target
/// rather than from a position of it?
///
/// The noise class succeeds through the unifier's reduction fallback: a
/// ι-collapsible pattern (`Nat.sub ?n 0` WHNFs to bare `?n`) meets a target
/// whose argument refuted the structural match (`Nat.sub a a` — `0 =?= a` is
/// rigid-rigid), both sides get reduced, and `?n` absorbs `whnf(target)` —
/// the stuck `Nat.rec` re-spelling of the very subterm being rewritten, which
/// makes the "rewrite" pure noise (it replaces the subterm with a def-eq
/// respelling of itself). The signature is precise: the binding is NOT a
/// syntactic subterm of the target as given, yet it is def-eq to the ENTIRE
/// target. Refusing exactly that refuses the absorption.
///
/// Deliberate allowances (each a measured legitimate bend that a broader
/// "binding must be a verbatim subterm" rule was seen to break — the
/// `data_map-length` battery row):
/// * a binding that IS a syntactic subterm of the normalized or source
///   target — the ordinary first-order match;
/// * a NON-subterm binding that is not def-eq to the whole target: the
///   unifier legally exposes constructors inside an ARGUMENT by ι-reduction
///   (`List.length_cons`'s `@List.cons ?α ?x ?xs` argument against
///   `List.map f (x :: xs)` reduces the argument to `cons (f x) (map f xs)`
///   and binds `?x := f x` — pieces of a reduced argument, not a re-spelling
///   of the whole target);
/// * a NUMERAL-shaped binding (`Lit k`, `Nat.zero`, a `Nat.succ` chain):
///   value-level literal bridging (`?k := 2` when `Nat.succ ?k` meets
///   `Lit 3`) — fast-pathed before any def-eq work;
/// * a binding still carrying unassigned metas (left to the later guards /
///   discharge), and any OPEN comparison (loose BVars on either side), where
///   `is_def_eq` is unreliable — both conservatively allowed, preserving the
///   pre-guard behaviour.
fn binding_is_whnf_absorption(
    state: &ProofState,
    goal: &Goal,
    bound: &Expr,
    match_target: &Expr,
    source: &Expr,
) -> bool {
    if contains_unassigned_meta(bound) || is_numeral_shaped(bound) {
        return false;
    }
    if occurs_syntactically(bound, match_target) || occurs_syntactically(bound, source) {
        return false;
    }
    if bound.has_loose_bvars() || source.has_loose_bvars() {
        return false;
    }
    state.is_def_eq(goal, bound, source)
}

/// The canonical `Lit` behind a closed Nat numeral spelling: a raw literal is
/// itself; the surface `@OfNat.ofNat Nat k (instOfNatNat k)` projection form
/// yields its stored literal. `None` for everything else — deliberately NOT
/// `Nat.zero`/`Nat.succ` towers, which need value arithmetic and whose
/// tower-to-literal rewrites are genuine (order-decreasing) normalizations.
fn numeral_spelling_lit(e: &Expr) -> Option<Expr> {
    if matches!(e.kind(), ExprKind::Lit(_)) {
        return Some(e.clone());
    }
    super::match_target::as_nat_ofnat_literal(e)
}

/// Is `e` a closed numeral spelling: a literal, `Nat.zero`, or a `Nat.succ`
/// chain terminating in one? (See [`binding_is_whnf_absorption`].)
fn is_numeral_shaped(e: &Expr) -> bool {
    stack_safe(|| match e.kind() {
        ExprKind::Lit(_) => true,
        ExprKind::Const(name, _) => *name == *NAT_ZERO_NAME,
        ExprKind::App(f, a) => {
            matches!(f.kind(), ExprKind::Const(name, _) if *name == *NAT_SUCC_NAME)
                && is_numeral_shaped(a)
        }
        _ => false,
    })
}

static NAT_ZERO_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.zero"));
static NAT_SUCC_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.succ"));

/// Does `needle` occur as a syntactic subterm of `hay` (plain structural
/// equality at every node)?
fn occurs_syntactically(needle: &Expr, hay: &Expr) -> bool {
    stack_safe(|| {
        if needle == hay {
            return true;
        }
        match hay.kind() {
            ExprKind::App(f, a) => {
                occurs_syntactically(needle, f) || occurs_syntactically(needle, a)
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                occurs_syntactically(needle, ty) || occurs_syntactically(needle, body)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                occurs_syntactically(needle, ty)
                    || occurs_syntactically(needle, val)
                    || occurs_syntactically(needle, body)
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                occurs_syntactically(needle, inner)
            }
            _ => false,
        }
    })
}

/// Try to apply a simp lemma and also produce the proof term.
///
/// On success, returns `(result, proof)` where `proof` is the lemma constant
/// applied to the matched arguments (i.e., `lemma_name arg0 arg1 ...`).
/// The proof has type `from = to` where `from` matched `expr` and `to` is the result.
/// Conditional lemmas (RC-J) are handled here: any binder the LHS match left
/// undetermined that is a genuine `Prop` side condition is handed to
/// [`super::discharge::discharge_premise`], and the whole rewrite is abandoned
/// when it cannot be closed. `lemmas`/`config` are threaded in for that
/// discharger (it may run `simp` recursively on the premise, bounded by
/// [`SimpConfig::discharge_depth`]).
///
/// Applies [`star_noise_head_guard_refuses`] first: a `Const`-headed pattern
/// is only matched against a subterm whose normalized head is the same
/// constant. With `CLEAN_SIMP_HEAD_GUARD_TRACE` set, a refusal additionally
/// runs the unguarded matcher and reports (stderr) any rewrite the guard
/// suppressed — diagnostic only: that ghost run consumes simp budget/fuel, so
/// never quote a verdict measured with the trace on.
///
/// REQUIRES: `lemma.name` and its BVar layout align with `lemma.lhs`/`lemma.rhs`
/// ENSURES: On Some, returns the instantiated RHS plus a proof term built from `lemma.name`
/// ENSURES: On Some, every side condition of `lemma` was discharged with a
///   type-checked proof term; no argument slot is silently skipped
/// ENSURES: On Some, the guard did not refuse — i.e. the lemma's stored
///   pattern head (when a non-hetero `Const`) equals the normalized target head
pub(crate) fn try_apply_simp_lemma_with_proof(
    state: &ProofState,
    goal: &Goal,
    target: &MatchTarget,
    lemma: &SimpLemma,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
    budget: &SimpBudget,
) -> Option<(Expr, Expr)> {
    if star_noise_head_guard_refuses(lemma, target.expr()) {
        if std::env::var_os("CLEAN_SIMP_HEAD_GUARD_TRACE").is_some() {
            if let Some((would_be, _proof)) =
                try_apply_simp_lemma_unguarded(state, goal, target, lemma, lemmas, config, budget)
            {
                if would_be != *target.source() {
                    eprintln!(
                        "simp-head-guard: refused would-have-fired lemma={} \
                         pattern_head={:?} target_head={:?} target={:?} would_rewrite_to={:?}",
                        lemma.name,
                        lemma.lhs.get_app_fn(),
                        target.expr().get_app_fn(),
                        target.source(),
                        would_be
                    );
                }
            }
        }
        return None;
    }
    try_apply_simp_lemma_unguarded(state, goal, target, lemma, lemmas, config, budget)
}

/// The matcher body behind [`try_apply_simp_lemma_with_proof`], WITHOUT the
/// star-noise head guard. Only that wrapper (and its trace arm) may call this.
fn try_apply_simp_lemma_unguarded(
    state: &ProofState,
    goal: &Goal,
    target: &MatchTarget,
    lemma: &SimpLemma,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
    budget: &SimpBudget,
) -> Option<(Expr, Expr)> {
    // The subterm being rewritten. Every guard below — `lhs_inst ≡ expr`,
    // `proof_matches_rewrite` — is stated over THIS, never over the normalised
    // match target.
    let expr = target.source();
    // Match-rejection tracer: CLEAN_SIMP_MATCH_TRACE=<name-substring> prints
    // which exit dropped a candidate whose name matches the filter. Sibling of
    // CLEAN_SIMP_HEAD_GUARD_TRACE; diagnostic only.
    let mtrace = std::env::var("CLEAN_SIMP_MATCH_TRACE")
        .ok()
        .filter(|f| lemma.name.to_string().contains(f.as_str()))
        .is_some();
    let mut metas = MetaState::new();
    // Pattern metas are scoped to the GOAL's locals (elab locals + goal ctx):
    // a pattern variable must be allowed to bind a goal subterm mentioning a
    // goal FVar (`?n := a` for `a * 1`), while binder-opened temporaries stay
    // rejected by the unifier's scope check (B102).
    let pattern_scope = state.meta_scope_for_context(&goal.local_ctx);
    let (pattern_with_metas, mut bvar_to_meta) =
        convert_bvars_to_metas(&lemma.lhs, &mut metas, &pattern_scope);

    // Match target: the projection peel and the `OfNat` literal collapse the
    // matcher needs, computed ONCE per subterm by the candidate loop rather
    // than once per candidate. See [`MatchTarget`] for why hoisting them is
    // behaviour-preserving and what each step is for.
    let match_target = target.expr();

    // Normalize the LEMMA PATTERN the same way, so the two sides meet. Without
    // this the normalization above is ONE-SIDED: a lemma whose own statement is
    // written in notation keeps its `HDiv.hDiv` head while the goal subterm has
    // just been reduced to `Nat.div`, and head-keyed unification fails on the
    // head alone — even when pattern and goal subterm are otherwise byte-identical.
    // See [`peel_pattern_to_target_head`].
    let peeled_pattern =
        peel_pattern_to_target_head(state, goal, &pattern_with_metas, match_target);
    let match_pattern = peeled_pattern.as_ref().unwrap_or(&pattern_with_metas);

    // Numeral-source guard (B103's sibling, measured 2026-08-28): a source
    // subterm that IS a closed numeral spelling (`Lit` or the OfNat
    // projection form) may only be rewritten by a lemma whose own stored LHS
    // is numeral-spelled (`two_eq : 2 = x` legitimately rewrites a `2`). A
    // constructor- or function-headed pattern (`Nat.succ ?n`) reaches a bare
    // literal only through the unifier's value bridge
    // (`Lit 1 ≡ Nat.succ (Lit 0)`), and the rewrite it then produces —
    // `1 → 0 + 1`, measured firing INSIDE an `OfNat` spine, where the
    // congrArg proof left the value-indexed instance stale and the kernel
    // killed the whole declaration — is a de-normalization Lean's
    // literal-keyed index never offers. Refusing here is offering-parity,
    // stated at match time because Clean's always-offered unindexed buckets
    // cannot express it at index time.
    if numeral_spelling_lit(expr).is_some() && numeral_spelling_lit(&lemma.lhs).is_none() {
        if mtrace {
            eprintln!("simp-match: lemma={} REJECT numeral-source", lemma.name);
        }
        return None;
    }

    let ctx = LocalContext::new();
    let unify_result = {
        // B15 (simp-set discipline): match lemma LHSs at `withReducible`
        // transparency. Lean's `simp` unfolds only `@[reducible]` constants while
        // matching, so a bare `def f := 0 + n` (semireducible) is opaque — the
        // pattern `0 + ?n` of a default lemma like `Nat.zero_add` does NOT reach
        // inside `f x`. The old full-transparency unifier silently unfolded `f`
        // to expose `0 + n`, letting `simp` "make progress" on and close goals
        // Lean rejects with "simp made no progress". Genuine matches (syntactic,
        // or through an `@[reducible]` abbrev) are unaffected.
        let mut unifier = Unifier::with_env_reducible(&mut metas, &state.env, ctx);
        // Match WITHOUT the eager leading WHNF (B102): both sides are surface
        // forms — the lemma's stated LHS and a goal subterm (post projection
        // peel / OfNat collapse). The eager pre-WHNF δ/ι-rots a literal-operand
        // arithmetic pattern (`Nat.mul ?n 1` → its stuck `Nat.rec` body, with
        // the goal side reducing DIFFERENTLY), so the structural match that
        // should be trivial fails on mismatched normal forms. `unify_core`
        // still reduces internally wherever discriminants disagree, so genuine
        // def-eq matches (and the `Nat.zero ≡ Lit 0` bridge) are preserved.
        unifier.unify_no_initial_whnf(match_pattern, match_target)
    };

    match unify_result {
        UnifyResult::Success => {
            // Instantiate BOTH expr-metavariables AND solved universe-level
            // metavariables. A builtin pattern that carries a `Level::Param` head
            // (e.g. universe-polymorphic `eq_self`/`ite_*` over `Eq.{u_simp}`/
            // `ite.{u_simp}`) gets `u_simp` solved as a level constraint by the
            // unifier; without `instantiate_levels` the instantiated term keeps
            // the unbound `Param`, so the downstream `is_def_eq(lhs_inst, expr)`
            // guard (and the assembled proof) carry `Eq.{u_simp}` vs the goal's
            // `Eq.{1}` and are spuriously rejected. `instantiate_levels` is a
            // no-op when no level param was solved, so the common case is
            // untouched.
            let inst = |e: &Expr| metas.instantiate_levels(&metas.instantiate(e));

            // Binding-hygiene half of the star-noise guard (see
            // `binding_is_whnf_absorption`): refuse the match when a pattern
            // variable was bound by absorbing a re-spelling of the WHOLE
            // target (`Nat.sub_zero` on `Nat.sub a a` binding `?n` to the
            // stuck `Nat.rec` WHNF of `Nat.sub a a` itself). Runs before the
            // type/def-eq guards so a noise match never pays for them;
            // purely restrictive.
            for meta_expr in bvar_to_meta.values() {
                let bound = inst(meta_expr);
                if bound == *meta_expr {
                    continue; // unassigned: left to the later guards/discharge
                }
                if binding_is_whnf_absorption(state, goal, &bound, match_target, expr) {
                    if std::env::var_os("CLEAN_SIMP_HEAD_GUARD_TRACE").is_some() {
                        eprintln!(
                            "simp-head-guard: refused absorptive-binding lemma={} \
                             binding={bound:?} target={:?}",
                            lemma.name,
                            target.source()
                        );
                    }
                    return None;
                }
            }

            // The instantiated LHS the proof is *stated* over. For lemmas whose
            // builtin pattern uses a bare head (`Nat.mul`) but whose match target
            // is typeclass-headed (`@HMul.hMul Nat … n 0`), `lhs_inst` differs
            // syntactically from `expr` even though they are (genuinely) def-eq.
            let lhs_with_metas = substitute_bvars_with_metas(&lemma.lhs, &bvar_to_meta);
            let lhs_inst = inst(&lhs_with_metas);

            // The validation below relies on `infer_type`, which is only
            // meaningful for closed terms: when simp recurses under a binder the
            // matched `expr`/`lhs_inst`/proof carry loose `BVar`s with no local
            // context, so type inference is unreliable. In that case we keep the
            // baseline behaviour (no extra check) and rely on the downstream
            // congruence + kernel re-check. The spurious top-level matches we
            // want to reject (whole-goal `Eq …` matched by `Nat.add ?n 0`) are
            // always closed, so this targeting loses no coverage.
            let closed = !expr.has_loose_bvars() && !lhs_inst.has_loose_bvars();

            // Soundness guard against spurious unifier matches. The first-order
            // unifier can WHNF-reduce a pattern (`Nat.add ?n 0`) and bind `?n` to
            // a partial application of an unrelated head — e.g. matching the whole
            // goal `Eq Nat (n*0) 0` by treating `Eq Nat (n*0)` as `?n` and the
            // trailing `0` as the literal — producing an `lhs_inst` like
            // `Nat.add (Eq Nat (n*0)) Nat.zero` that is NOT a real rewrite of
            // `expr`. Reject any match whose reconstructed LHS is not def-eq to
            // `expr`: a genuine rewrite always has `lhs_inst ≡ expr`. We require
            // `lhs_inst` to be *well-typed at the type of `expr`* before trusting
            // the def-eq check, since `is_def_eq` on an ill-typed term can
            // spuriously succeed via WHNF.
            // Soundness guard against ι-collapsed pattern matches that leave a
            // pattern metavariable UNASSIGNED. The first-order unifier can match
            // `Nat.mul ?n 0` against a target by WHNF-reducing BOTH sides to the
            // ι base-case `0` and unifying `0 =?= 0` — succeeding WITHOUT ever
            // binding `?n`. The instantiated proof/result then carry a leaked
            // unassigned-metavar FVar (`MetaState::to_fvar`, high-bit tagged) in
            // place of `?n`, e.g. `Nat.mul_zero ?n` — an ill-typed term the
            // downstream `is_def_eq` checks accept (both sides ι-collapse to `0`)
            // but the kernel `add_decl` later rejects with a `TypeMismatch`. A
            // genuine rewrite fully instantiates every pattern metavariable, so a
            // leaked meta means the match was spurious: bail to `None` and let
            // simp try another candidate / report NoProgress.
            if contains_unassigned_meta(&lhs_inst) {
                if mtrace {
                    eprintln!("simp-match: lemma={} REJECT lhs-meta-leak", lemma.name);
                }
                return None;
            }

            if closed && lhs_inst != *expr {
                let expr_ty = state.infer_type(goal, expr).ok();
                let lhs_ok = state
                    .infer_type(goal, &lhs_inst)
                    .ok()
                    .zip(expr_ty)
                    .is_some_and(|(lhs_ty, e_ty)| state.is_def_eq(goal, &lhs_ty, &e_ty));
                if !lhs_ok || !state.is_def_eq(goal, &lhs_inst, expr) {
                    if mtrace {
                        eprintln!(
                            "simp-match: lemma={} REJECT lhs-guard lhs_ok={lhs_ok}",
                            lemma.name
                        );
                    }
                    return None;
                }
            }

            // RC-J: the LHS match determines only the binders that OCCUR in the
            // pattern. A conditional lemma's hypotheses do not, so they arrive
            // here unbound; discharge them (or abandon the rewrite). Runs after
            // the cheap `lhs_inst ≡ expr` guard so a spurious match never pays
            // for a discharge attempt.
            if !bind_undetermined_binders(
                state,
                goal,
                lemma,
                &metas,
                &mut bvar_to_meta,
                lemmas,
                config,
                budget,
            ) {
                if mtrace {
                    eprintln!("simp-match: lemma={} REJECT discharge", lemma.name);
                }
                return None;
            }

            // The RHS is instantiated only AFTER discharge: a dependent
            // conclusion may mention the hypothesis binder, and `bvar_to_meta`
            // now carries its proof.
            let rhs_with_metas = substitute_bvars_with_metas(&lemma.rhs, &bvar_to_meta);
            let result = inst(&rhs_with_metas);
            if contains_unassigned_meta(&result) {
                if mtrace {
                    eprintln!("simp-match: lemma={} REJECT result-meta-leak", lemma.name);
                }
                return None;
            }

            // B7 (ordered rewriting, Lean parity): a PERMUTATIVE lemma — same
            // term on both sides up to a bijective renaming of its pattern
            // variables, `Nat.add_comm : ?a + ?b = ?b + ?a` canonically —
            // must not fire unconditionally. It matches its own output, so
            // the main simp loop flips the SAME node every pass until
            // `max_steps`, and (worse) the top-level match at that node runs
            // before child recursion, so rewrites INSIDE the operands (the
            // induction hypotheses of `data_tree-mirror-size`) are starved
            // for the whole run. Lean marks such lemmas `perm` at
            // registration and applies them only when the rewrite strictly
            // DECREASES the term in a fixed total order — terminating, and
            // canonicalizing both sides of an equality goal to the same
            // ordering-minimal operand order. Same rule here.
            //
            // The comparison is `result < lhs_inst` — both assembled from the
            // LEMMA's own pattern over the matched bindings — and
            // deliberately NOT `result < expr` (the goal subterm). The two
            // differ when the unifier matched through reduction: a
            // ι-collapsed star pattern (`Nat.sub ?n 0` ⇒ bare `?n`, B102) can
            // legally rewrite `Nat.add a b` to its stuck `Nat.rec` WHNF
            // (def-eq, kernel-checkable), and against THAT spelling a
            // bare-`Nat.add` flip always compares "smaller", re-arming the
            // flip on every spelling round-trip (measured: a 4-cycle
            // `unfold → flip → unfold → flip` consuming all 1000 steps on
            // `Nat.add a b = Nat.add b a`). `lhs_inst`/`result` share the
            // pattern's spelling by construction, so the order sees ONLY the
            // operand permutation and re-spelling cannot re-enable a flip.
            // Refusing is fail-closed (simp just reports the goal honestly);
            // every accepted rewrite still carries its kernel-checked proof.
            //
            // (The star-noise re-spelling itself is now refused upstream by
            // `star_noise_head_guard_refuses` / `binding_is_whnf_absorption`,
            // so the 4-cycle can no longer arise — but the pattern-side
            // comparison stays: it is the principled choice independent of
            // that guard, and defense in depth against any future spelling
            // bend the guard does not cover.)
            if super::perm::is_permutative_pair(&lemma.lhs, &lemma.rhs)
                && !super::perm::expr_order_lt(&result, &lhs_inst)
            {
                if mtrace {
                    eprintln!("simp-match: lemma={} REJECT perm-order", lemma.name);
                }
                return None;
            }

            // B103 (numeral-respell termination): a rewrite whose source and
            // result are BOTH closed numeral spellings of the SAME literal is
            // a pure re-spelling. Neither star-noise guard refuses the class:
            // `Nat.sub_zero`'s hetero-op pattern absorbs the OfNat-form `1`
            // with a numeral-shaped binding (the carve-out the locked iota
            // rows need), and `Bool.false.sizeOf_spec` — whose closed LHS
            // `sizeOf false` WHNF-computes to `1` — has no binding at all.
            // The PAIR is a 2-cycle (OfNat form -> `Lit` -> OfNat form) that
            // burned all 1000 `max_steps` re-spelling one literal, starving
            // the closing lemma (measured: g_simp probe 27 / the minimal
            // `Nat.succ (List.length l) = List.length l + 1`, 500 fires each
            // way). The rule: a same-literal respell is REFUSED OUTRIGHT.
            // Replacing one spelling of a literal with another spelling of
            // the SAME literal can never make semantic progress — spelling
            // bridging at MATCH time is already the job of [`MatchTarget`]'s
            // OfNat collapse and the unifier's literal bridges — while every
            // permitted direction was measured to break a goal family,
            // because the elaborator's own spellings are MIXED (`0` arrives
            // as a raw `Lit`, `1` as the OfNat projection form): allowing
            // OfNat→`Lit` respelled `+ 1` goals away from every lemma RHS
            // (`Nat.succ_eq_add_one`/`Nat.zero_add` churned 500 rounds on
            // `simp [Nat.succ_eq_add_one]`), and allowing `Lit`→OfNat let
            // `Nat.default_eq_zero`/`Bool.toNat_false` — closed compute
            // lemmas whose LHS WHNFs to `0` — respell the `Lit 0` goals of
            // `n + 0 + 0 = n` into forms the `Nat.add_zero` builtin then
            // missed (three g_simp rows red). Both measured 2026-08-28.
            if let (Some(src_lit), Some(res_lit)) =
                (numeral_spelling_lit(expr), numeral_spelling_lit(&result))
            {
                if src_lit == res_lit {
                    if mtrace {
                        eprintln!("simp-match: lemma={} REJECT numeral-respell", lemma.name);
                    }
                    return None;
                }
            }

            let proof = if let Some(proof_expr) = &lemma.proof_expr {
                let proof_with_metas = substitute_bvars_with_metas(proof_expr, &bvar_to_meta);
                let proof = metas.instantiate(&proof_with_metas);
                // Prebuilt templates (`mk_iff_rewrite_proof_template`) are
                // assembled at REGISTRATION time, where nothing can solve the
                // declaration's universe parameters — matching happens later.
                // A template whose head still spells this lemma's own declared
                // parameter is therefore unsolved, and emitting it produces an
                // ill-typed term that `proof_matches_rewrite` cannot catch
                // (`infer_type` is the non-checking fast path) and only the
                // kernel rejects, killing the whole declaration. Refuse it
                // here so simp merely reports that the lemma did not apply.
                let declared: Vec<Name> = state
                    .env
                    .get_const(&lemma.name)
                    .map(|info| info.level_params.clone())
                    .unwrap_or_default();
                if !declared.is_empty() && template_has_unsolved_level(&proof, &declared) {
                    if mtrace {
                        eprintln!("simp-match: lemma={} REJECT template-level", lemma.name);
                    }
                    return None;
                }
                if !proof_matches_rewrite(state, goal, &proof, expr, &result) {
                    if mtrace {
                        eprintln!(
                            "simp-match: lemma={} REJECT proof-mismatch-template",
                            lemma.name
                        );
                    }
                    return None;
                }
                proof
            } else {
                // Build the proof term: lemma.name applied to the matched arguments.
                // In de Bruijn representation, BVar(0) is the innermost binder and
                // higher indices correspond to outer binders. Theorem application
                // requires outermost-binder-first order, so we iterate in reverse:
                // BVar(max-1) first (outermost), down to BVar(0) (innermost).
                //
                // Universe-polymorphic lemmas need the const's level args
                // supplied: `@eq_self.{1} Nat n`, not the bare `eq_self`.
                //
                // TWO level-param conventions coexist in the simp set, and the
                // proof reconstruction has to serve both:
                //
                //  * A lemma taken from the ENVIRONMENT (`simp [X]`,
                //    `simp only [X]`, the `@[simp]` registry) has its pattern
                //    lifted verbatim out of `decl.type_`, so the `Const` nodes
                //    of `lemma.lhs` carry the DECLARATION's real level-param
                //    names (`u`, `u_1`, …). Those are the params the unifier
                //    just solved against the goal's levels, so each decl level
                //    param must be resolved under its OWN name. Substituting a
                //    fixed `u_simp` here left every such lemma's level
                //    unconstrained, so the assembled proof carried an
                //    unassigned `Param("u_simp")`, `proof_matches_rewrite`
                //    rejected it, and the rewrite was silently dropped as
                //    `NoProgress` — 37% of Lean core's `@[simp]` set is
                //    universe-polymorphic, so this was most of the imported
                //    simp set (RC-E.1).
                //
                //  * Clean's HAND-WRITTEN builtin patterns
                //    (`simp/lemmas_builtin.rs`) deliberately spell a single
                //    `Level::Param("u_simp")` in their `Const` heads
                //    (`Eq.{u_simp}`, `ite.{u_simp}`, `List.append_nil.{u_simp}`)
                //    — a name that has no counterpart in the proof
                //    declaration's level params (`List.append_nil.{u}`). For
                //    those the decl's own name is never constrained and
                //    `u_simp` is, so the `u_simp` convention is the fallback.
                //
                // Resolving the decl's own name FIRST and only falling back to
                // `u_simp` when that name is still unsolved keeps both paths
                // working without renaming anything: a registry pattern never
                // mentions `u_simp`, so its fallback lookup is itself unsolved
                // and the own-name resolution is kept (which is also the right
                // answer when a level legitimately resolves to a *rigid* param
                // of the surrounding polymorphic declaration).
                let lemma_levels: Vec<Level> = state
                    .env
                    .get_const(&lemma.name)
                    .map(|info| {
                        info.level_params
                            .iter()
                            .map(|param| resolve_lemma_level(&metas, param))
                            .collect()
                    })
                    .unwrap_or_default();
                // FAIL CLOSED on an unsolved lemma universe. A level parameter
                // that occurs only in a BINDER TYPE — `implies_true.{u}
                // (α : Sort u) : (α → True) = True`, whose registered pattern
                // is just `Pi(_ : ?α, True)` — is never touched by matching,
                // so `resolve_lemma_level` hands back the declaration's own
                // raw `Param("u")` and simp emitted `@implies_true.{u} Nat`.
                // The kernel then rejected the whole declaration
                // (`expected Sort(Param(u)), inferred Sort(1)`); worse, the
                // guard below could not catch it, because `infer_type` is the
                // NON-checking fast path and never checks an application's
                // argument against its binder domain. Refusing the rewrite
                // here turns a hard, declaration-killing type error into an
                // ordinary "this lemma did not apply", which is the honest
                // outcome — simp may still close the goal another way.
                //
                // A level that legitimately resolves to a RIGID param of the
                // surrounding polymorphic declaration is fine and common, so
                // the test is not "has params" but "is one of THIS lemma's own
                // declared parameter names", i.e. demonstrably unsolved.
                let declared: Vec<Name> = state
                    .env
                    .get_const(&lemma.name)
                    .map(|info| info.level_params.clone())
                    .unwrap_or_default();
                let max_bvar = bvar_to_meta.keys().copied().max().map_or(0, |m| m + 1);
                let is_leaked = |lvls: &[Level]| {
                    lvls.iter().any(
                        |lvl| matches!(lvl, Level::Param(p) if declared.iter().any(|d| d == p)),
                    )
                };
                // SOLVE what matching could not. Walk the declaration's own Pi
                // telescope alongside the arguments about to be applied: a
                // binder declared `(α : Sort u)` whose argument is `Nat` pins
                // `u := 1` (from `Nat : Sort 1`). This is precisely the
                // information the LHS pattern lacks, and it is exactly how the
                // application would have solved the level had it gone through
                // the elaborator's own app path.
                let mut solved_params: Vec<Name> = Vec::new();
                let lemma_levels = if is_leaked(&lemma_levels) {
                    let mut subst: Vec<(Name, Level)> = Vec::new();
                    if let Some(info) = state.env.get_const(&lemma.name) {
                        let mut ty = info.type_.clone();
                        for i in (0..max_bvar).rev() {
                            // A binder with no matched argument is NOT applied
                            // by the assembly loop below, so the telescope and
                            // the argument list part ways here: continuing
                            // would solve a later `Sort u` binder from the
                            // WRONG argument (e.g. `u := 0` from a `True`).
                            // Alignment is unrecoverable, so stop solving —
                            // any still-unsolved parameter is then refused by
                            // the guard below, which is the safe direction.
                            let Some(meta_expr) = bvar_to_meta.get(&i) else {
                                break;
                            };
                            let arg = inst(meta_expr);
                            let ExprKind::Pi(_, dom, body) = ty.kind() else {
                                break;
                            };
                            if let ExprKind::Sort(Level::Param(p)) = dom.kind() {
                                if declared.iter().any(|d| d == p)
                                    && !subst.iter().any(|(q, _)| q == p)
                                {
                                    if let Ok(arg_ty) = state.infer_type(goal, &arg) {
                                        if let ExprKind::Sort(l) = state.whnf(goal, &arg_ty).kind()
                                        {
                                            subst.push((p.clone(), l.clone()));
                                            solved_params.push(p.clone());
                                        }
                                    }
                                }
                            }
                            ty = body.instantiate(&arg);
                        }
                    }
                    lemma_levels
                        .into_iter()
                        .map(|lvl| match &lvl {
                            Level::Param(p) => subst
                                .iter()
                                .find(|(q, _)| q == p)
                                .map_or(lvl.clone(), |(_, l)| l.clone()),
                            _ => lvl,
                        })
                        .collect()
                } else {
                    lemma_levels
                };
                // Still unsolved after that: refuse the rewrite. NOTE the
                // test is "did solving assign this parameter", not "is its
                // name one of the declaration's" — a level legitimately
                // solved to a RIGID param of the surrounding declaration can
                // share the lemma's spelling (`{γ : Sort u}` against
                // `implies_true.{u}`), and refusing those broke goals that
                // previously worked by that very name coincidence.
                // Emitting the
                // declaration's own raw parameter produced `@implies_true.{u}
                // Nat`, which the kernel rejected — killing the whole
                // declaration — while the guard below could not catch it
                // (`infer_type` is the non-checking fast path and never checks
                // an application's argument against its binder domain).
                // Refusing turns that into an ordinary "this lemma did not
                // apply".
                let unsolved_leak = lemma_levels.iter().any(|lvl| {
                    matches!(lvl, Level::Param(p)
                        if declared.iter().any(|d| d == p)
                            && !solved_params.iter().any(|s| s == p))
                });
                if unsolved_leak {
                    if mtrace {
                        eprintln!("simp-match: lemma={} REJECT unsolved-level", lemma.name);
                    }
                    return None;
                }
                let mut proof = Expr::const_(lemma.name.clone(), lemma_levels);
                for i in (0..max_bvar).rev() {
                    if let Some(meta_expr) = bvar_to_meta.get(&i) {
                        let arg = inst(meta_expr);
                        proof = Expr::app(proof, arg);
                    }
                }
                // Soundness symmetry with the `Some` branch: validate that the
                // assembled proof actually proves `expr = result` (def-eq).
                // Previously only the `proof_expr: Some` branch ran this check,
                // so a malformed builtin entry could emit an ill-typed proof that
                // only the downstream kernel `add_decl` rejected. Bail to None on
                // mismatch so simp reports NoProgress instead. Guarded by
                // `closed` (and a closed proof) because `infer_type` is unreliable
                // for proofs carrying loose binder variables.
                if closed
                    && !proof.has_loose_bvars()
                    && !proof_matches_rewrite(state, goal, &proof, expr, &result)
                {
                    if mtrace {
                        eprintln!(
                            "simp-match: lemma={} REJECT proof-mismatch-assembled",
                            lemma.name
                        );
                    }
                    return None;
                }
                proof
            };

            // Final defensive backstop: never hand back a proof carrying a leaked
            // unassigned-metavar FVar (see the `contains_unassigned_meta` guard on
            // `lhs_inst`/`result` above). The assembled proof reuses the same
            // instantiated metas, so a leak here mirrors a leak there; rejecting
            // keeps simp from emitting a term the kernel would reject.
            if contains_unassigned_meta(&proof) {
                if mtrace {
                    eprintln!("simp-match: lemma={} REJECT proof-meta-leak", lemma.name);
                }
                return None;
            }

            if mtrace {
                eprintln!("simp-match: lemma={} ACCEPT", lemma.name);
            }
            Some((result, proof))
        }
        UnifyResult::Failure(_) | UnifyResult::Stuck => {
            if mtrace {
                eprintln!(
                    "simp-match: lemma={} REJECT unify-fail result={unify_result:?} pattern={match_pattern:?} target={match_target:?}",
                    lemma.name
                );
            }
            None
        }
    }
}

/// Bind the lemma binders the LHS match left undetermined, discharging the ones
/// that are genuine `Prop` side conditions (RC-J).
///
/// `convert_bvars_to_metas` mints a metavariable only for a BVar that OCCURS in
/// the pattern, so a conditional lemma
/// (`(a b : Nat) (h : b ≤ a) : a - b + b = a`) reaches proof assembly with `h`'s
/// slot missing entirely. The old assembly loop then skipped that argument, so
/// the term it built was `mycond a b` — still `Pi`-typed — which only the
/// downstream kernel `add_decl` rejected, with
/// `TypeMismatch { expected: <the equality>, inferred: Pi(..) }`.
///
/// Binders are walked from the OUTERMOST inwards (decreasing BVar index):
/// binder `k`'s type may mention only binders outside it, which carry HIGHER
/// indices, so by the time a slot is examined everything its type depends on is
/// already resolved.
///
/// Three outcomes per undetermined slot:
///
/// * **Not statable** (the instantiated domain still has loose BVars or an
///   unassigned meta — e.g. simp is recursing under a binder): left alone, the
///   pre-existing behaviour. The assembled proof stays `Pi`-typed and is
///   rejected by `proof_matches_rewrite`, so this is still fail-closed.
/// * **Not a `Prop`**: also left alone. A missing DATA argument is a malformed
///   pattern, not a side condition, and inventing a witness for it would be
///   unsound; the same fail-closed rejection applies.
/// * **A stated `Prop`**: handed to the discharger. On success its proof is
///   inserted into `bvar_to_meta` so every downstream consumer (RHS
///   substitution, `proof_expr` templates, the argument loop) picks it up
///   uniformly. On failure this returns `false` and the caller abandons the
///   rewrite.
///
/// # Soundness
///
/// This function never fabricates a term. The only expressions it inserts come
/// from `discharge_premise`, which type-checks each candidate against the
/// premise before returning it. Returning `false` is always safe: it merely
/// means simp reports `NoProgress` for this lemma.
///
/// ENSURES: Returns `true` only when every slot it chose to fill was filled
///   with a proof whose inferred type is def-eq to the corresponding premise.
#[allow(clippy::too_many_arguments)]
fn bind_undetermined_binders(
    state: &ProofState,
    goal: &Goal,
    lemma: &SimpLemma,
    metas: &MetaState,
    bvar_to_meta: &mut hashbrown::HashMap<u32, Expr>,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
    budget: &SimpBudget,
) -> bool {
    // A rule minted from a LOCAL hypothesis (`simp [*]`, `simp [h]`) carries
    // that hypothesis' name, which may coincide with an environment constant —
    // and reading THAT constant's binder telescope would describe a completely
    // different lemma. Local hypotheses shadow environment constants here
    // exactly as they do in `lemmas::resolve_unfold_defs`.
    let lemma_name = lemma.name.to_string();
    if goal.local_ctx.iter().any(|decl| decl.name == lemma_name) {
        return true;
    }
    // Hand-written builtin patterns likewise have no environment declaration to
    // read binders from; they are unconditional by construction, so there is
    // nothing to discharge.
    let Some(info) = state.env.get_const(&lemma.name) else {
        return true;
    };
    // Fast path: an unconditional lemma whose every binder the LHS match
    // already determined needs no work at all, and that is the overwhelming
    // majority of matches. Counting the Pi spine allocates nothing; the
    // lifting walk below only runs when a slot is genuinely open.
    let total = leading_pi_binder_count(&info.type_);
    if total == 0 || (0..total as u32).all(|index| bvar_to_meta.contains_key(&index)) {
        return true;
    }
    let binder_types = collect_binder_types_in_conclusion(&info.type_);

    for index in (0..binder_types.len()).rev() {
        let key = index as u32;
        if bvar_to_meta.contains_key(&key) {
            continue;
        }

        let domain = substitute_bvars_with_metas(&binder_types[index], bvar_to_meta);
        let domain = metas.instantiate_levels(&metas.instantiate(&domain));
        if domain.has_loose_bvars() || contains_unassigned_meta(&domain) {
            continue;
        }

        // Only propositions are side conditions.
        let is_prop = state
            .infer_type(goal, &domain)
            .is_ok_and(|sort| state.is_def_eq(goal, &sort, &Expr::prop()));
        if !is_prop {
            continue;
        }

        let Some(proof) =
            super::discharge::discharge_premise(state, goal, &domain, lemmas, config, budget)
        else {
            return false;
        };
        bvar_to_meta.insert(key, proof);
    }

    true
}

/// The level-param name Clean's hand-written builtin simp patterns
/// (`simp/lemmas_builtin.rs`) use for their universe-polymorphic `Const` heads.
/// It is a pattern-local convention, NOT any declaration's level param.
const BUILTIN_PATTERN_LEVEL_PARAM: &str = "u_simp";

/// Resolve one level param of a simp lemma's declaration to the level the
/// unifier solved for it while matching the lemma's pattern.
///
/// `param` is the name as it appears in the DECLARATION (`u`, `u_1`, …), which
/// is also how an environment-sourced pattern spells it — so that is the primary
/// lookup. A hand-written builtin pattern instead spells
/// [`BUILTIN_PATTERN_LEVEL_PARAM`], leaving the declaration's own name
/// unconstrained; that is the only case the fallback fires in, because a
/// registry pattern never mentions `u_simp` and so leaves it unsolved too.
///
/// ENSURES: returns the concrete level whenever the unifier solved one for
///   either name; otherwise returns the declaration's own (unsolved) param, so
///   the caller's `proof_matches_rewrite` guard still fails closed.
fn resolve_lemma_level(metas: &MetaState, param: &Name) -> Level {
    let own = metas.instantiate_level(&Level::param(param.clone()));
    if own.has_params() {
        let builtin = metas.instantiate_level(&Level::param(Name::from_string(
            BUILTIN_PATTERN_LEVEL_PARAM,
        )));
        if !builtin.has_params() {
            return builtin;
        }
    }
    own
}

/// Whether `expr` contains a leaked *unassigned* metavariable, represented as an
/// `FVar` whose id carries `MetaState`'s high-bit tag (`MetaState::to_fvar` /
/// `from_fvar`). After `MetaState::instantiate`, an FVar that still decodes to a
/// `MetaId` is a pattern metavariable the unifier never bound — a hallmark of a
/// spurious ι-collapsed match (e.g. `Nat.mul ?n 0` matched against a target that
/// WHNF-reduces to `0` without binding `?n`). Such a term is ill-typed and must
/// not be emitted as (part of) a simp rewrite proof.
fn contains_unassigned_meta(expr: &Expr) -> bool {
    stack_safe(|| match expr.kind() {
        ExprKind::FVar(id) => MetaState::from_fvar(*id).is_some(),
        ExprKind::App(f, a) => contains_unassigned_meta(f) || contains_unassigned_meta(a),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            contains_unassigned_meta(ty) || contains_unassigned_meta(body)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            contains_unassigned_meta(ty)
                || contains_unassigned_meta(val)
                || contains_unassigned_meta(body)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            contains_unassigned_meta(inner)
        }
        _ => false,
    })
}

/// Whether `proof` really witnesses `expr = result`.
///
/// The extraction is deliberately **top-level only** (`extract_eq_parts`, not
/// `extract_equality_full`). `extract_equality_full` recurses THROUGH `Pi`
/// binders, so it read a still-undischarged conditional proof of type
/// `∀ (h : b ≤ a), a - b + b = a` as if it proved the bare equality — which is
/// exactly how a `Pi`-typed simp proof used to escape this guard and surface
/// only at the kernel as
/// `TypeMismatch { expected: <the equality>, inferred: Pi(..) }` (RC-J).
/// A proof of a universally quantified equality is not a proof of that
/// equality, so rejecting it here turns a kernel type error into a clean
/// `NoProgress`.
fn proof_matches_rewrite(
    state: &ProofState,
    goal: &Goal,
    proof: &Expr,
    expr: &Expr,
    result: &Expr,
) -> bool {
    let Some((_, proof_lhs, proof_rhs)) = state
        .infer_type(goal, proof)
        .ok()
        .and_then(|ty| extract_eq_parts(&ty))
    else {
        return false;
    };

    state.is_def_eq(goal, &proof_lhs, expr) && state.is_def_eq(goal, &proof_rhs, result)
}

/// Recursively substitute occurrences of constants in `unfold_defs` with the
/// stored definition body.
///
/// Used by `simp_expr` to implement `simp [foo]` delta-unfolding when `foo` is
/// a `Declaration::Definition`. This mirrors `tactic::unfold::substitute_const`
/// but matches against a map of names rather than a single name, so a single
/// pass can unfold every user-requested definition. Part of #3518.
///
/// # Soundness
///
/// Substituting a `Declaration::Definition`'s value for its name is a
/// definitional-equality step by construction of the kernel, so this rewrite
/// is proof-free (simp records it via `SimpResult { proof: None }`).
///
/// # Contract
///
/// REQUIRES: `expr` is a well-formed expression tree.
/// REQUIRES: Each `(name, body)` entry in `unfold_defs` comes from a
///   `Declaration::Definition` so that substitution preserves definitional
///   equality (`resolve_unfold_defs` enforces this).
/// ENSURES: Every `Const(name, _)` node with `name` in `unfold_defs` is
///   replaced by the corresponding body; universe parameters are currently
///   not substituted into the body (matches the existing `unfold` tactic
///   behavior, which covers the Phase 2 monadic-unfolding use case).
/// ENSURES: Non-matching nodes preserve their constructor/metadata while
///   recursively rewriting children.
fn unfold_named_consts(expr: &Expr, unfold_defs: &HashMap<Name, Expr>) -> Expr {
    struct UnfoldFolder<'a> {
        unfold_defs: &'a HashMap<Name, Expr>,
    }

    impl ExprFolder for UnfoldFolder<'_> {
        fn fold_const(&mut self, name: &Name, levels: &LevelVec) -> Expr {
            if let Some(body) = self.unfold_defs.get(name) {
                body.clone()
            } else {
                Expr::const_(name.clone(), levels.clone())
            }
        }
    }

    let mut folder = UnfoldFolder { unfold_defs };
    folder.fold_expr(expr)
}

/// Whether a prebuilt rewrite proof still carries one of `declared` — the
/// lemma's OWN universe parameters — in a `Const` head. Such a level was
/// never solved (templates are built before matching), so the term is
/// ill-typed; see the call site for why the ordinary guard cannot see it.
fn template_has_unsolved_level(proof: &Expr, declared: &[Name]) -> bool {
    struct V<'a> {
        declared: &'a [Name],
        found: bool,
    }
    impl clean_kernel::ExprVisitor for V<'_> {
        type Result = ();
        fn combine(&self, _a: (), _b: ()) {}
        fn visit_const(&mut self, _name: &Name, levels: &LevelVec) {
            if levels
                .iter()
                .any(|lvl| matches!(lvl, Level::Param(p) if self.declared.iter().any(|d| d == p)))
            {
                self.found = true;
            }
        }
    }
    let mut v = V {
        declared,
        found: false,
    };
    clean_kernel::ExprVisitor::visit_expr(&mut v, proof);
    v.found
}
