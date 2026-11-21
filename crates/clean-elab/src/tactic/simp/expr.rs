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
use clean_kernel::{BinderInfo, Expr, ExprFolder, ExprKind, FVarId, Level, LevelVec, LocalContext};

use crate::stack_safe;
use crate::unify::{MetaState, Unifier, UnifyResult};

/// Pre-interned `Eq` name (avoids repeated allocation in equality extraction).
static EQ_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Eq"));

/// Pre-interned `Iff` name (avoids repeated allocation in iff extraction).
static IFF_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Iff"));

use super::binder::open_binder;
use super::binder_domain::{binding_violates_declared_domain, statement_yields_pattern};
use super::budget::SimpBudget;
use super::instance_slot::synthesize_class_slot;
use super::lemma_levels::{is_local_rule, LemmaLevels};
use super::match_target::{collapse_nat_ofnat_literals, match_successor_arguments, MatchTarget};
use super::pattern::{convert_bvars_to_metas, substitute_bvars_with_metas};
use super::proof::{
    mk_congr, mk_congr_arg, mk_congr_fun, mk_eq_trans, mk_forall_congr, mk_funext,
    mk_pi_domain_congr,
};
use super::reduce::{beta_reduce, eta_reduce, eta_reduce_fixpoint};
use super::simproc::{try_simprocs, SimprocSet};
use super::types::{SimpConfig, SimpLemma, SimpLemmaSet, SimpResult, UnfoldDef};
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
    collect_leading_binder_types(ty, leading_pi_binder_count(ty))
}

/// [`collect_binder_types_in_conclusion`] for the first `count` binders only,
/// re-expressed in the context just under THEM. A rule made of a local
/// equation is stated over the binders `extract_local_equality_template`
/// peeled off the hypothesis's WHNF, which can be fewer than its statement's
/// `Pi` spine.
///
/// ENSURES: `result.len() == min(count, leading_pi_binder_count(ty))`.
pub(crate) fn collect_leading_binder_types(ty: &Expr, count: usize) -> Vec<Expr> {
    // Outermost-first, each domain in its own context.
    let mut outer = Vec::with_capacity(count);
    let mut current = ty;
    while let ExprKind::Pi(_bi, domain, body) = current.kind() {
        if outer.len() == count {
            break;
        }
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
    if result.expr != *expr && !budget.admit(&result.expr, "simplifying a subterm") {
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
    // Lean's `simpImpl` returns a PROOF untouched (`if (← isProof e) then
    // return { expr := e }`): by proof irrelevance nothing can be gained by
    // rewriting inside one, and rewriting a `Prop` that occurs as an
    // ARGUMENT of a proof retypes it — `Eq.mpr P True h₁ True.intro` became
    // `Eq.mpr True True h₁ True.intro` once `P` was rewritten to `True`, and
    // the kernel refused it (`expected True = True, got P = True`). That is
    // what the `dite` collapse (`try_simp_dite`) leaves in the goal,
    // `t (Eq.mpr …)`, on the very next pass (measured 2026-09-12).
    if is_proof_term(state, goal, expr) {
        return SimpResult::refl(expr.clone());
    }

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
            if !budget.admit(&unfolded, "unfolding the requested definitions") {
                return SimpResult::refl(expr.clone());
            }
            result = SimpResult {
                expr: unfolded,
                proof: None,
            };
        }
    }

    if config.beta {
        // βζ copies a let-bound match alternative to every use (G76): refuse
        // a reduct far past the budget before building it. Such a `let`
        // enters a goal by unfolding a definition, so only an unfolding simp
        // pays for the check.
        if !config.unfold_defs.is_empty()
            && !budget.admit_before_zeta(&result.expr, "simplifying a subterm")
        {
            return SimpResult::refl(expr.clone());
        }
        let beta_reduced = beta_reduce(&result.expr);
        if beta_reduced != result.expr {
            if !budget.admit(&beta_reduced, "reducing a βζ redex") {
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
            if !budget.admit(&eta_reduced, "reducing an η redex") {
                return SimpResult::refl(expr.clone());
            }
            result = SimpResult {
                expr: eta_reduced,
                proof: None,
            };
        }
    }

    // ι: a recursor (or Clean's registered `casesOn`) applied to a
    // constructor (`super::iota`). Definitional, like β/η above, and charged
    // to the budget the same way.
    if let Some(reduced) = super::matcher::reduce_matcher_app(state, goal, &result.expr, budget)
        .or_else(|| super::iota::reduce_recursor_app(state, goal, &result.expr, budget))
        .or_else(|| super::proj_reduce::reduce_field_app(state, goal, &result.expr))
    {
        if !budget.admit(&reduced, "reducing a matcher, recursor or projection") {
            return SimpResult::refl(expr.clone());
        }
        result = SimpResult {
            expr: reduced,
            proof: None,
        };
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
    // Simplifying the children can expose the constructor a recursor
    // dispatches on: ι again, chained after their congruence proof.
    if let Some(reduced) = super::matcher::reduce_matcher_app(state, goal, &result.expr, budget)
        .or_else(|| super::iota::reduce_recursor_app(state, goal, &result.expr, budget))
        .or_else(|| super::proj_reduce::reduce_field_app(state, goal, &result.expr))
    {
        if budget.admit(
            &reduced,
            "reducing a matcher, recursor or projection after its children",
        ) {
            let iota = SimpResult {
                expr: reduced,
                proof: None,
            };
            return mk_eq_trans(result, iota, state, goal);
        }
    }

    // Try to apply simp lemmas at the top level (produces a real proof term).
    // Guard: skip matches that produce the same expression — this can happen when the
    // unifier WHNF-reduces the pattern (e.g. `Nat.add ?n 0` → `?n`) and the meta
    // absorbs the entire target, yielding an identity rewrite.
    let match_target = MatchTarget::new(state, goal, &result.expr);
    for lemma in lemmas.candidates_for_target(state, goal, &match_target) {
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
    // `simp only [..]` naming a simproc runs exactly the named ones
    // (`SimprocScope::Named`); Clean's table is none of them.
    if config.use_simprocs && config.simprocs.runs_clean_table() {
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

    // Lean's Prop-level literal comparisons (`Nat.reduceLT` and kin, G41):
    // the default simp set decides all of them, a `simp only` the ones its
    // list names (Lean's `simp only` runs no simproc it does not name).
    let literal_cmps = config.simprocs.literal_cmps(config.only);
    if config.use_simprocs && literal_cmps != 0 {
        if let Some(step) =
            super::simproc_builtins_cmp::reduce_literal_cmp(state, &result.expr, literal_cmps)
        {
            return mk_eq_trans(result, step, state, goal);
        }
    }

    // `imp_false` read as written (`imp_false.rs`, G39).
    if let Some(step) = super::imp_false::simp_imp_false(state, goal, &result.expr, config) {
        return mk_eq_trans(result, step, state, goal);
    }

    // Lean 4.8's always-on `simpCtorEq` became the named `reduceCtorEq`
    // simproc in the 4.30 oracle. The surface chooses the measured scope.
    if config.reduce_ctor_eq {
        if let Some(step) = super::ctor_eq::simp_ctor_eq(state, goal, &result.expr) {
            return mk_eq_trans(result, step, state, goal);
        }
    }

    // Lean's `C.injEq` lemmas (`ctor_inj.rs`, G70): members of the default
    // simp set, so a `simp only` that does not name them does not use them.
    if !config.only {
        if let Some(step) = super::ctor_inj::simp_ctor_inj(state, goal, &result.expr) {
            return mk_eq_trans(result, step, state, goal);
        }
    }

    result
}

/// Which argument positions of the application `head args` must NOT be
/// rewritten with a proof — Lean's `FunInfo.hasFwdDeps` plus its
/// `subsingletonInst` kind (`Meta/CongrTheorems.lean`).
///
/// A position is FROZEN when a LATER argument's type, or the application's own
/// type, depends on it: rewriting it leaves every sibling that mentions it
/// stale, and the assembled `congrArg`/`congr` equation is then ill-typed. The
/// two faces this closes are `@Exists P (fun h : P => …)` — the predicate's
/// type `P → Prop` mentions `P`, so `P` may not move while the lambda keeps
/// its `P` domain — and `@ite α c inst t e`, where `inst : Decidable c`
/// mentions `c`, so a condition rewritten to something that is not
/// `True`/`False` (the case `try_simp_ite` does NOT collapse) left the
/// instance at the old proposition.
///
/// Dependence is read off the telescope INSTANTIATED with the arguments
/// actually supplied and beta-reduced, not off the declared binder types
/// alone. Lean reads the declared ones (`getFunInfoNArgs`) and can afford to:
/// its `simp [f]` unfolds a `match`-defined `f` through equation lemmas, so a
/// recursor reaches its congruence step only with a constructor major. Clean's
/// `simp [f]` delta-unfolds (`unfold_named_consts`), so `bnot P` becomes
/// `Bool.casesOn (fun _ => Bool) P true false` with `P` still a variable, and
/// on the DECLARED telescope that major is mentioned by the result type
/// `motive t` — frozen, so `hp : P = true` never reached it and the
/// hypothesis stalled one iota short of its goal
/// (`proofs/trust-soundness/chc_tarski_unbounded.lean` `mp_eq`, the ouroboros
/// gate; measured with `CLEAN_SIMP_SPINE_TRACE`: `head=Bool.casesOn
/// frozen=[true, true, false, false]`). With `motive := fun _ => Bool`
/// supplied, `motive t` beta-reduces to `Bool`: nothing depends on `t`,
/// `congrArg (Bool.casesOn motive) hp` is well-typed, and that is exactly the
/// condition the kernel checks. A motive that genuinely depends on the major
/// (`mkT : (b : Bool) → T b`) still freezes it. Instantiation can only ERASE
/// a dependence the declared telescope states, never add one, so the
/// instantiated check runs only for the positions the declared scan marks.
///
/// Returns `None` when the head is not a constant with a readable telescope;
/// the caller then keeps the historical binary split.
fn frozen_arg_positions(state: &ProofState, head: &Expr, args: &[&Expr]) -> Option<Vec<bool>> {
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };
    let info = state.env.get_const(name)?;
    let arity = args.len();
    let mut domains: Vec<Expr> = Vec::new();
    let mut infos: Vec<BinderInfo> = Vec::new();
    let mut current = info.type_.clone();
    for _ in 0..arity {
        let ExprKind::Pi(binder, domain, codomain) = current.kind() else {
            break;
        };
        domains.push(domain.as_ref().clone());
        infos.push(binder.info);
        current = codomain.as_ref().clone();
    }
    let declared = domains.len();
    if declared == 0 {
        return None;
    }
    // An OVER-applied head (`(dite α P inst f g) a`, whose `α` is itself a
    // function type) is left to the binary split, which reaches the prefix
    // `dite α P inst f g` as a node of its own — where `try_simp_dite` runs
    // first and this analysis then applies at the arity the telescope
    // declares. Handling it here instead would skip that node entirely and
    // the `dite` collapse with it (measured: `Function.dite_apply`'s
    // `(dite P f g) a` shape, `tests_simp_dite_collapse.rs`).
    if declared < arity {
        return None;
    }
    let mut frozen = vec![false; arity];
    for i in 0..declared {
        // An instance-implicit slot is Lean's `subsingletonInst`: it is
        // transported, never rewritten, because its value is irrelevant and
        // its TYPE is pinned by the arguments it mentions.
        if infos[i] == BinderInfo::InstImplicit {
            frozen[i] = true;
            continue;
        }
        // Binder `i` is seen from binder `j` as the loose index `j - i - 1`,
        // and from the result type (after `declared` binders) as
        // `declared - i - 1`.
        let mentioned_later = ((i + 1)..declared)
            .any(|j| crate::tactic::bvar_ops::has_loose_bvar(&domains[j], (j - i - 1) as u32));
        let mentioned_in_result =
            crate::tactic::bvar_ops::has_loose_bvar(&current, (declared - i - 1) as u32);
        frozen[i] = (mentioned_later || mentioned_in_result)
            && argument_has_dependents(&info.type_, args, i);
    }
    Some(frozen)
}

/// Whether a LATER argument's type, or the application's type, still mentions
/// argument `index` once `telescope` is instantiated with `args` and
/// beta-reduced. The argument at `index` is replaced by a sentinel local so
/// its occurrences survive the instantiation; every other argument is
/// substituted as supplied, which is what lets a constant motive erase the
/// dependence its declared binder type states.
///
/// REQUIRES: `telescope` has at least `args.len()` leading `Pi` binders (the
///   caller's declared scan established it).
fn argument_has_dependents(telescope: &Expr, args: &[&Expr], index: usize) -> bool {
    // Above every local the elaborator can mint (they are allocated upward
    // from 0) and below the metavariable tag (the top bit), so no supplied
    // argument can carry it.
    let sentinel = FVarId::new((1u64 << 63) - 1);
    let mut rest = telescope.clone();
    for (position, arg) in args.iter().enumerate() {
        let ExprKind::Pi(_, domain, codomain) = rest.kind() else {
            return false;
        };
        if position > index && mentions_fvar_after_beta(domain, sentinel) {
            return true;
        }
        let value = if position == index {
            Expr::fvar(sentinel)
        } else {
            (*arg).clone()
        };
        rest = crate::tactic::bvar_ops::instantiate(codomain, &value);
    }
    mentions_fvar_after_beta(&rest, sentinel)
}

fn mentions_fvar_after_beta(expr: &Expr, id: FVarId) -> bool {
    // Beta and let reduction can erase a free variable, but cannot introduce
    // one absent from the input. A possible or unknown bound needs the fold.
    if !expr.may_contain_fvar_at_or_above(id) {
        return false;
    }
    #[cfg(test)]
    dependency_tests::BETA_FOLDS.with(|count| count.set(count.get() + 1));
    mentions_fvar(&beta_reduce(expr), id)
}

#[cfg(test)]
#[path = "dependency_tests.rs"]
mod dependency_tests;

/// Whether the local `id` occurs in `expr`.
fn mentions_fvar(expr: &Expr, id: FVarId) -> bool {
    match expr.kind() {
        ExprKind::FVar(fid) => *fid == id,
        ExprKind::App(f, a) => mentions_fvar(f, id) || mentions_fvar(a, id),
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            mentions_fvar(ty, id) || mentions_fvar(body, id)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            mentions_fvar(ty, id) || mentions_fvar(val, id) || mentions_fvar(body, id)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            mentions_fvar(inner, id)
        }
        _ => false,
    }
}

/// Rewrite an application ARGUMENT BY ARGUMENT, leaving the positions
/// [`frozen_arg_positions`] marks untouched.
///
/// Returns `None` — deliberately leaving the caller's binary split in charge —
/// only when the head has no readable telescope or no position is frozen. When
/// a position IS frozen this returns `Some`, even for an unchanged expression:
/// the caller must not fall back to the binary split, which would descend into
/// the prefix `D P` as its own node and rewrite `P` there, where nothing knows
/// a later sibling depends on it. So the blast radius is exactly "applications
/// with a dependent argument position", and nothing else.
fn simp_app_spine(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
    budget: &SimpBudget,
) -> Option<SimpResult> {
    let head = expr.get_app_fn();
    let args = expr.get_app_args();
    if args.is_empty() {
        return None;
    }
    // Diagnostic sibling of `CLEAN_SIMP_MATCH_TRACE` /
    // `CLEAN_SIMP_HEAD_GUARD_TRACE`: print which head this analysis could read
    // a telescope for and which positions it froze. Trace-only; never changes
    // the verdict. It is what showed the freeze was being UNDONE on the second
    // pass before the early return below existed.
    let spine_trace = std::env::var_os("CLEAN_SIMP_SPINE_TRACE").is_some();
    let frozen = match frozen_arg_positions(state, head, &args) {
        Some(frozen) => frozen,
        None => {
            if spine_trace {
                eprintln!("simp-spine: no telescope for head {head:?}");
            }
            return None;
        }
    };
    if spine_trace {
        eprintln!("simp-spine: head={head:?} frozen={frozen:?}");
    }
    if !frozen.iter().any(|f| *f) {
        return None;
    }

    // The head itself is still simplified: the binary split reached it at its
    // innermost node, and `simp [myDef]`'s delta-unfold lives there.
    let head_result = stack_safe(|| simp_expr_budgeted(state, goal, head, lemmas, config, budget));
    let mut old_fn = head.clone();
    let mut new_fn = head_result.expr;
    let mut fn_proof = head_result.proof;

    for (index, arg) in args.iter().enumerate() {
        let (new_arg, arg_proof) = if frozen[index] {
            ((*arg).clone(), None)
        } else {
            let arg_result =
                stack_safe(|| simp_expr_budgeted(state, goal, arg, lemmas, config, budget));
            (arg_result.expr, arg_result.proof)
        };
        if old_fn == new_fn {
            if let Some(step) = arg_proof.as_ref().and_then(|proof| {
                super::iota::reduce_after_argument_rewrite(
                    state, goal, expr, index, &new_arg, proof, budget,
                )
            }) {
                return Some(step);
            }
        }
        let old_app = Expr::app(old_fn.clone(), (*arg).clone());
        let new_app = Expr::app(new_fn.clone(), new_arg.clone());
        let app_proof = if old_app == new_app {
            None
        } else {
            match (&fn_proof, &arg_proof) {
                (Some(h_f), Some(h_a)) => {
                    mk_congr(state, goal, &old_fn, &new_fn, arg, &new_arg, h_f, h_a)
                }
                (Some(h_f), None) => mk_congr_fun(state, goal, &old_fn, &new_fn, arg, h_f),
                (None, Some(h_a)) => mk_congr_arg(state, goal, &old_fn, arg, &new_arg, h_a),
                (None, None) => None,
            }
        };
        old_fn = old_app;
        new_fn = new_app;
        fn_proof = app_proof;
    }

    // The same defense-in-depth guard the binary split carries: an assembled
    // congruence proof that does not prove `expr = new_fn` is dropped rather
    // than emitted.
    let proof = match fn_proof {
        Some(p)
            if !new_fn.has_loose_bvars()
                && !p.has_loose_bvars()
                && !proof_matches_rewrite(state, goal, &p, expr, &new_fn) =>
        {
            None
        }
        other => other,
    };
    Some(SimpResult {
        expr: new_fn,
        proof,
    })
}

/// The child-recursion phase of one simp frame: recurse into subexpressions,
/// building congruence proofs. Returns the frame's input `result` untouched
/// when no child changed. Split out of `simp_expr_inner` so the node-level
/// lemma/simproc rewriting can run AFTER it (post-order, Lean parity).
/// Lean's `Simp.isOfNatNatLit`: `@OfNat.ofNat α n inst` with exactly three
/// arguments and a raw `Nat` literal `n`.
pub(super) fn is_of_nat_nat_lit(e: &Expr) -> bool {
    let ExprKind::Const(head, _) = e.get_app_fn().kind() else {
        return false;
    };
    let args = e.get_app_args();
    args.len() == 3
        && *head == Name::from_string("OfNat.ofNat")
        && matches!(
            args[1].kind(),
            ExprKind::Lit(clean_kernel::expr::Literal::Nat(_))
        )
}

fn simp_children(
    state: &ProofState,
    goal: &Goal,
    result: SimpResult,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
    budget: &SimpBudget,
) -> SimpResult {
    // Lean's `simpApp` (`Simp/Main.lean:580`): an `OfNat.ofNat α n inst`
    // node with a raw literal `n` is a numeral and is NOT visited — neither
    // its type, its literal nor its instance. Descending into it let simp
    // unfold a non-canonical instance (`instance weird : OfNat Nat 5 :=
    // ⟨7⟩`) and read `(5 : Nat)` as `7`, closing `h : (5 : Nat) < 6 ⊢ False`
    // where pinned Lean 4.8.0 leaves "unsolved goals" (review r4t q1). The node
    // itself is still rewritten by lemmas and simprocs, as in Lean.
    if is_of_nat_nat_lit(&result.expr) {
        return result;
    }
    match result.expr.kind() {
        ExprKind::App(f, arg) => {
            // Rewrite an ite condition together with its dependent Decidable
            // instance before generic application congruence. Ordinary
            // ite_congr transport is available to simp only; branch collapse
            // remains scoped to the reduceIte simproc or named rewrite lemmas.
            if let Some(ite_step) = try_simp_ite(state, goal, &result.expr, lemmas, config, budget)
            {
                return mk_eq_trans(result, ite_step, state, goal);
            }
            // The dependent twin: `@dite α c inst t e` collapses to `t hc` /
            // `e hnc` via `dif_pos`/`dif_neg` — see `try_simp_dite`. Lean's
            // `reduceDite`.
            if config.simprocs.runs_dite_collapse() {
                if let Some(dite_step) =
                    try_simp_dite(state, goal, &result.expr, lemmas, config, budget)
                {
                    return mk_eq_trans(result, dite_step, state, goal);
                }
            }

            // Lean's `congrArgs` (`Meta/Tactic/Simp/Types.lean`) asks
            // `getFunInfoNArgs` for the head's parameter info and rewrites an
            // argument with a PROOF only when `!info.hasFwdDeps`; a position
            // other arguments (or the result type) depend on is rebuilt
            // definitionally. The binary `App(f, arg)` split below cannot
            // express that — at this node `arg` is the LAST argument of its own
            // prefix, so "does a LATER argument mention it" is a question only
            // the whole spine can answer. `simp_app_spine` answers it, and
            // returns `None` whenever no position is frozen, which leaves the
            // historical path in charge of every other application.
            // An application with a frozen position is handled ENTIRELY here:
            // falling through to the binary split would re-enter the prefix
            // `D P` as its own node, where `P` is the last argument and nothing
            // knows a later sibling depends on it — the rewrite would land on
            // the second pass instead of the first (measured).
            if let Some(spine) = simp_app_spine(state, goal, &result.expr, lemmas, config, budget) {
                if spine.expr == result.expr && spine.proof.is_none() {
                    return result;
                }
                return mk_eq_trans(result, spine, state, goal);
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
                let lambda = Expr::lam(*bi, ty.as_ref().clone(), new_body);
                // Simplifying the body can expose an eta redex. Contract
                // it before parent patterns choose a less specific rule.
                let expression = if config.eta {
                    eta_reduce_fixpoint(&lambda)
                } else {
                    lambda
                };
                let lam_result = SimpResult {
                    expr: expression,
                    proof: lam_proof,
                };
                return mk_eq_trans(result, lam_result, state, goal);
            }
        }
        ExprKind::Pi(bi, ty, body) => {
            let ty_result =
                stack_safe(|| simp_expr_budgeted(state, goal, ty, lemmas, config, budget));
            // A DEPENDENT `∀ (h : A), B h` may not have its domain rewritten
            // here: the body keeps its `h : A` occurrences, so `∀ (h : True),
            // B h` with `B : A → Prop` is ill-typed and `mk_pi_domain_congr`
            // refuses to prove it (`contains_bvar(body, 0)`), leaving a claimed
            // DEFINITIONAL change the kernel then kills the declaration over.
            // Lean's `simpForall` (`Meta/Tactic/Simp/Main.lean`) rewrites such
            // a domain only through `forall_prop_domain_congr`, which
            // transports the body's bound-proof occurrences with `h₁.substr`;
            // Clean has no such transport, so the domain is left alone and the
            // BODY is simplified under the original domain — Lean's own
            // non-Prop path. A domain change carrying NO proof is genuinely
            // definitional, so the body stays well-typed and is still taken.
            let body_depends = crate::tactic::bvar_ops::has_loose_bvar(body, 0);
            if ty_result.expr != **ty && !(body_depends && ty_result.proof.is_some()) {
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
            // Lean's `simpProj` (`Simp/Main.lean:299`) tries `reduceProj?`
            // BEFORE it descends, so a projection whose structure argument is
            // already a constructor application — or an instance constant that
            // unfolds to one at reducible+instances transparency — never
            // survives to be rebuilt by congruence. Without this step the node
            // was left stuck forever: see `super::proj_reduce`.
            //
            // Definitional (ι), hence `proof: None`, exactly like the
            // delta/beta/eta rewrites at the top of `simp_expr_inner`; and
            // charged to the budget for the same reason they are, because a
            // projected field can be arbitrarily large.
            if let Some(reduced) = super::proj_reduce::reduce_proj(state, goal, &result.expr) {
                if budget.admit(&reduced, format_args!("reducing projection {name}.{idx}")) {
                    let iota = SimpResult {
                        expr: reduced,
                        proof: None,
                    };
                    return mk_eq_trans(result, iota, state, goal);
                }
            }
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
                let rebuilt = mk_eq_trans(result, proj_result, state, goal);
                // Lean re-tries `reduceProj?` on the rebuilt node: simplifying
                // the structure argument is precisely what can expose the
                // constructor. Chained as a SECOND step so the congruence
                // proof keeps stating the equation it actually proves —
                // `mk_eq_trans` keeps the left proof when the right step is
                // definitional, which is sound because the two right-hand
                // sides are def-eq and `Eq`'s type is checked up to def-eq.
                if let Some(reduced) = super::proj_reduce::reduce_proj(state, goal, &rebuilt.expr) {
                    if budget.admit(&reduced, "reducing a projection after its argument") {
                        let iota = SimpResult {
                            expr: reduced,
                            proof: None,
                        };
                        return mk_eq_trans(rebuilt, iota, state, goal);
                    }
                }
                return rebuilt;
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
pub(super) fn peel_ite(expr: &Expr) -> Option<(Level, Expr, Expr, Expr, Expr, Expr)> {
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

/// The equation `h₁ : c = c'` the `ite`/`dite` collapse transports along,
/// where `c'` is what simp made of the condition `c`.
///
/// A rewritten condition carries its proof. An UNCHANGED (or only
/// definitionally changed) one carries none, and collapses only in a scope
/// that runs Lean's `reduceIte`/`reduceDite`
/// ([`super::types::SimprocScope::collapses_literal_condition`]), which
/// `simp`s the condition and tests the RESULT (`r.expr.isTrue`, with
/// `r.getProof` falling back to `rfl`). Its proof is then
/// `@Eq.refl.{1} Prop c'`: the kernel accepts it at `c = c'` exactly when `c`
/// is definitionally `c'`, which is what a proof-free simp step claims.
fn condition_equation(cond_result: &SimpResult, config: &SimpConfig) -> Option<Expr> {
    if let Some(proof) = &cond_result.proof {
        return Some(proof.clone());
    }
    if !config.simprocs.collapses_literal_condition() {
        return None;
    }
    Some(Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [Expr::prop(), cond_result.expr.clone()],
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
    // carries a proof `h₁ : c = c'`. A condition that is already
    // `True`/`False` collapses here only in a `reduceIte` scope
    // (`condition_equation`); under Clean's default scope the top-level
    // `ite_true`/`ite_false` lemma and the simproc table's `ite` instance
    // evaluation handle it, so requiring a proof there loses no coverage.
    let cond_result = stack_safe(|| simp_expr_budgeted(state, goal, &c, lemmas, config, budget));
    if !config.simprocs.runs_ite_collapse() {
        return super::conditional_congr::rewrite_condition(
            state,
            goal,
            expr,
            &cond_result,
            budget,
        );
    }
    let Some(h1) = condition_equation(&cond_result, config) else {
        return super::conditional_congr::rewrite_condition(
            state,
            goal,
            expr,
            &cond_result,
            budget,
        );
    };
    let h1 = &h1;

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

    // A non-deciding condition rewrite still admits dependent congruence.
    super::conditional_congr::rewrite_condition(state, goal, expr, &cond_result, budget)
}

/// Is `e` a proof — is its type a proposition? Lean's `Meta.isProof`.
///
/// Types (`Sort`, `Π`) and literals are never proofs and are answered without
/// inference; a term with loose bound variables (simp descending under a
/// binder it has not opened) or one whose type cannot be inferred is treated
/// as NOT a proof, which is the pre-existing behaviour — the check can only
/// make simp leave more alone, never less.
fn is_proof_term(state: &ProofState, goal: &Goal, e: &Expr) -> bool {
    if matches!(
        e.kind(),
        ExprKind::Sort(_) | ExprKind::Pi(..) | ExprKind::Lit(_) | ExprKind::BVar(_)
    ) || e.has_loose_bvars_quick()
    {
        return false;
    }
    let Ok(ty) = state.infer_type(goal, e) else {
        return false;
    };
    let Ok(sort) = state.infer_type(goal, &ty) else {
        return false;
    };
    matches!(state.whnf(goal, &sort).kind(), ExprKind::Sort(l) if l.is_zero())
}

/// `@dite.{u} α c inst t e` as `(u, α, c, inst, t, e)`; the dependent twin of
/// [`peel_ite`].
fn peel_dite(expr: &Expr) -> Option<(Level, Expr, Expr, Expr, Expr, Expr)> {
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
    if name.to_string() != "dite" {
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

/// dite-condition congruence under a dependent `Decidable` instance — the
/// twin of [`try_simp_ite`] for `@dite α c inst t e`, whose branches TAKE the
/// decision: when the condition rewrites to `True` (resp. `False`) the term
/// collapses to `t hc` (resp. `e hnc`) via `dif_pos`/`dif_neg`, keeping the
/// original symbolic `c` and `inst` on the equation's left. Without this the
/// generic App recursion rewrote only the condition and left `inst :
/// Decidable c` beside `dite True …` — `expected Decidable True, got
/// Decidable P` (`by_cases h : P <;> simp [h]` in `apply_dite₂`, `dite_apply`,
/// `dite_mem`, `mem_dite`, `Mathlib/Logic/Basic.lean`, measured 2026-09-11).
/// The applied branch is head-beta-reduced, as simp's own beta step would.
///
/// `dif_pos`/`dif_neg` live in `Init.Core`, not the built-in prelude: with
/// neither present the collapse is skipped and the term is left untouched
/// (the pre-existing behaviour), never fabricated.
fn try_simp_dite(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
    budget: &SimpBudget,
) -> Option<SimpResult> {
    let (u, alpha, c, inst, t, e) = peel_dite(expr)?;
    let dif_pos = Name::from_string("dif_pos");
    let dif_neg = Name::from_string("dif_neg");
    if state.env.get_const(&dif_pos).is_none() || state.env.get_const(&dif_neg).is_none() {
        return None;
    }

    let cond_result = stack_safe(|| simp_expr_budgeted(state, goal, &c, lemmas, config, budget));
    let h1 = condition_equation(&cond_result, config)?;
    let h1 = &h1;

    let true_c = Expr::const_(Name::from_string("True"), vec![]);
    let false_c = Expr::const_(Name::from_string("False"), vec![]);

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
        // @dif_pos.{u} {c} {inst} hc {α} {t} {e} : @dite α c inst t e = t hc
        let proof = Expr::apps(
            Expr::const_(dif_pos, vec![u]),
            [c, inst, hc.clone(), alpha, t.clone(), e],
        );
        let branch = crate::tactic::op_projection::head_beta(&Expr::app(t, hc));
        return Some(SimpResult {
            expr: branch,
            proof: Some(proof),
        });
    }

    if cond_result.expr == false_c {
        // hnc := @Eq.mp.{0} c False h₁ : c → False
        let hnc = Expr::apps(
            Expr::const_(Name::from_string("Eq.mp"), vec![Level::zero()]),
            [c.clone(), false_c.clone(), h1.clone()],
        );
        // @dif_neg.{u} {c} {inst} hnc {α} {t} {e} : @dite α c inst t e = e hnc
        let proof = Expr::apps(
            Expr::const_(dif_neg, vec![u]),
            [c, inst, hnc.clone(), alpha, t, e.clone()],
        );
        let branch = crate::tactic::op_projection::head_beta(&Expr::app(e, hnc));
        return Some(SimpResult {
            expr: branch,
            proof: Some(proof),
        });
    }

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
    // A `∀`/`→` pattern matches only a `∀`/`→` subterm. Lean matches at
    // reducible transparency, where `Not` (a plain `def`) does not unfold, so
    // `imp_false`'s `?a → False` never matches `¬q`; Clean's prelude marks
    // `Not` reducible, and the pattern rewrote `¬¬p` to `¬(p → False)` (G39).
    if matches!(lemma.lhs.kind(), ExprKind::Pi(..))
        && !matches!(match_target.kind(), ExprKind::Pi(..))
    {
        return true;
    }
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
    // Every attempt is charged to the declaration's automation work budget
    // (Lean's `Simp.simpLoop` calls `checkSystem "simp"` per step). A refused
    // charge trips `budget`, and the enclosing frames unwind fail-closed.
    if !budget.charge_attempt() {
        return None;
    }
    if star_noise_head_guard_refuses(lemma, target.head_guard_target()) {
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
    let mtrace = slot_trace(lemma);
    let mut metas = MetaState::new();
    // Pattern metas are scoped to the GOAL's locals (elab locals + goal ctx):
    // a pattern variable must be allowed to bind a goal subterm mentioning a
    // goal FVar (`?n := a` for `a * 1`), while binder-opened temporaries stay
    // rejected by the unifier's scope check (B102).
    let pattern_scope = state.meta_scope_for_context(&goal.local_ctx);
    // Lean's `SimpTheorem.getValue`: THIS use of the lemma gets fresh level
    // metavariables in place of its declared universe parameters (see
    // `lemma_levels`), and the goal's own parameters are rigid for the
    // attempt, so matching can solve the lemma's levels and nothing else.
    // Without it the pattern spelled the declaration's own names, the
    // name-keyed `MetaState` could not tell a lemma `u_1` matching never
    // touched from one unified with the goal's SAME-NAMED `u_1`, and every
    // universe-polymorphic `Iff` template was refused outright.
    let levels = LemmaLevels::for_lemma(state, lemma);
    if !levels.is_empty() {
        metas.set_rigid_level_params(target.level_params().iter().cloned());
    }
    let lhs_pattern = levels.rename(&lemma.lhs);
    let (pattern_with_metas, mut bvar_to_meta) =
        convert_bvars_to_metas(&lhs_pattern, &mut metas, &pattern_scope);

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
    // Dot notation can elaborate a lemma LHS as an applied lambda. The
    // target traversal already beta-reduced its application and its arguments.
    // Use the same bounded reduction on this shape before matching heads, so
    // nested applications in the lambda body also acquire their stated heads.
    // Proof reconstruction below still instantiates the original lemma LHS.
    let beta_pattern = if config.beta
        && matches!(pattern_with_metas.kind(), ExprKind::App(..))
        && matches!(pattern_with_metas.get_app_fn().kind(), ExprKind::Lam(..))
    {
        if !budget.admit_before_zeta(
            &pattern_with_metas,
            format_args!("preparing the pattern of lemma {}", lemma.name),
        ) {
            return None;
        }
        let reduced = beta_reduce(&pattern_with_metas);
        if !budget.admit(
            &reduced,
            format_args!("preparing the pattern of lemma {}", lemma.name),
        ) {
            return None;
        }
        Some(reduced)
    } else {
        None
    };
    let match_pattern = beta_pattern.as_ref().unwrap_or(&pattern_with_metas);
    let peeled_pattern = peel_pattern_to_target_head(state, goal, match_pattern, match_target);
    let match_pattern = peeled_pattern.as_ref().unwrap_or(match_pattern);
    // The target's literal collapse also runs when its outer head is a
    // predicate or local function. The projection peel above returns None
    // when heads already agree, so it alone leaves nested OfNat wrappers in
    // patterns such as P (n + 1). Normalize those leaves on both sides; the
    // original-pattern equality and assembled-proof checks below still apply.
    let literal_pattern = collapse_nat_ofnat_literals(match_pattern);
    let match_pattern = literal_pattern.as_ref().unwrap_or(match_pattern);

    // ETA — the same one-sided normalization, on the step `simp_expr_inner`
    // has ALREADY applied to the goal subterm and never applied to the
    // pattern. `eta_reduce` is a folder, so the target subtree reaches the
    // matcher fully eta-reduced while a lemma's stored LHS does not, and the
    // two sides then differ on nothing but that.
    //
    // The measured row is `Mathlib/Logic/Basic.lean:dite_ne_right_iff`. Every
    // imported lemma whose LHS came from `if h : p then x h else y` carries an
    // ETA-EXPANDED then-branch, because that notation elaborates that way:
    // `dite_eq_right_iff`'s pattern is
    // `@dite α ?p ?inst (fun h => ?x h) (fun _ => ?y) = ?y`, while a goal whose
    // then-branch is a bare local reads `@dite α p inst A (fun _ => b) = b`.
    // Matching them needs `fun h => ?x h =?= A`, and the unifier's eta arm
    // (`unify_expr.rs`, `eta_expand_other`) reads the non-lambda side's domain
    // out of `tc.infer_type(other)` — which for a GOAL LOCAL fails, because
    // the matcher's unifier is built over an empty kernel context and the
    // kernel answers `UnknownFVar`. The arm then falls through to
    // `try_kernel_def_eq`, which cannot assign a metavariable, and the
    // candidate dies as a shape bail:
    // `cannot unify a lambda with a free variable: fun (x : ?p) => ?x x vs fvar#3`.
    //
    // Reducing the pattern makes the eta arm unnecessary rather than making it
    // work: `fun h => ?x h` contracts to `?x`, which the first-order matcher
    // assigns directly. HANDING THE UNIFIER THE GOAL'S LOCAL CONTEXT INSTEAD
    // WAS TRIED AND REVERTED — it is what the diagnosis proposed, and it
    // regressed NINE universe-polymorphic lemma-matching tests
    // (`tests_simp_lemma_levels`, `tests_simp_instance_args`,
    // `tests_simp_lemma_rows`, …, measured 527 passed / 0 failed before,
    // 518 / 9 after). The reason is that the context is not read by the eta
    // arm alone: `propagate_meta_type_levels` and `expr_sort_level`
    // (`unify/unifier/mod.rs`) both bail on a failed `infer_type`, so giving
    // them a context that types goal locals silently turns level propagation
    // ON for every match. That is a change to LEVEL SOLVING, not to eta, and
    // it needs its own measurement; this normalization closes the measured row
    // without touching it.
    //
    // Gated on `config.eta` so pattern and target are always normalized by the
    // SAME steps: with eta off, neither side is reduced.
    //
    // TO A FIXPOINT, which is not the same as one call. `eta_reduce` contracts
    // at most one binder per `Lam` node — its folder rebuilds the node from an
    // already-folded body and never re-examines what it just built — so
    // `fun a b => ?x a b` lands on `fun a => ?x a` and stops one binder short.
    // The TRAVERSAL never notices, because simp's outer loop re-simplifies the
    // rewritten target and collects the fixpoint over passes; the MATCHER gets
    // no second pass, since the pattern is re-derived from `lemma.lhs` on every
    // attempt and the same single contraction happens again. Lean contracts to
    // a fixpoint on both of its own paths — `DiscrTree/Main.lean`'s `reduce`
    // re-enters on every `etaExpandedStrict?` hit, and `isDefEqEta` peels one
    // binder per recursive call — and the pinned v4.30.0-rc2 closes the
    // two-binder analogue of the measured row, which without this loop reports
    // `simp: no progress made`
    // (`tests/simp_proj_eta_adversarial_e2e.rs`,
    // `test_simp_eta_matches_a_two_binder_goal_local_function`).
    let eta_pattern = config.eta.then(|| eta_reduce_fixpoint(match_pattern));
    let match_pattern = match eta_pattern.as_ref() {
        Some(reduced) if reduced != match_pattern => reduced,
        _ => match_pattern,
    };

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

    let normalized = match_successor_arguments(state, goal, match_pattern, match_target, budget);
    let unification_target = normalized.as_ref().unwrap_or(match_target);
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
        unifier.unify_no_initial_whnf(match_pattern, unification_target)
    };

    match unify_result {
        UnifyResult::Success => {
            // A level only a BINDER TYPE mentions is invisible to matching
            // (`implies_true.{u} (α : Sort u)`'s pattern is `?α → True`); Lean
            // solves it when it type-checks the assignment `?α := Nat`. Solve
            // it the same way, from the bound arguments' types, before any
            // guard reads an instantiated term.
            if levels.has_unsolved(&metas) {
                if let Some(info) = state.env.get_const(&lemma.name) {
                    if statement_yields_pattern(&info.type_, &lemma.lhs) {
                        levels.solve_from_bound_argument_types(
                            state,
                            goal,
                            &info.type_,
                            &mut metas,
                            &bvar_to_meta,
                        );
                    }
                }
            }

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
            let lhs_with_metas = substitute_bvars_with_metas(&lhs_pattern, &bvar_to_meta);
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

            // TYPE DISCIPLINE on the bindings the match just made. Pattern
            // metas are minted with the placeholder type `Expr::type_()`
            // (`pattern.rs`) and `MetaState::assign` never type-checks, so a
            // lemma binder declared `(p : Prop)` will happily capture a goal
            // subterm of type `Sort v`. No guard above objects — `lhs_inst ≡
            // expr` is satisfied (it IS the same term) and
            // `proof_matches_rewrite` runs the non-checking `infer_type` — so
            // the ill-typed proof reaches `close_goal`'s `infer_type_strict`
            // and kills the whole declaration with `expected Sort(Zero),
            // inferred Sort(Param ..)`. Worse, the bad candidate is tried
            // BEFORE the correct universe-polymorphic one, which therefore
            // never runs. Refusing here restores that ordering: simp reports
            // "this lemma did not apply" and moves on. Runs after the cheap
            // `lhs_inst ≡ expr` guard so a spurious match never pays for the
            // telescope walk.
            if binding_violates_declared_domain(state, goal, lemma, &levels, &metas, &bvar_to_meta)
            {
                return None;
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
                &levels,
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
            let rhs_pattern = levels.rename(&lemma.rhs);
            let rhs_with_metas = substitute_bvars_with_metas(&rhs_pattern, &bvar_to_meta);
            let result = inst(&rhs_with_metas);
            if contains_unassigned_meta(&result) {
                if mtrace {
                    eprintln!("simp-match: lemma={} REJECT result-meta-leak", lemma.name);
                }
                return None;
            }
            // A level only the RIGHT-hand side mentions is fixed by nothing;
            // the rewrite would hand the goal a level metavariable.
            if levels.mentions_unsolved(&result) {
                if mtrace {
                    eprintln!("simp-match: lemma={} REJECT result-level", lemma.name);
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
                // Every lemma binder the template applies must be BOUND. A
                // template's loose de Bruijn indices are exactly the lemma's
                // binders (`mk_iff_rewrite_proof_template` applies all of
                // them), and `substitute_bvars_with_metas` leaves an unbound
                // one in place. An `Iff` lemma whose binder neither the match
                // nor the discharger determined (`[Inh1 α]` in
                // `PP x ↔ True`) was measured by the work package being
                // ACCEPTED and the kernel then aborting the whole declaration
                // with "Unbound variable index: 1"; `proof_matches_rewrite`
                // is no guarantee here, since the non-checking `infer_type`
                // of `propext l r h` need not look at `h`. Lean refuses the
                // rewrite when the instantiated proof still holds an
                // assignable metavariable (`Rewrite.lean`, `tryTheoremCore`:
                // "failed, proof contains metavariables"); this is that
                // refusal, stated before the template is ever instantiated,
                // so it holds whatever the later checks happen to see.
                if !template_binders_bound(proof_expr, &bvar_to_meta) {
                    if mtrace {
                        eprintln!(
                            "simp-match: lemma={} REJECT template-unbound-binder",
                            lemma.name
                        );
                    }
                    return None;
                }
                // Prebuilt templates (`mk_iff_rewrite_proof_template`) are
                // assembled at REGISTRATION time and spell the declaration's
                // own universe parameters. For an environment lemma those are
                // renamed to this attempt's fresh levels and instantiated
                // from the match — Lean's `getValue` — so the template stands
                // for the declaration at the levels the goal needs. They used
                // to be substituted for BVARS only, which left every
                // universe-polymorphic `↔` lemma spelling its own parameter
                // and refused wholesale as `template-level` (`eq_comm`,
                // `forall_eq'`, `Classical.not_forall`, `Pi.le_def`, …).
                //
                // A LOCAL rule's template spells the goal's own levels, which
                // matching must not re-spell, so it keeps expression-only
                // instantiation (its levels are the goal's by construction).
                let proof_with_metas =
                    substitute_bvars_with_metas(&levels.rename(proof_expr), &bvar_to_meta);
                let proof = if levels.is_empty() {
                    metas.instantiate(&proof_with_metas)
                } else {
                    inst(&proof_with_metas)
                };
                // A level still unsolved after that — a fresh name the match
                // and the argument types left open — would make an ill-typed
                // term that `proof_matches_rewrite` cannot catch (`infer_type`
                // is the non-checking fast path) and only the kernel rejects,
                // killing the whole declaration. Refuse it here so simp merely
                // reports that the lemma did not apply. A rule with no renaming
                // (a local shadowing a constant's name) keeps the declared-name
                // test it always had.
                let unsolved = if levels.is_empty() {
                    let declared: Vec<Name> = state
                        .env
                        .get_const(&lemma.name)
                        .map(|info| info.level_params.clone())
                        .unwrap_or_default();
                    !declared.is_empty() && template_has_unsolved_level(&proof, &declared)
                } else {
                    levels.mentions_unsolved(&proof)
                };
                if unsolved {
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
                // For an ENVIRONMENT lemma (`simp [X]`, `simp only [X]`, the
                // `@[simp]` registry) the declared parameters were renamed to
                // this attempt's fresh levels before matching (Lean's
                // `SimpTheorem.getValue`, see `lemma_levels`), so each resolves
                // to whatever matching and the bound arguments' types solved
                // it to — a concrete level, the goal's own `u_1`, a compound —
                // and a fresh name that comes back is exactly an unsolved
                // level. 37% of Lean core's `@[simp]` set is
                // universe-polymorphic (RC-E.1), so this is most of the
                // imported simp set.
                //
                // Clean's HAND-WRITTEN builtin patterns
                // (`simp/lemmas_builtin.rs`) spell a single pattern-local
                // `Level::Param("u_simp")` (`Eq.{u_simp}`, `ite.{u_simp}`,
                // `List.append_nil.{u_simp}`) that no declaration has, so a
                // fresh level they leave unsolved falls back to `u_simp`'s
                // solution. A rule with no renaming — no universe parameters,
                // or a local shadowing a constant's name — keeps the
                // declared-name resolution it always had.
                let declared: Vec<Name> = state
                    .env
                    .get_const(&lemma.name)
                    .map(|info| info.level_params.clone())
                    .unwrap_or_default();
                let lemma_levels: Vec<Level> = if levels.is_empty() {
                    declared
                        .iter()
                        .map(|param| resolve_lemma_level(&metas, param))
                        .collect()
                } else {
                    let builtin = builtin_pattern_level(&metas);
                    levels
                        .resolved(&metas)
                        .into_iter()
                        .map(|lvl| match &builtin {
                            Some(solved) if levels.level_is_unsolved(&lvl) => solved.clone(),
                            _ => lvl,
                        })
                        .collect()
                };
                // FAIL CLOSED on an unsolved lemma universe. A parameter that
                // neither matching nor the argument types fixed —
                // `implies_true.{u} (α : Sort u) : (α → True) = True` over an
                // argument whose sort cannot be inferred — used to be emitted
                // as the declaration's own raw `Param("u")`
                // (`@implies_true.{u} Nat`), which the kernel rejected,
                // killing the whole declaration; the guard below cannot catch
                // it, because `infer_type` is the NON-checking fast path and
                // never checks an application's argument against its binder
                // domain. Refusing turns that into an ordinary "this lemma did
                // not apply".
                let unsolved_leak = if levels.is_empty() {
                    lemma_levels.iter().any(
                        |lvl| matches!(lvl, Level::Param(p) if declared.iter().any(|d| d == p)),
                    )
                } else {
                    lemma_levels.iter().any(|lvl| levels.level_is_unsolved(lvl))
                };
                if unsolved_leak {
                    if mtrace {
                        eprintln!("simp-match: lemma={} REJECT unsolved-level", lemma.name);
                    }
                    return None;
                }
                let max_bvar = bvar_to_meta.keys().copied().max().map_or(0, |m| m + 1);
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
            // Same backstop for levels: nothing this attempt renamed may leave
            // it unsolved (Lean: "failed, proof contains metavariables").
            if levels.mentions_unsolved(&proof) {
                if mtrace {
                    eprintln!("simp-match: lemma={} REJECT proof-level", lemma.name);
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

/// Bind the lemma binders the LHS match left undetermined: synthesizing the
/// ones whose type is a class, discharging the ones that are genuine `Prop`
/// side conditions (RC-J) — Lean's `synthesizeArgs`.
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
/// Four outcomes per undetermined slot:
///
/// * **Not statable** (the instantiated domain still has loose BVars, an
///   unassigned meta or an unsolved lemma level — e.g. simp is recursing
///   under a binder): left alone. A template that applies it is refused
///   (`REJECT template-unbound-binder`) and an assembled proof stays
///   `Pi`-typed and is rejected by `proof_matches_rewrite`, so this is
///   fail-closed.
/// * **A class** (`[Decidable q]`, `[Subsingleton α]`, `[Inhabited α]`):
///   filled by typeclass synthesis in the goal's scope when an instance
///   exists; otherwise it falls through to the next two cases.
/// * **Not a `Prop`**: left alone. A missing DATA argument is a malformed
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
/// from the elaborator's instance resolver and from `discharge_premise`, and
/// each is type-checked against its slot before it is inserted. Returning
/// `false` is always safe: it merely means simp reports `NoProgress` for this
/// lemma.
///
/// ENSURES: Returns `true` only when every slot it chose to fill was filled
///   with a proof whose inferred type is def-eq to the corresponding premise.
#[allow(clippy::too_many_arguments)]
fn bind_undetermined_binders(
    state: &ProofState,
    goal: &Goal,
    lemma: &SimpLemma,
    levels: &LemmaLevels,
    metas: &MetaState,
    bvar_to_meta: &mut hashbrown::HashMap<u32, Expr>,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
    budget: &SimpBudget,
) -> bool {
    let binder_types = if is_local_rule(lemma) {
        // A rule minted from a LOCAL hypothesis (`simp [*]`, `simp [h]`)
        // carries that hypothesis' name, which may coincide with an
        // environment constant — and reading THAT constant's binder telescope
        // would describe a completely different lemma. Its telescope is the
        // HYPOTHESIS's own (`lemmas::local_rule_binder_types`): Lean's
        // `synthesizeArgs` makes no difference between a global theorem and
        // `ih : ∀ m, m < n → f m = g m`, whose premise the match leaves open
        // exactly as a global conditional lemma's. They used to be skipped
        // here, so every conditional local rule was refused
        // (`template-unbound-binder`; before that guard, the kernel aborted
        // the declaration on the loose binder) — measured 2026-09-20:
        // `simp only [h, hp]` with `h : ∀ x, p x → f x = g x`, `hp : p 3`
        // made no progress on `f 3 = g 3`, which pinned Lean closes.
        //
        // Fast path first: the template applies every binder of the rule, so
        // "all of its loose indices are bound" is "nothing is open".
        match &lemma.proof_expr {
            Some(template) if !template_binders_bound(template, bvar_to_meta) => {}
            _ => return true,
        }
        let Some(types) = super::lemmas::local_rule_binder_types(state, goal, lemma) else {
            return true;
        };
        types
    } else {
        // Hand-written builtin patterns have no environment declaration to
        // read binders from; they are unconditional by construction, so there
        // is nothing to discharge.
        let Some(info) = state.env.get_const(&lemma.name) else {
            return true;
        };
        // Fast path: an unconditional lemma whose every binder the LHS match
        // already determined needs no work at all, and that is the
        // overwhelming majority of matches. Counting the Pi spine allocates
        // nothing; the lifting walk below only runs when a slot is genuinely
        // open.
        let total = leading_pi_binder_count(&info.type_);
        if total == 0 || (0..total as u32).all(|index| bvar_to_meta.contains_key(&index)) {
            return true;
        }
        // The telescope in this attempt's fresh levels (see `lemma_levels`),
        // so a premise is stated at the levels the match solved.
        collect_binder_types_in_conclusion(&levels.rename(&info.type_))
    };

    for index in (0..binder_types.len()).rev() {
        let key = index as u32;
        if bvar_to_meta.contains_key(&key) {
            continue;
        }

        let domain = substitute_bvars_with_metas(&binder_types[index], bvar_to_meta);
        let domain = metas.instantiate_levels(&metas.instantiate(&domain));
        // A premise still carrying an unsolved fresh level is not statable
        // either: its proof would carry the level metavariable too.
        if domain.has_loose_bvars()
            || contains_unassigned_meta(&domain)
            || levels.mentions_unsolved(&domain)
        {
            if slot_trace(lemma) {
                eprintln!(
                    "simp-match: lemma={} binder#{index} not statable: {domain:?}",
                    lemma.name
                );
            }
            continue;
        }

        // Lean's `synthesizeArgs` (`Rewrite.lean:57-100`): a slot whose type
        // is a CLASS is filled by typeclass synthesis first, whether or not
        // it is a proposition (`[Decidable p]`, `[Subsingleton α]`,
        // `[Nonempty α]`), and a proposition the search cannot answer falls
        // through to the discharger. Clean used to skip every non-`Prop`
        // slot here, so an instance binder the LHS does not determine — the
        // `[Decidable q]` of `Decidable.forall_or_left`, the
        // `[Subsingleton α]` of `eq_iff_true_of_subsingleton` — was never
        // filled, not even from a local instance (measured 2026-09-12:
        // `simp only [lemK]` over a global `Inh1 Nat` instance made no
        // progress where Lean rewrites).
        if let Some(instance) = synthesize_class_slot(state, goal, &domain, budget) {
            bvar_to_meta.insert(key, instance);
            continue;
        }
        if slot_trace(lemma) {
            eprintln!(
                "simp-match: lemma={} binder#{index} no instance for {domain:?}",
                lemma.name
            );
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

/// Whether `CLEAN_SIMP_MATCH_TRACE` selects `lemma` (diagnostic only).
///
/// The variable is read ONCE per process: this runs for every lemma attempt,
/// and a `getenv` per attempt (process-wide lock plus an allocation) was 2.5%
/// of the samples of the 189.5 s `simp_rw` in `Mathlib/Order/Basic.lean`
/// (performance audit 2026-09-24). Nothing sets it after start-up.
fn slot_trace(lemma: &SimpLemma) -> bool {
    static FILTER: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    FILTER
        .get_or_init(|| std::env::var("CLEAN_SIMP_MATCH_TRACE").ok())
        .as_deref()
        .is_some_and(|f| lemma.name.to_string().contains(f))
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

/// What matching solved the builtin patterns' pattern-local
/// [`BUILTIN_PATTERN_LEVEL_PARAM`] to, or `None` when it is still unsolved (a
/// registry pattern never mentions it, so this is `None` for every
/// environment lemma).
fn builtin_pattern_level(metas: &MetaState) -> Option<Level> {
    let param = Name::from_string(BUILTIN_PATTERN_LEVEL_PARAM);
    let solved = metas.instantiate_level(&Level::param(param.clone()));
    let mut params = Vec::new();
    solved.collect_params(&mut params);
    (!params.contains(&param)).then_some(solved)
}

/// Whether `expr` contains a leaked *unassigned* metavariable, represented as an
/// `FVar` whose id carries `MetaState`'s high-bit tag (`MetaState::to_fvar` /
/// `from_fvar`). After `MetaState::instantiate`, an FVar that still decodes to a
/// `MetaId` is a pattern metavariable the unifier never bound — a hallmark of a
/// spurious ι-collapsed match (e.g. `Nat.mul ?n 0` matched against a target that
/// WHNF-reduces to `0` without binding `?n`). Such a term is ill-typed and must
/// not be emitted as (part of) a simp rewrite proof.
pub(super) fn contains_unassigned_meta(expr: &Expr) -> bool {
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
pub(super) fn proof_matches_rewrite(
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
/// ENSURES: Every `Const(name, us)` node with `name` in `unfold_defs` is
///   replaced by the corresponding body INSTANTIATED at `us`.
/// ENSURES: A `Const(name, us)` whose level count disagrees with the stored
///   declaration's parameter count is left folded, not substituted.
/// ENSURES: Non-matching nodes preserve their constructor/metadata while
///   recursively rewriting children.
///
/// The level instantiation is not a refinement — it is what makes the
/// substitution definitional at all. Splicing the raw body of a
/// universe-polymorphic definition leaves that definition's OWN parameter
/// names free in the goal, so the rewritten target is not def-eq to the one it
/// replaced and `replace_target_def_eq` refuses the whole `simp` step. See
/// [`super::types::UnfoldDef`].
fn unfold_named_consts(expr: &Expr, unfold_defs: &HashMap<Name, UnfoldDef>) -> Expr {
    struct UnfoldFolder<'a> {
        unfold_defs: &'a HashMap<Name, UnfoldDef>,
    }

    impl ExprFolder for UnfoldFolder<'_> {
        fn fold_const(&mut self, name: &Name, levels: &LevelVec) -> Expr {
            if let Some(def) = self.unfold_defs.get(name) {
                if def.level_params.len() == levels.len() {
                    return def
                        .value
                        .instantiate_level_params_direct(&def.level_params, levels);
                }
            }
            Expr::const_(name.clone(), levels.clone())
        }
    }

    let mut folder = UnfoldFolder { unfold_defs };
    folder.fold_expr(expr)
}

/// Whether every lemma binder a prebuilt proof template refers to has been
/// bound — by the LHS match, or by `bind_undetermined_binders`.
///
/// A template's loose de Bruijn indices ARE the lemma's binders, counted from
/// the innermost (the indexing of `bvar_to_meta`'s keys), so a loose
/// `BVar(i)` at binder depth `d` is binder `i - d`.
fn template_binders_bound(template: &Expr, bvar_to_meta: &hashbrown::HashMap<u32, Expr>) -> bool {
    fn go(e: &Expr, depth: u32, bound: &hashbrown::HashMap<u32, Expr>) -> bool {
        if e.loose_bvar_range() <= depth {
            return true;
        }
        stack_safe(|| match e.kind() {
            ExprKind::BVar(idx) => bound.contains_key(&(*idx - depth)),
            ExprKind::App(f, a) => go(f, depth, bound) && go(a, depth, bound),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                go(ty, depth, bound) && go(body, depth + 1, bound)
            }
            ExprKind::Let(_, ty, val, body, _) => {
                go(ty, depth, bound) && go(val, depth, bound) && go(body, depth + 1, bound)
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
                go(inner, depth, bound)
            }
            _ => true,
        })
    }
    go(template, 0, bvar_to_meta)
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
