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
) -> Expr {
    // h := name applied to its binder arguments (outermost binder first).
    let mut h = Expr::const_(lemma_name.clone(), vec![]);
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

/// Simplify an expression using simp lemmas.
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
pub(crate) fn simp_expr(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
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
    if !config.unfold_defs.is_empty() {
        let unfolded = unfold_named_consts(&result.expr, &config.unfold_defs);
        if unfolded != result.expr {
            result = SimpResult {
                expr: unfolded,
                proof: None,
            };
        }
    }

    if config.beta {
        let beta_reduced = beta_reduce(&result.expr);
        if beta_reduced != result.expr {
            result = SimpResult {
                expr: beta_reduced,
                proof: None,
            };
        }
    }

    if config.eta {
        let eta_reduced = eta_reduce(&result.expr);
        if eta_reduced != result.expr {
            result = SimpResult {
                expr: eta_reduced,
                proof: None,
            };
        }
    }

    // Try to apply simp lemmas at the top level (produces a real proof term).
    // Guard: skip matches that produce the same expression — this can happen when the
    // unifier WHNF-reduces the pattern (e.g. `Nat.add ?n 0` → `?n`) and the meta
    // absorbs the entire target, yielding an identity rewrite.
    for lemma in lemmas.candidates(state, goal, &result.expr) {
        if let Some((new_expr, proof)) =
            try_apply_simp_lemma_with_proof(state, goal, &result.expr, lemma, lemmas, config)
        {
            if new_expr != result.expr {
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

    // Recurse into subexpressions, building congruence proofs
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
            if let Some(ite_step) = try_simp_ite(state, goal, &result.expr, lemmas, config) {
                return mk_eq_trans(result, ite_step, state, goal);
            }

            let f_result = stack_safe(|| simp_expr(state, goal, f, lemmas, config));
            let arg_result = stack_safe(|| simp_expr(state, goal, arg, lemmas, config));
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
            let body_result = stack_safe(|| simp_expr(state, goal, body, lemmas, config));
            if body_result.expr != **body {
                // Build funext proof when body has a proof term
                let lam_proof = body_result
                    .proof
                    .as_ref()
                    .and_then(|bp| mk_funext(state, goal, ty, body, &body_result.expr, bp));
                let lam_result = SimpResult {
                    expr: Expr::lam(*bi, ty.as_ref().clone(), body_result.expr),
                    proof: lam_proof,
                };
                return mk_eq_trans(result, lam_result, state, goal);
            }
        }
        ExprKind::Pi(bi, ty, body) => {
            let ty_result = stack_safe(|| simp_expr(state, goal, ty, lemmas, config));
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

            let body_result = stack_safe(|| simp_expr(state, goal, body, lemmas, config));
            if body_result.expr != **body {
                // Build forall_congr + propext proof when body has a proof term
                // and the Pi type is Prop-valued. Falls back to proof: None
                // (definitional) for non-Prop Pi or when body proof is absent.
                let pi_proof = body_result
                    .proof
                    .as_ref()
                    .and_then(|bp| mk_forall_congr(state, goal, ty, body, &body_result.expr, bp));
                let pi_result = SimpResult {
                    expr: Expr::pi(*bi, ty.as_ref().clone(), body_result.expr),
                    proof: pi_proof,
                };
                return mk_eq_trans(result, pi_result, state, goal);
            }
        }
        ExprKind::Let(name, ty, val, body, non_dep) => {
            let val_result = stack_safe(|| simp_expr(state, goal, val, lemmas, config));
            let body_result = stack_safe(|| simp_expr(state, goal, body, lemmas, config));
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
            let inner_result = stack_safe(|| simp_expr(state, goal, inner, lemmas, config));
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
            let inner_result = stack_safe(|| simp_expr(state, goal, inner, lemmas, config));
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
) -> Option<SimpResult> {
    let (u, alpha, c, inst, t, e) = peel_ite(expr)?;

    // Simplify ONLY the condition. A genuine rewrite to True/False always
    // carries a proof `h₁ : c = c'`; if the condition is already syntactically
    // `True`/`False` the top-level `ite_true`/`ite_false` lemma handles it, so
    // requiring `Some(h1)` here loses no coverage and avoids fabricating a proof
    // for a non-change.
    let cond_result = stack_safe(|| simp_expr(state, goal, &c, lemmas, config));
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

/// If `e` is exactly the Nat-numeral projection form
/// `@OfNat.ofNat Nat (Lit k) (instOfNatNat (Lit k))`, return the raw literal
/// `Lit(Nat k)`; otherwise `None`.
///
/// SOUNDNESS: `instOfNatNat k` is the structure literal storing `k`, so the
/// projection ι/δ-reduces to `k` — the two spellings are definitionally equal
/// (the kernel's `add_decl` re-check enforces exactly this equivalence).
fn as_nat_ofnat_literal(e: &Expr) -> Option<Expr> {
    static OFNAT_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("OfNat.ofNat"));
    static NAT_NAME: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat"));
    static INST_OFNAT_NAT_NAME: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("instOfNatNat"));

    let head = e.get_app_fn();
    let ExprKind::Const(head_name, _) = head.kind() else {
        return None;
    };
    if *head_name != *OFNAT_NAME {
        return None;
    }
    let args = e.get_app_args();
    let [ty, lit, inst] = args.as_slice() else {
        return None;
    };
    if !matches!(ty.kind(), ExprKind::Const(n, _) if *n == *NAT_NAME) {
        return None;
    }
    if !matches!(lit.kind(), ExprKind::Lit(clean_kernel::Literal::Nat(_))) {
        return None;
    }
    let inst_head = inst.get_app_fn();
    if !matches!(inst_head.kind(), ExprKind::Const(n, _) if *n == *INST_OFNAT_NAT_NAME) {
        return None;
    }
    Some((*lit).clone())
}

/// Rewrite every `@OfNat.ofNat Nat k (instOfNatNat k)` subterm of `e` to the
/// raw `Lit(Nat k)`. Returns `None` when nothing collapsed (the common case),
/// so callers keep the original expression without an extra clone.
fn collapse_nat_ofnat_literals(e: &Expr) -> Option<Expr> {
    struct OfNatCollapser {
        changed: bool,
    }
    impl ExprFolder for OfNatCollapser {
        fn fold_app(&mut self, f: &Expr, arg: &Expr) -> Expr {
            let rebuilt = Expr::app(self.fold_expr(f), self.fold_expr(arg));
            if let Some(lit) = as_nat_ofnat_literal(&rebuilt) {
                self.changed = true;
                lit
            } else {
                rebuilt
            }
        }
    }
    let mut collapser = OfNatCollapser { changed: false };
    let folded = collapser.fold_expr(e);
    collapser.changed.then_some(folded)
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
/// REQUIRES: `lemma.name` and its BVar layout align with `lemma.lhs`/`lemma.rhs`
/// ENSURES: On Some, returns the instantiated RHS plus a proof term built from `lemma.name`
/// ENSURES: On Some, every side condition of `lemma` was discharged with a
///   type-checked proof term; no argument slot is silently skipped
pub(crate) fn try_apply_simp_lemma_with_proof(
    state: &ProofState,
    goal: &Goal,
    expr: &Expr,
    lemma: &SimpLemma,
    lemmas: &SimpLemmaSet,
    config: &SimpConfig,
) -> Option<(Expr, Expr)> {
    let mut metas = MetaState::new();
    // Pattern metas are scoped to the GOAL's locals (elab locals + goal ctx):
    // a pattern variable must be allowed to bind a goal subterm mentioning a
    // goal FVar (`?n := a` for `a * 1`), while binder-opened temporaries stay
    // rejected by the unifier's scope check (B102).
    let pattern_scope = state.meta_scope_for_context(&goal.local_ctx);
    let (pattern_with_metas, mut bvar_to_meta) =
        convert_bvars_to_metas(&lemma.lhs, &mut metas, &pattern_scope);

    // Match target. When `expr` is a heterogeneous-operator typeclass projection
    // (`@HMul.hMul Nat … n 0`), bare-head builtin/library lemmas (`Nat.mul ?n 0`)
    // cannot unify head-to-head against the projection spine: the first-order
    // unifier mis-binds `?n` to a partial `HMul.hMul …` application, assembling a
    // malformed proof that only the kernel `add_decl` rejects (after which simp
    // has already lost the chance to fall through to another candidate). Peel
    // EXACTLY the projection layer — exposing `Nat.mul n 0` WITHOUT ι-reducing
    // the operands — and unify the pattern against THAT. The unifier then binds
    // `?n ↦ n` correctly. Soundness is unchanged: the peeled form is def-eq to
    // `expr`, so the existing `lhs_inst ≡ expr` guard and `proof_matches_rewrite`
    // (both still stated over the ORIGINAL `expr`) validate the bridge, and the
    // kernel re-check is the final backstop. `reduce_op_projection_head` returns
    // `None` for non-projection heads, so the common case is untouched.
    let peeled = reduce_op_projection_head(state, goal, expr);
    let match_target = peeled.as_ref().unwrap_or(expr);

    // Collapse `@OfNat.ofNat Nat k (instOfNatNat k)` operand leaves to the raw
    // `Lit(Nat k)` before matching (B102). The surface elaborator spells a Nat
    // numeral as the OfNat projection form; builtin literal-operand patterns
    // (`Nat.add ?n 0`, `Nat.mul ?n 1`) carry the bare `Nat.zero`/`Lit 1` leaf,
    // and the reducible-transparency unifier cannot bridge the two (the OfNat
    // instance does not unfold at `withReducible`). The collapse is exactly
    // the instance's own ι/δ-reduction (`instOfNatNat k` stores `k`), so it is
    // def-eq; the `lhs_inst ≡ expr` guard below is still stated over the
    // ORIGINAL `expr` and the kernel re-check backstops any mis-assembly.
    let collapsed = collapse_nat_ofnat_literals(match_target);
    let match_target = collapsed.as_ref().unwrap_or(match_target);

    // Normalize the LEMMA PATTERN the same way, so the two sides meet. Without
    // this the normalization above is ONE-SIDED: a lemma whose own statement is
    // written in notation keeps its `HDiv.hDiv` head while the goal subterm has
    // just been reduced to `Nat.div`, and head-keyed unification fails on the
    // head alone — even when pattern and goal subterm are otherwise byte-identical.
    // See [`peel_pattern_to_target_head`].
    let peeled_pattern =
        peel_pattern_to_target_head(state, goal, &pattern_with_metas, match_target);
    let match_pattern = peeled_pattern.as_ref().unwrap_or(&pattern_with_metas);

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
            ) {
                return None;
            }

            // The RHS is instantiated only AFTER discharge: a dependent
            // conclusion may mention the hypothesis binder, and `bvar_to_meta`
            // now carries its proof.
            let rhs_with_metas = substitute_bvars_with_metas(&lemma.rhs, &bvar_to_meta);
            let result = inst(&rhs_with_metas);
            if contains_unassigned_meta(&result) {
                return None;
            }

            let proof = if let Some(proof_expr) = &lemma.proof_expr {
                let proof_with_metas = substitute_bvars_with_metas(proof_expr, &bvar_to_meta);
                let proof = metas.instantiate(&proof_with_metas);
                if !proof_matches_rewrite(state, goal, &proof, expr, &result) {
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
                let mut proof = Expr::const_(lemma.name.clone(), lemma_levels);
                let max_bvar = bvar_to_meta.keys().copied().max().map_or(0, |m| m + 1);
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
                return None;
            }

            Some((result, proof))
        }
        UnifyResult::Failure(_) | UnifyResult::Stuck => None,
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

        let Some(proof) = super::discharge::discharge_premise(state, goal, &domain, lemmas, config)
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
