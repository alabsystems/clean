// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rewrite tactics for equality goals and hypotheses.
//!
//! Contains `rewrite`, `rewrite_ltr`, `rewrite_rtl`, and `rewrite_at` —
//! tactics that replace subexpressions using equality proofs via `Eq.subst`.

// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, LocalContext, Name};

use super::super::op_projection::{is_hetero_op_projection, reduce_op_projection_head};
use super::super::{Goal, ProofState, TacticError, TacticResult};
use super::expr_utils::{
    abstract_over, contains_expr, find_defeq_subterm_with, match_equality, match_iff, replace_expr,
    rewrite_candidate_summaries,
};
use crate::unify::{MetaState, Unifier, UnifyResult};

/// Direction of a rewrite operation.
///
/// `Forward` rewrites left-to-right (replacing LHS with RHS).
/// `Backward` rewrites right-to-left (replacing RHS with LHS), corresponding
/// to Lean 4's `rw [<-h]` syntax.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)] // 2026-08-10: no caller; staged prototype kept per keep-and-annotate doctrine.
pub(crate) enum RewriteDirection {
    /// Rewrite left-to-right: replace occurrences of LHS with RHS.
    Forward,
    /// Rewrite right-to-left: replace occurrences of RHS with LHS.
    Backward,
}

impl RewriteDirection {
    /// Returns `true` for backward (right-to-left) rewrites.
    #[allow(dead_code)] // 2026-08-10: no caller; staged prototype kept per keep-and-annotate doctrine.
    pub(crate) fn is_reverse(self) -> bool {
        matches!(self, RewriteDirection::Backward)
    }
}

/// A structured representation of a rewrite rule, pairing a direction with
/// the equality proof and its decomposed sides.
///
/// Constructed from a hypothesis name in the local context via
/// [`RewriteRule::from_hypothesis`].
#[derive(Debug, Clone)]
#[allow(dead_code)] // 2026-08-10: no caller; staged prototype kept per keep-and-annotate doctrine.
pub(crate) struct RewriteRule {
    /// Direction of the rewrite.
    pub(crate) direction: RewriteDirection,
    /// The equality proof expression (typically an FVar reference).
    #[allow(dead_code)]
    // 2026-08-10: no caller; staged prototype kept per keep-and-annotate doctrine.
    pub(crate) proof: Expr,
    /// The type of the equality (the `alpha` in `@Eq alpha a b`).
    pub(crate) eq_type: Expr,
    /// Left-hand side of the equality.
    pub(crate) lhs: Expr,
    /// Right-hand side of the equality.
    pub(crate) rhs: Expr,
    /// Universe levels on the `Eq` constant.
    pub(crate) eq_levels: Vec<Level>,
}

impl RewriteRule {
    /// Build a `RewriteRule` from a named hypothesis in the proof state.
    ///
    /// # Errors
    /// - `HypothesisNotFound` if `hyp_name` is not in the local context.
    /// - `GoalMismatch` if the hypothesis type is not an equality.
    #[allow(dead_code)] // 2026-08-10: no caller; staged prototype kept per keep-and-annotate doctrine.
    pub(crate) fn from_hypothesis(
        state: &ProofState,
        goal: &Goal,
        hyp_name: &str,
        direction: RewriteDirection,
    ) -> Result<Self, TacticError> {
        let hyp_decl = goal
            .local_ctx
            .iter()
            .find(|d| d.name == hyp_name)
            .ok_or_else(|| TacticError::HypothesisNotFound(hyp_name.to_string()))?;

        let hyp_ty = state.whnf(goal, &hyp_decl.ty);
        let (eq_type, lhs, rhs, eq_levels) = match_equality(&hyp_ty)?;

        Ok(RewriteRule {
            direction,
            proof: Expr::fvar(hyp_decl.fvar),
            eq_type,
            lhs,
            rhs,
            eq_levels,
        })
    }

    /// The expression to search for in the goal (the "from" side).
    ///
    /// `from_*` here names the LHS/RHS direction of the rewrite, not a
    /// type conversion — `&self` is correct.
    #[allow(clippy::wrong_self_convention)]
    #[allow(dead_code)] // 2026-08-10: no caller; staged prototype kept per keep-and-annotate doctrine.
    pub(crate) fn from_expr(&self) -> &Expr {
        match self.direction {
            RewriteDirection::Forward => &self.lhs,
            RewriteDirection::Backward => &self.rhs,
        }
    }

    /// The expression to replace with (the "to" side).
    #[allow(dead_code)] // 2026-08-10: no caller; staged prototype kept per keep-and-annotate doctrine.
    pub(crate) fn to_expr(&self) -> &Expr {
        match self.direction {
            RewriteDirection::Forward => &self.rhs,
            RewriteDirection::Backward => &self.lhs,
        }
    }
}

/// Rewrite the goal using an equality hypothesis.
///
/// Given a hypothesis `h : a = b` and a goal containing `a`,
/// replaces occurrences of `a` with `b` and uses `Eq.subst` to justify the transformation.
///
/// # Arguments
/// * `state` - The proof state
/// * `hyp_name` - Name of the equality hypothesis to use
/// * `reverse` - If true, rewrite `b` to `a` instead of `a` to `b`
///
/// # Example
/// ```text
/// Given: h : x = y, goal: P x
/// After rewrite(h): goal becomes P y
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: `hyp_name` refers to a hypothesis of type `a = b` in the local context
/// ENSURES: On Ok, the goal target has `a` (or `b` if `reverse`) replaced with `b` (or `a`)
/// ENSURES: On Ok, the proof uses `Eq.subst` to justify the rewrite
/// ENSURES: On Err(HypothesisNotFound), `hyp_name` is not in the local context
pub fn rewrite(state: &mut ProofState, hyp_name: &str, reverse: bool) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Resolution order matches Lean 4: a local hypothesis named `hyp_name`
    // shadows an environment constant of the same name. Only when no such
    // hypothesis exists do we fall back to the environment (`rw [Nat.add_comm]`).
    let eqn = match goal.local_ctx.iter().find(|d| d.name == hyp_name) {
        Some(hyp_decl) => {
            // Check that the hypothesis is an equality. If it is an `Iff` instead,
            // adapt it to an `Eq` via `propext` and feed the same machinery.
            let hyp_ty = state.whnf(&goal, &hyp_decl.ty);
            let proof = Expr::fvar(hyp_decl.fvar);
            if matches!(hyp_ty.kind(), ExprKind::Pi(..)) {
                // A universally-quantified local hypothesis `h : ∀ x, lhs = rhs`
                // (a Pi/∀ *over* an equation) must have its leading binders
                // peeled — instantiated with fresh metavariables that the
                // from-side match against the goal solves — before
                // `match_equality` can see the `Eq`/`Iff` head. Without peeling,
                // `match_equality` sees the `Pi` head and the rewrite fails.
                // This mirrors the environment-constant path exactly; the
                // resulting `Eq.subst` proof is still kernel-rechecked in
                // `finish_rewrite`. (Local hypotheses carry no level params, so
                // no universe instantiation is needed — pass the fvar directly.)
                let target = state.metas.instantiate(&goal.target);
                peel_and_resolve_rewrite_equation(
                    state,
                    &goal,
                    hyp_name,
                    reverse,
                    &target,
                    Vec::new(),
                    proof,
                    hyp_ty,
                )?
            } else {
                match match_equality(&hyp_ty) {
                    Ok((eq_type, lhs, rhs, eq_levels)) => RewriteEquation {
                        eq_type,
                        lhs,
                        rhs,
                        eq_levels,
                        proof,
                    },
                    Err(eq_err) => iff_rewrite_equation(&hyp_ty, proof).ok_or(eq_err)?,
                }
            }
        }
        None => {
            let target = state.metas.instantiate(&goal.target);
            resolve_env_rewrite_equation(state, &goal, hyp_name, reverse, &target, Vec::new())?
        }
    };

    finish_rewrite(state, &goal, hyp_name, reverse, eqn)
}

/// A fully-resolved rewrite equation: `proof : @Eq eq_type lhs rhs` with
/// `lhs`/`rhs` concrete (no loose metavariables after env instantiation).
struct RewriteEquation {
    eq_type: Expr,
    lhs: Expr,
    rhs: Expr,
    eq_levels: Vec<Level>,
    proof: Expr,
}

/// Adapt an `Iff`-headed rewrite source into the `Eq`-shaped [`RewriteEquation`]
/// that the rest of the rewrite machinery consumes.
///
/// Given `iff_ty = @Iff p q` (with `p q : Prop`) and a proof `iff_proof : p ↔ q`,
/// this synthesizes the foundational `propext` axiom application
///
/// ```text
/// @propext p q iff_proof : @Eq.{succ zero} Prop p q
/// ```
///
/// and returns the equation `Eq Prop p q` whose proof is exactly that term.
/// `propext` has no level parameters (see `clean-kernel` `init_propext`), and the
/// resulting `Eq` lives at universe level `succ zero` because `α = Prop : Sort 1`.
///
/// REQUIRES: `iff_ty` is `@Iff p q` (caller checks via [`match_iff`]).
/// ENSURES: On `Some`, the returned `proof` type-checks to `@Eq Prop p q` and feeds
///   the identical `Eq.subst`/`Eq.symm` path used for genuine equalities, so an
///   over-eager or wrong-direction `Iff` rewrite still fails closed in the kernel.
fn iff_rewrite_equation(iff_ty: &Expr, iff_proof: Expr) -> Option<RewriteEquation> {
    let (p, q) = match_iff(iff_ty)?;
    // propext : {a b : Prop} → (a ↔ b) → a = b   (no level params).
    // Application order is `propext p q iff_proof` (implicits a, b made explicit).
    let propext = Expr::const_(Name::from_string("propext"), vec![]);
    let proof = Expr::app(
        Expr::app(Expr::app(propext, p.clone()), q.clone()),
        iff_proof,
    );
    Some(RewriteEquation {
        eq_type: Expr::prop(),
        lhs: p,
        rhs: q,
        eq_levels: vec![Level::succ(Level::zero())],
        proof,
    })
}

/// Resolve a rewrite rule from an *environment* constant when no local
/// hypothesis of the same name exists.
///
/// Mirrors how `simp` sources lemmas via `env.get_const`: the constant's type
/// is taken (with fresh universe params substituted for its level params), its
/// leading `∀`/Pi binders are instantiated with fresh metavariables (so a
/// univ-polymorphic / quantified equation such as
/// `Nat.add_comm : ∀ n m, n + m = m + n` becomes a matchable pattern), and the
/// resulting `@Eq α lhs rhs` body is matched against a subterm of `haystack`
/// to solve those metavariables. The proof term is `c.{u…} arg₀ … argₖ` with
/// the instantiated arguments, so it type-checks in the kernel via `close_goal`
/// (at-goal) or `replace_local_decl_with_cast` (at-hypothesis).
///
/// The binder-peeling, body matching, and from-side unification are shared with
/// the *local-hypothesis* path via [`peel_and_resolve_rewrite_equation`]; this
/// wrapper only adds the environment-constant lookup and universe instantiation.
///
/// `haystack` is the expression the `from` side is unified against — the goal
/// target for `rw [lemma]`, or a hypothesis type for `rw [lemma] at h`. The
/// returned [`RewriteEquation`] is identical in both cases; only the metavariable
/// solving differs by which subterms are available to match.
///
/// `focus_path` is attached to a `RewriteNoMatch` error so the diagnostic can
/// say whether the no-match was at the goal (empty) or a named hypothesis.
///
/// # Errors
/// - `HypothesisNotFound` if `name` is neither a local hypothesis nor a constant.
/// - `GoalMismatch` if the constant's type is not an equality (under binders).
/// - `RewriteNoMatch` if no subterm of `haystack` unifies with the `from` side.
fn resolve_env_rewrite_equation(
    state: &mut ProofState,
    goal: &Goal,
    name: &str,
    reverse: bool,
    haystack: &Expr,
    focus_path: Vec<String>,
) -> Result<RewriteEquation, TacticError> {
    let const_name = Name::from_string(name);
    let info = state
        .env
        .get_const(&const_name)
        .ok_or_else(|| TacticError::HypothesisNotFound(name.to_string()))?;
    let level_params = info.level_params.clone();
    let const_type = info.type_.clone();

    // Fresh universe parameters for each declared level param, exactly as
    // `mk_const` does — referencing a univ-polymorphic constant with the wrong
    // arity yields kernel-invalid terms (#1828).
    let level_args: Vec<Level> = (0..level_params.len())
        .map(|_| state.fresh_universe_param())
        .collect();
    let const_type = const_type.instantiate_level_params_direct(&level_params, &level_args);
    let proof_base = Expr::const_(const_name, level_args);

    peel_and_resolve_rewrite_equation(
        state, goal, name, reverse, haystack, focus_path, proof_base, const_type,
    )
}

/// Resolve an *environment-constant* rewrite rule for the conv focus-rewrite
/// path (`conv => …; rw [envLemma]`).
///
/// The conv path needs the identical resolution `rw [envLemma]` performs — look
/// up the constant, instantiate its universe params, peel its leading `∀`
/// binders to fresh metavariables, and unify the `from` side (LHS forward / RHS
/// backward) against `haystack` (the conv focus) to solve them — but it then
/// lifts the rewrite through conv's own congruence proof rather than
/// `finish_rewrite`. So it consumes the resolved *parts* rather than the private
/// [`RewriteEquation`]: `(eq_type, lhs, rhs, eq_levels, proof)`, where `proof`
/// is `@const meta… : @Eq eq_type lhs rhs` in the equation's *original*
/// orientation (the caller applies `Eq.symm` for a reverse rewrite). Every part
/// is fully resolved (metavars + levels), so the caller's structural focus
/// search and the kernel re-check downstream see concrete terms.
///
/// Visibility mirrors its `pub use`d block-mates (`rewrite`, `rewrite_with_proof`):
/// `pub` here, capped to crate reach by the enclosing `pub(crate) mod equality`.
#[allow(clippy::type_complexity)]
pub fn resolve_env_rewrite_parts(
    state: &mut ProofState,
    goal: &Goal,
    name: &str,
    reverse: bool,
    haystack: &Expr,
) -> Result<(Expr, Expr, Expr, Vec<Level>, Expr), TacticError> {
    let eqn = resolve_env_rewrite_equation(state, goal, name, reverse, haystack, Vec::new())?;
    Ok((eqn.eq_type, eqn.lhs, eqn.rhs, eqn.eq_levels, eqn.proof))
}

/// Peel the leading `∀`/Pi binders off a rewrite source's type and resolve it to
/// a concrete [`RewriteEquation`].
///
/// Shared by the environment-constant path ([`resolve_env_rewrite_equation`],
/// where `proof_base = c.{u…}` and `base_type` is the level-instantiated const
/// type) and the **local-hypothesis** path (`rw [h]` / `rw [h] at k` where
/// `h : ∀ x, lhs = rhs`, `proof_base` = `h`'s fvar, `base_type` = the hypothesis
/// type). In both cases the leading binders are instantiated with fresh
/// metavariables so a quantified equation becomes a matchable pattern; the
/// `from` side is unified against a subterm of `haystack` (goal target or
/// hypothesis type) to solve them, and the proof term becomes
/// `proof_base meta₀ meta₁ …` (Lean theorem-application order). `resolve_all`
/// then makes the equation sides syntactically concrete for `finish_rewrite`'s
/// structural search.
///
/// SOUNDNESS (elaboration/tactic-completeness only): peeling a ∀-quantified
/// equational source with fresh metavariables — solved by matching against the
/// rewrite target — is exactly how Lean's `rw [h]` handles `h : ∀ x, lhs = rhs`.
/// It changes only *which* proof term is built (`proof_base meta…`); that term's
/// `Eq.subst`/`Eq.mpr` cast is still re-checked by the kernel downstream
/// (`close_goal` / `replace_local_decl_with_cast`). No kernel/TCB code is touched.
///
/// # Errors
/// - `GoalMismatch` if the body under the binders is neither an `Eq` nor an `Iff`.
/// - `RewriteNoMatch` if no subterm of `haystack` unifies with the `from` side.
#[allow(clippy::too_many_arguments)]
fn peel_and_resolve_rewrite_equation(
    state: &mut ProofState,
    goal: &Goal,
    name: &str,
    reverse: bool,
    haystack: &Expr,
    focus_path: Vec<String>,
    proof_base: Expr,
    base_type: Expr,
) -> Result<RewriteEquation, TacticError> {
    // Peel leading Pi binders, instantiating each with a fresh metavariable.
    // `meta_args` keeps the binder order (outermost first) so the proof term can
    // re-apply them as `proof_base meta₀ meta₁ …` (Lean theorem-application order).
    let mut current = state.whnf(goal, &base_type);
    let mut meta_args: Vec<Expr> = Vec::new();
    while let ExprKind::Pi(_bi, domain, codomain) = current.kind() {
        let domain_inst = state.metas.instantiate(domain);
        let meta_id = state.fresh_meta(domain_inst);
        let meta = Expr::fvar(MetaState::to_fvar(meta_id));
        current = codomain.instantiate(&meta);
        meta_args.push(meta);
    }

    // The body (under its leading binders) must be an `@Eq α a b`, or an
    // `@Iff p q` which we adapt to `Eq Prop p q` via `propext`. A non-equation
    // source — e.g. `rw [Nat.succ]` (a function) or a local `h : ∀ x, P x` —
    // fails cleanly here. `is_iff` records that the proof term must be wrapped
    // `propext lhs rhs (proof_base meta…)` further down.
    let mut is_iff = false;
    let (eq_type, lhs, rhs, eq_levels) = match match_equality(&current) {
        Ok(parts) => parts,
        Err(_) => match match_iff(&current) {
            Some((p, q)) => {
                is_iff = true;
                (Expr::prop(), p, q, vec![Level::succ(Level::zero())])
            }
            None => {
                return Err(TacticError::GoalMismatch(format!(
                    "rewrite rule '{name}' is not an equation: its type is not of the form \
                     (∀ …, a = b) or (∀ …, p ↔ q)"
                )));
            }
        },
    };

    // The side of the equation we search for (LHS for forward, RHS for
    // backward). It may still contain unassigned metavariables; we unify it
    // against a subterm of `haystack` (goal target or hypothesis type) to solve
    // them.
    let from_pattern = if reverse { rhs.clone() } else { lhs.clone() };
    let haystack = state.metas.instantiate(haystack);
    if !unify_pattern_with_subterm(state, goal, &from_pattern, &haystack) {
        let shown = resolve_all(state, &from_pattern);
        return Err(TacticError::RewriteNoMatch {
            tactic: "rewrite".to_owned(),
            rule: name.to_owned(),
            direction: if reverse { "backward" } else { "forward" }.to_owned(),
            searched_for: shown.to_string(),
            focus: haystack.to_string(),
            focus_path,
            candidates: rewrite_candidate_summaries(&haystack, &shown, 5),
        });
    }

    // Build the proof `proof_base meta₀ meta₁ …`, then fully resolve so the
    // now-solved value metavariables and universe-level params become concrete.
    let mut proof = proof_base;
    for arg in &meta_args {
        proof = Expr::app(proof, arg.clone());
    }

    // For an `Iff` source, the constructed term proves `p ↔ q`; lift it to the
    // `Eq Prop p q` the rewrite machinery expects: `@propext p q (proof_base …)`.
    if is_iff {
        let propext = Expr::const_(Name::from_string("propext"), vec![]);
        proof = Expr::app(
            Expr::app(Expr::app(propext, lhs.clone()), rhs.clone()),
            proof,
        );
    }

    // `eq_levels` are the `Eq` constant's universe levels; resolve any that were
    // solved during matching so the constructed `Eq.subst`/`Eq.symm` terms agree
    // with the (concrete-level) goal.
    let eq_levels = eq_levels
        .iter()
        .map(|l| state.metas.instantiate_level(l))
        .collect();

    Ok(RewriteEquation {
        eq_type: resolve_all(state, &eq_type),
        lhs: resolve_all(state, &lhs),
        rhs: resolve_all(state, &rhs),
        eq_levels,
        proof: resolve_all(state, &proof),
    })
}

/// Resolve both expression metavariables and universe-level constraints in
/// `expr`. Env-sourced rewrite rules introduce fresh universe params that the
/// matcher solves via the level-constraint table; plain `metas.instantiate`
/// only substitutes expression metavariables, so the levels must be canonicalized
/// separately for the resulting term to be syntactically concrete.
fn resolve_all(state: &ProofState, expr: &Expr) -> Expr {
    let inst = state.metas.instantiate(expr);
    state.metas.instantiate_levels(&inst)
}

/// Find the first subterm of `haystack` that unifies with `pattern` (a side of
/// an env equation, possibly containing metavariables), assigning the
/// metavariables in `state.metas` on success. Pre-order traversal.
///
/// Each attempt runs inside a metavariable scope (`push_scope`/`pop_scope`) so
/// that a *failed* unification leaves no partial bindings behind — without this,
/// a failed match at the root could assign a meta to a wrong subterm and poison
/// the later successful match (mirrors simp's fresh-`MetaState`-per-attempt).
/// On the first success the scope is committed and `true` is returned.
fn unify_pattern_with_subterm(
    state: &mut ProofState,
    goal: &Goal,
    pattern: &Expr,
    haystack: &Expr,
) -> bool {
    let ctx = state.build_local_ctx(goal);

    // Keyed (head-symbol) match first, mirroring Lean's `rw`, which selects a
    // rewrite target by its head constant *without* whnf-reducing the goal.
    // `Unifier::unify` reduces both sides to WHNF before structural comparison,
    // so a use of a *reducible* defined constant — e.g. `f n` where the imported
    // WF-defined `f` iota-reduces on a constructor-headed `Acc` proof — is
    // reduced away before the pattern `f ?x` can bind, yielding a spurious
    // `RewriteNoMatch`. The local-hypothesis rewrite path already matches
    // syntactically (`contains_expr` / `replace_expr`); this keeps the
    // environment-constant path consistent so `rw [f.eq_def]` rewrites a *use*
    // of an imported WF-defined function. Argument-level unification still uses
    // the full (WHNF-capable) unifier, so genuinely def-eq arguments match.
    if keyed_head_unify(state, goal, &ctx, pattern, haystack) {
        return true;
    }

    // Full-unifier fallback — but ONLY at a node whose head can plausibly match
    // the pattern's head. When the pattern is a rigid-const application
    // (`Nat.add ?a Nat.zero`) and THIS node's head is a *different* rigid const
    // (`@Eq …`, `@HAdd.hAdd …`, an fvar `n`, …), running the full unifier here
    // is not just useless, it is actively harmful: the unifier WHNFs the
    // pattern, and `Nat.add ?a Nat.zero` ι-reduces (base case on its 2nd arg) to
    // the bare metavar `?a`, which then binds to whatever this node is — a
    // spurious success that captures `?a` against the wrong subterm and stops
    // the search before it reaches the real `HAdd.hAdd`-headed occurrence.
    // `keyed_head_unify` (above) already handled genuine head matches, including
    // the typeclass-projection bridge, so here we only run the full unifier when
    // the heads are not a rigid-const mismatch, and otherwise recurse
    // structurally into the children to find the matchable node.
    if !rigid_const_head_mismatch(pattern, haystack) {
        state.metas.push_scope();
        let unified = {
            let (metas, env) = state.metas_and_env();
            // `unify_no_initial_whnf` — NOT `unify`: the eager entry WHNF would
            // collapse `Nat.add ?a Nat.zero → ?a` even when the heads agree on a
            // sibling shape; skipping it keeps the pattern an App so arg-level
            // unification proceeds normally. `unify_core` still WHNFs internally
            // where discriminants disagree, so genuine def-eq args still match.
            matches!(
                Unifier::with_env(metas, env, ctx.clone()).unify_no_initial_whnf(pattern, haystack),
                UnifyResult::Success
            )
        };
        if unified {
            state.metas.commit();
            return true;
        }
        state.metas.pop_scope();
    }
    match haystack.kind() {
        ExprKind::App(f, a) => {
            unify_pattern_with_subterm(state, goal, pattern, f)
                || unify_pattern_with_subterm(state, goal, pattern, a)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            unify_pattern_with_subterm(state, goal, pattern, ty)
                || unify_pattern_with_subterm(state, goal, pattern, body)
        }
        ExprKind::Let(_, ty, val, body, _) => {
            unify_pattern_with_subterm(state, goal, pattern, ty)
                || unify_pattern_with_subterm(state, goal, pattern, val)
                || unify_pattern_with_subterm(state, goal, pattern, body)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) | ExprKind::Squash(inner) => {
            unify_pattern_with_subterm(state, goal, pattern, inner)
        }
        _ => false,
    }
}

/// Whether `pattern` and `haystack` are applications whose ultimate spine heads
/// are both *rigid constants with different names*. Used by
/// [`unify_pattern_with_subterm`] to skip the harmful full-unifier fallback at a
/// node that cannot match the pattern's head (and where WHNF-ing the pattern
/// would spuriously collapse it onto this node). `keyed_head_unify` — including
/// the typeclass-projection bridge — has already had its chance before this is
/// consulted, so a remaining const-vs-const head mismatch means "recurse
/// structurally", never "force a unify here".
fn rigid_const_head_mismatch(pattern: &Expr, haystack: &Expr) -> bool {
    let (ExprKind::Const(pat_name, _), ExprKind::Const(hay_name, _)) =
        (pattern.get_app_fn().kind(), haystack.get_app_fn().kind())
    else {
        return false;
    };
    pat_name != hay_name
}

/// Keyed head-symbol match between a rewrite `pattern` and a goal subterm,
/// without WHNF-reducing the subterm spine.
///
/// Both `pattern` and `haystack` are decomposed into a function head plus an
/// argument spine. The match fires only when both heads are the *same* constant
/// (same `Name`) applied to the same number of arguments; then the head universe
/// levels and each argument are unified through the full unifier (which may WHNF
/// individual arguments — that is correct, as arguments can be genuinely def-eq).
/// Crucially the `f`-headed *spine* is never reduced, so a reducible defined
/// constant (e.g. an imported WF-defined function that iota-reduces on a concrete
/// argument) is still matched at its `f`-headed node instead of being reduced
/// away first.
///
/// Runs inside a metavariable scope so a partial failure leaves no bindings
/// behind, exactly like the WHNF path in [`unify_pattern_with_subterm`].
///
/// Returns `true` (and commits the bindings) only on a complete head+args match;
/// otherwise it restores the scope and returns `false`, leaving the caller to
/// fall back to the WHNF unifier and structural recursion.
fn keyed_head_unify(
    state: &mut ProofState,
    goal: &Goal,
    ctx: &LocalContext,
    pattern: &Expr,
    haystack: &Expr,
) -> bool {
    let pat_fn = pattern.get_app_fn();
    let hay_fn = haystack.get_app_fn();
    let (ExprKind::Const(pat_name, pat_levels), ExprKind::Const(hay_name, hay_levels)) =
        (pat_fn.kind(), hay_fn.kind())
    else {
        return false;
    };
    if pat_name != hay_name || pat_levels.len() != hay_levels.len() {
        // Heads disagree syntactically. The one case `rw` must still recover is
        // a Nat.*/op-headed *lemma* matched against a typeclass-projection-headed
        // *goal* subterm: pattern head `Nat.add` vs haystack head `HAdd.hAdd`
        // (the goal's `n + 0` desugars to `@HAdd.hAdd … (HAdd.mk … Nat.add) n 0`).
        // Reduce exactly ONE typeclass-projection layer of the haystack head so
        // its head becomes the underlying op const (`Nat.add`), then re-key. We
        // deliberately do NOT whnf the whole subterm — the kernel's full-delta
        // whnf over-reduces `Nat.add n 0` past the matchable `Nat.add`-headed
        // form all the way to `n`, which would defeat the syntactic
        // `replace_expr` in `finish_rewrite`. See `reduce_op_projection_head`.
        // Symmetric projection bridge: reduce ONE projection layer on whichever
        // side IS the hetero-op projection, then re-key once. We only retry when
        // the reduced head const now equals the other side's const head, which
        // bounds recursion (one reduction per side, and the next call's heads
        // agree syntactically so it takes the matched path, never this arm).
        if is_hetero_op_projection(hay_name) {
            // Goal/haystack-side projection (`@HAdd.hAdd … Nat.add n 0` vs a
            // `Nat.add`-headed pattern). Reduce the haystack and re-key.
            if let ExprKind::Const(pat_name_c, _) = pat_fn.kind() {
                if let Some(reduced) = reduce_op_projection_head(state, goal, haystack) {
                    if let ExprKind::Const(red_name, _) = reduced.get_app_fn().kind() {
                        if red_name == pat_name_c {
                            return keyed_head_unify(state, goal, ctx, pattern, &reduced);
                        }
                    }
                }
            }
        } else if is_hetero_op_projection(pat_name) {
            // Pattern-side projection (an `HAdd`-headed lemma/hyp LHS vs a
            // concrete `Nat.add`-headed goal subterm). Mirror of the above:
            // reduce the PATTERN and re-key.
            if let Some(reduced) = reduce_op_projection_head(state, goal, pattern) {
                if let ExprKind::Const(red_name, _) = reduced.get_app_fn().kind() {
                    if red_name == hay_name {
                        return keyed_head_unify(state, goal, ctx, &reduced, haystack);
                    }
                }
            }
        }
        return false;
    }
    let pat_args: Vec<Expr> = pattern.get_app_args().into_iter().cloned().collect();
    let hay_args: Vec<Expr> = haystack.get_app_args().into_iter().cloned().collect();
    if pat_args.len() != hay_args.len() {
        return false;
    }

    state.metas.push_scope();
    let ok = {
        let (metas, env) = state.metas_and_env();
        let mut unifier = Unifier::with_env(metas, env, ctx.clone());
        let levels_ok = pat_levels
            .iter()
            .zip(hay_levels.iter())
            .all(|(lp, lh)| matches!(unifier.unify_levels(lp, lh), UnifyResult::Success));
        levels_ok
            && pat_args.iter().zip(hay_args.iter()).all(|(ap, ah)| {
                // When the pattern argument is a bare (unapplied) metavariable,
                // assign it the SURFACE haystack argument directly rather than
                // routing through `unify`, which WHNF-reduces `ah` first. The
                // downstream `finish_rewrite` step replaces the instantiated
                // `from` pattern by a SYNTACTIC `replace_expr`/`contains_expr`,
                // so a metavar bound to `ah`'s δ-unfolded WHNF (e.g. a reducible
                // `Nat.testBit m i` collapsed to its `Nat.rec` body) would no
                // longer be found in the surface goal, yielding a spurious
                // `RewriteNoMatch`. Binding the surface form keeps the rewrite
                // pattern aligned with the goal's actual syntax. Soundness is
                // unaffected — the resulting `Eq.subst` proof is kernel-checked.
                unifier.try_assign_bare_meta(ap, ah)
                    || matches!(unifier.unify(ap, ah), UnifyResult::Success)
            })
    };
    if ok {
        state.metas.commit();
        true
    } else {
        state.metas.pop_scope();
        false
    }
}

/// Locate the first subterm of `haystack` that is definitionally equal to
/// `needle` but does **not** occur syntactically (so `contains_expr` already
/// failed). Returns the *surface* (un-reduced) goal subterm so the subsequent
/// `replace_expr` / `abstract_over` in [`finish_rewrite`] operate on the goal's
/// actual syntax.
///
/// This is the def-eq fallback that lets `rw` rewrite a use of a reducible
/// definition or an instance-projection-headed application (e.g. `m &&& n =
/// @HAnd.hAnd … Nat.land m n`, which whnf-reduces to `Nat.land m n`) against a
/// rule whose `from`-side is written in the unfolded form (`Nat.land m n`).
/// Real Lean's `rw` matches up to the ambient transparency; this restores that
/// behaviour for the syntactic-replacement path.
///
/// The walk itself (needle gating, head-keyed pre-filter, pre-order traversal)
/// is the shared [`find_defeq_subterm_with`]; this wrapper supplies the
/// tactic-side (`ProofState`) definitional-equality oracle. See the shared
/// helper for the soundness and performance notes.
fn find_defeq_subterm(
    state: &ProofState,
    goal: &Goal,
    haystack: &Expr,
    needle: &Expr,
) -> Option<Expr> {
    find_defeq_subterm_with(haystack, needle, &mut |a, b| state.is_def_eq(goal, a, b))
}

/// Shared tail of `rewrite`: with a concrete equation in hand, replace the
/// `from` side with the `to` side in the goal and build the kernel-checked
/// `Eq.subst` proof. `rule_name` is used only for diagnostics.
fn finish_rewrite(
    state: &mut ProofState,
    goal: &Goal,
    rule_name: &str,
    reverse: bool,
    eqn: RewriteEquation,
) -> TacticResult {
    let RewriteEquation {
        eq_type,
        lhs,
        rhs,
        eq_levels,
        proof: eq_proof,
    } = eqn;

    // Determine what to replace with what
    let (from, to) = if reverse {
        (rhs.clone(), lhs.clone())
    } else {
        (lhs.clone(), rhs.clone())
    };

    // Locate, in the goal, the subterm to be rewritten.
    //
    // `from` is the equation's `from`-side in the *syntactic* form carried by
    // the rule (e.g. `Nat.testBit (Nat.land m n) i`). The goal subterm that the
    // selection phase matched may be a *definitionally equal but syntactically
    // distinct* form of `from` — e.g. `Nat.testBit (m &&& n) i`, where
    // `m &&& n = @HAnd.hAnd … (instHAnd … Nat.land) m n` whnf-reduces (through
    // the instance projection) to `Nat.land m n`. A purely syntactic
    // `contains_expr` would then miss the occurrence, yielding a spurious
    // `RewriteNoMatch` even though real Lean's `rw` (which matches up to the
    // ambient transparency via `kabstract`) succeeds.
    //
    // `from_in_goal` is therefore the *actual surface subterm of the goal* that
    // is rewritten: `from` itself when it occurs syntactically (the common, fast
    // path), otherwise a goal subterm found to be def-eq to `from`. Crucially the
    // equation indices and `eq_proof`/`symm_proof` below still use the original
    // `from`/`to`, so the `Eq.subst` proof type is `motive from`, which
    // `close_goal` checks def-eq against the goal target (`motive from_in_goal`).
    // Soundness is unaffected: matching up to def-eq only changes *which* subterm
    // is selected, never the kernel-rechecked proof term.
    let target = state.metas.instantiate(&goal.target);
    let from_in_goal = if contains_expr(&target, &from) {
        from.clone()
    } else if let Some(actual) = find_defeq_subterm(state, goal, &target, &from) {
        actual
    } else {
        return Err(TacticError::RewriteNoMatch {
            tactic: "rewrite".to_owned(),
            rule: rule_name.to_owned(),
            direction: if reverse { "backward" } else { "forward" }.to_owned(),
            searched_for: from.to_string(),
            focus: target.to_string(),
            focus_path: Vec::new(),
            candidates: rewrite_candidate_summaries(&target, &from, 5),
        });
    };

    // Replace occurrences of the matched surface subterm with `to` in the goal.
    let new_target = replace_expr(&target, &from_in_goal, &to);

    // Create a metavariable for the new goal
    let new_meta_id = state.fresh_meta(new_target.clone());
    let new_meta = Expr::fvar(MetaState::to_fvar(new_meta_id));

    // Build the motive: λ x, target[from_in_goal → x]
    // This is the predicate P such that P(from_in_goal) = target and
    // P(to) = new_target. P(from) is def-eq to target (= P(from_in_goal)).
    let motive = abstract_over(&target, &from_in_goal);

    // Proof construction using Eq.subst:
    // Eq.subst : {α} → {motive : α → Prop} → {a b : α} → Eq a b → motive a → motive b
    //
    // For forward rewrite (eq_proof : a = b, replace a with b in goal G):
    // - Original goal: G[a] = motive(a)
    // - New goal: G[b] = motive(b)
    // - We need: proof of motive(a) from proof of motive(b)
    // - Use Eq.symm eq_proof : b = a, then Eq.subst (Eq.symm eq_proof) : motive(b) → motive(a)
    //
    // For reverse rewrite (eq_proof : a = b, replace b with a in goal G):
    // - Original goal: G[b]
    // - New goal: G[a]
    // - We need: proof of motive(b) from proof of motive(a)
    // - Use eq_proof directly: Eq.subst eq_proof : motive(a) → motive(b)

    let symm_proof = if reverse {
        // reverse: use eq_proof : a = b directly to go from motive(a) to motive(b).
        // from=rhs=b, to=lhs=a, goal was G[b], new goal is G[a].
        eq_proof
    } else {
        // forward: use Eq.symm eq_proof : b = a to go from motive(b) to motive(a)
        let symm = Expr::const_(Name::from_string("Eq.symm"), eq_levels.clone());
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(symm, eq_type.clone()), from.clone()),
                to.clone(),
            ),
            eq_proof,
        )
    };

    // Build: Eq.subst {α} {motive} {to} {from} symm_proof ?m
    let eq_subst = Expr::const_(Name::from_string("Eq.subst"), eq_levels.clone());
    let proof = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(eq_subst, eq_type.clone()),
                        Expr::lam(BinderInfo::Default, eq_type.clone(), motive),
                    ),
                    to.clone(),
                ),
                from.clone(),
            ),
            symm_proof,
        ),
        new_meta.clone(),
    );

    // Close the current goal with the proof
    // Part of #2154: type-check Eq.subst proof before accepting
    state.close_goal(goal, proof)?;

    // Add the new goal
    let new_goal = Goal {
        meta_id: new_meta_id,
        target: new_target,
        local_ctx: goal.local_ctx.clone(),
        tag: None,
    };
    state.goals.push_front(new_goal);

    Ok(())
}

/// Rewrite the goal using an equality hypothesis (left-to-right).
/// Convenience wrapper for `rewrite(state, hyp_name, false)`.
pub fn rewrite_ltr(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    rewrite(state, hyp_name, false)
}

/// Rewrite the goal using an equality hypothesis (right-to-left).
/// Convenience wrapper for `rewrite(state, hyp_name, true)`.
pub fn rewrite_rtl(state: &mut ProofState, hyp_name: &str) -> TacticResult {
    rewrite(state, hyp_name, true)
}

/// Rewrite the goal using an already-elaborated equality *proof term* rather
/// than a name looked up in the local context / environment.
///
/// This backs `rw [show A = B from rfl]`, `rw [lem x y h]`, and any other rw
/// rule whose term is not a bare identifier — the surface term is elaborated by
/// the caller (via `TacticEval::elaborate`, which instantiates universe params
/// as metavariables exactly like an ordinary term position), and its inferred
/// type is matched as `@Eq α lhs rhs`. The proof and decomposed sides are then
/// handed to the same kernel-checked [`finish_rewrite`] path used by the named
/// `rewrite`, so the resulting `Eq.subst` term is re-checked by the kernel.
///
/// # Errors
/// - `TypeCheckFailed` if `proof`'s type cannot be inferred.
/// - `GoalMismatch` if the inferred type is not an equality (after instantiation).
/// - `RewriteNoMatch` if the `from` side does not occur in the goal target.
///
/// REQUIRES: `state.goals` is non-empty.
/// ENSURES: On Ok, the goal target has `from` (`lhs`, or `rhs` if `reverse`)
///   replaced with `to`, justified by a kernel-checked `Eq.subst` proof.
pub fn rewrite_with_proof(state: &mut ProofState, proof: Expr, reverse: bool) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Infer the proof term's type, then resolve any value/universe metavariables
    // introduced by elaboration so the equality sides are syntactically concrete
    // for the structural `contains_expr` / `replace_expr` search in
    // `finish_rewrite` (mirrors the env-constant path's `resolve_all`).
    //
    // We deliberately do NOT WHNF-reduce the inferred type before matching: the
    // `from` side must stay in the same *syntactic* form carried by the proof's
    // type (e.g. `dbl n` from `dbl_unfold n : dbl n = n + n`), so it matches a
    // use of the reducible defined constant in the goal. WHNF would unfold the
    // `from` side to its δ/ι-normal form and the structural `contains_expr`
    // search would then miss the surface occurrence. We only WHNF as a *fallback*
    // when the inferred type is not already an `@Eq` application at the head
    // (e.g. a reducible alias for `Eq`).
    let proof_ty = resolve_all(state, &state.infer_type(&goal, &proof)?);
    let eqn = match match_equality(&proof_ty) {
        Ok((eq_type, lhs, rhs, eq_levels)) => RewriteEquation {
            eq_type: resolve_all(state, &eq_type),
            lhs: resolve_all(state, &lhs),
            rhs: resolve_all(state, &rhs),
            eq_levels: eq_levels
                .iter()
                .map(|l| state.metas.instantiate_level(l))
                .collect(),
            proof: resolve_all(state, &proof),
        },
        Err(eq_err) => {
            // Not a syntactic `Eq`. Adapt an `Iff` proof via `propext`; otherwise
            // fall back to WHNF (reducible alias for `Eq`) before giving up.
            match iff_rewrite_equation(&proof_ty, resolve_all(state, &proof)) {
                Some(mut eqn) => {
                    eqn.lhs = resolve_all(state, &eqn.lhs);
                    eqn.rhs = resolve_all(state, &eqn.rhs);
                    eqn.proof = resolve_all(state, &eqn.proof);
                    eqn
                }
                None => {
                    let reduced = resolve_all(state, &state.whnf(&goal, &proof_ty));
                    let (eq_type, lhs, rhs, eq_levels) =
                        match_equality(&reduced).map_err(|_| eq_err)?;
                    RewriteEquation {
                        eq_type: resolve_all(state, &eq_type),
                        lhs: resolve_all(state, &lhs),
                        rhs: resolve_all(state, &rhs),
                        eq_levels: eq_levels
                            .iter()
                            .map(|l| state.metas.instantiate_level(l))
                            .collect(),
                        proof: resolve_all(state, &proof),
                    }
                }
            }
        }
    };

    finish_rewrite(state, &goal, "<term>", reverse, eqn)
}

/// Rewrite within a specific hypothesis using an equality lemma.
///
/// `rw [lemma] at target_hyp` rewrites occurrences of the LHS of `lemma`
/// with the RHS inside `target_hyp`'s type, constructing a proper proof term
/// via `Eq.subst` to justify the type change.
///
/// # Proof Term Construction
///
/// Given `eq : a = b` and hypothesis `h : T[a]`, this tactic:
/// 1. Computes `new_ty = T[b]`
/// 2. Builds `h_cast := Eq.subst eq h : T[b]` (using motive `λ x, T[x]`)
/// 3. Closes the old goal with `let h' := h_cast in ?new_meta`
/// 4. Creates a new goal where `h'` has type `T[b]`
///
/// This follows Lean 4's `MVarId.replaceLocalDecl` pattern.
pub fn rewrite_at(
    state: &mut ProofState,
    lemma_name: &str,
    target_hyp: &str,
    reverse: bool,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Find the target hypothesis up front so the env-rule path can match the
    // rule's `from` side against this hypothesis's type (not the goal target).
    let target_idx = goal
        .local_ctx
        .iter()
        .position(|d| d.name == target_hyp)
        .ok_or_else(|| TacticError::HypothesisNotFound(target_hyp.to_string()))?;

    let target_fvar = goal.local_ctx[target_idx].fvar;
    let old_ty = goal.local_ctx[target_idx].ty.clone();

    // Resolve the rewrite rule exactly like the at-goal path: a local hypothesis
    // named `lemma_name` shadows an environment constant of the same name; only
    // when no such hypothesis exists do we fall back to the environment so that
    // `rw [Nat.add_zero] at h` resolves the *global lemma*. For the env path the
    // rule's `from` side is unified against the hypothesis type `old_ty` (the
    // location being rewritten), which solves the lemma's quantified
    // metavariables. (#2624 — at-hyp env-lemma resolution.)
    let RewriteEquation {
        eq_type,
        lhs,
        rhs,
        eq_levels,
        proof: lemma_proof,
    } = match goal.local_ctx.iter().find(|d| d.name == lemma_name) {
        Some(lemma_decl) => {
            // Check that the hypothesis is an equality. If it is an `Iff`, adapt
            // via `propext` and feed the same machinery.
            let lemma_ty = state.whnf(&goal, &lemma_decl.ty);
            let lemma_proof = Expr::fvar(lemma_decl.fvar);
            if matches!(lemma_ty.kind(), ExprKind::Pi(..)) {
                // A ∀-quantified local hypothesis (`h : ∀ x, lhs = rhs`) used as
                // the rewrite rule must have its leading binders peeled and
                // solved against the target hypothesis's type `old_ty` before
                // `match_equality` can see the `Eq`/`Iff` head — the same fix as
                // the at-goal `rewrite` path. Kernel still rechecks the resulting
                // `Eq.subst` cast in `replace_local_decl_with_cast`.
                peel_and_resolve_rewrite_equation(
                    state,
                    &goal,
                    lemma_name,
                    reverse,
                    &old_ty,
                    vec![format!("hyp:{target_hyp}")],
                    lemma_proof,
                    lemma_ty,
                )?
            } else {
                match match_equality(&lemma_ty) {
                    Ok((eq_type, lhs, rhs, eq_levels)) => RewriteEquation {
                        eq_type,
                        lhs,
                        rhs,
                        eq_levels,
                        proof: lemma_proof,
                    },
                    Err(eq_err) => iff_rewrite_equation(&lemma_ty, lemma_proof).ok_or(eq_err)?,
                }
            }
        }
        None => resolve_env_rewrite_equation(
            state,
            &goal,
            lemma_name,
            reverse,
            &old_ty,
            vec![format!("hyp:{target_hyp}")],
        )?,
    };

    let (from, to) = if reverse {
        (rhs.clone(), lhs.clone())
    } else {
        (lhs.clone(), rhs.clone())
    };

    // The env-lemma path solved metavariables while matching `from` against the
    // hypothesis type; instantiate so the structural `contains_expr`/`replace_expr`
    // search below sees the concrete (solved) form of `old_ty`.
    let old_ty = state.metas.instantiate(&old_ty);

    // Locate, in the hypothesis type, the subterm to rewrite. As in
    // `finish_rewrite`, prefer the syntactic occurrence of `from`; fall back to a
    // def-eq subterm so a reducible/instance-projected surface form still matches.
    // The equation indices and proof below keep the original `from`/`to`, so the
    // `Eq.subst` term's type is `motive from` — kernel-rechecked def-eq against
    // `motive from_in_hyp` by `replace_local_decl_with_cast`.
    let from_in_hyp = if contains_expr(&old_ty, &from) {
        from.clone()
    } else if let Some(actual) = find_defeq_subterm(state, &goal, &old_ty, &from) {
        actual
    } else {
        return Err(TacticError::RewriteNoMatch {
            tactic: "rewrite_at".to_owned(),
            rule: lemma_name.to_owned(),
            direction: if reverse { "backward" } else { "forward" }.to_owned(),
            searched_for: from.to_string(),
            focus: old_ty.to_string(),
            focus_path: vec![format!("hyp:{target_hyp}")],
            candidates: rewrite_candidate_summaries(&old_ty, &from, 5),
        });
    };

    let new_ty = replace_expr(&old_ty, &from_in_hyp, &to);

    // Build the motive: λ x, T[x] (abstract the matched surface subterm out of
    // old_ty). `motive from` is def-eq to `old_ty` (= `motive from_in_hyp`).
    let motive = abstract_over(&old_ty, &from_in_hyp);

    // Build the equality proof: from = to
    //
    // Forward (reverse=false): lemma is `a = b`, from=a, to=b → eq_proof = lemma
    // Reverse (reverse=true): lemma is `a = b`, from=b, to=a → eq_proof = Eq.symm lemma
    let eq_proof = if reverse {
        let symm = Expr::const_(Name::from_string("Eq.symm"), eq_levels.clone());
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(symm, eq_type.clone()), lhs.clone()),
                rhs.clone(),
            ),
            lemma_proof.clone(),
        )
    } else {
        lemma_proof.clone()
    };

    // Build h_cast := Eq.subst {eq_type} {motive} {from} {to} eq_proof h_old
    //
    // Eq.subst : {α} → {motive : α → Sort u} → {a b : α} → a = b → motive a → motive b
    // h_cast : motive(to) = T[to]  (given h_old : motive(from) = T[from])
    let eq_subst = Expr::const_(Name::from_string("Eq.subst"), eq_levels.clone());
    let h_cast = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(eq_subst, eq_type.clone()),
                        Expr::lam(BinderInfo::Default, eq_type.clone(), motive),
                    ),
                    from.clone(),
                ),
                to.clone(),
            ),
            eq_proof,
        ),
        Expr::fvar(target_fvar), // h_old
    );

    state.replace_local_decl_with_cast(target_fvar, new_ty, h_cast)
}

/// `rw [<proof-term>] at h`: rewrite inside hypothesis `target_hyp` by the
/// equality inferred from an arbitrary proof term (`rw [Nat.add_comm a b] at h`,
/// `rw [lem x y] at h`, `rw [show a = b from p] at h`). This is the at-hypothesis
/// analogue of [`rewrite_with_proof`]: it derives the [`RewriteEquation`] from
/// the proof term (the same `match_equality`/`Iff`-adapt/`whnf`-fallback path)
/// and then applies [`rewrite_at`]'s `Eq.subst`-cast hypothesis rewrite. Kept as
/// a self-contained path (not a refactor of `rewrite_at`) so the proven at-goal
/// and at-hyp env-lemma paths are byte-for-byte unchanged.
pub fn rewrite_at_with_proof(
    state: &mut ProofState,
    proof: Expr,
    target_hyp: &str,
    reverse: bool,
) -> TacticResult {
    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();
    let target_idx = goal
        .local_ctx
        .iter()
        .position(|d| d.name == target_hyp)
        .ok_or_else(|| TacticError::HypothesisNotFound(target_hyp.to_string()))?;
    let target_fvar = goal.local_ctx[target_idx].fvar;
    let old_ty = goal.local_ctx[target_idx].ty.clone();

    // Derive the equation from the proof term (mirrors `rewrite_with_proof`).
    let proof_ty = resolve_all(state, &state.infer_type(&goal, &proof)?);
    let RewriteEquation {
        eq_type,
        lhs,
        rhs,
        eq_levels,
        proof: eq_proof_term,
    } = match match_equality(&proof_ty) {
        Ok((eq_type, lhs, rhs, eq_levels)) => RewriteEquation {
            eq_type: resolve_all(state, &eq_type),
            lhs: resolve_all(state, &lhs),
            rhs: resolve_all(state, &rhs),
            eq_levels: eq_levels
                .iter()
                .map(|l| state.metas.instantiate_level(l))
                .collect(),
            proof: resolve_all(state, &proof),
        },
        Err(eq_err) => match iff_rewrite_equation(&proof_ty, resolve_all(state, &proof)) {
            Some(mut eqn) => {
                eqn.lhs = resolve_all(state, &eqn.lhs);
                eqn.rhs = resolve_all(state, &eqn.rhs);
                eqn.proof = resolve_all(state, &eqn.proof);
                eqn
            }
            None => {
                let reduced = resolve_all(state, &state.whnf(&goal, &proof_ty));
                let (eq_type, lhs, rhs, eq_levels) =
                    match_equality(&reduced).map_err(|_| eq_err)?;
                RewriteEquation {
                    eq_type: resolve_all(state, &eq_type),
                    lhs: resolve_all(state, &lhs),
                    rhs: resolve_all(state, &rhs),
                    eq_levels: eq_levels
                        .iter()
                        .map(|l| state.metas.instantiate_level(l))
                        .collect(),
                    proof: resolve_all(state, &proof),
                }
            }
        },
    };

    // Rewrite the hypothesis by that equation (mirrors `rewrite_at`'s tail).
    let (from, to) = if reverse {
        (rhs.clone(), lhs.clone())
    } else {
        (lhs.clone(), rhs.clone())
    };
    let old_ty = state.metas.instantiate(&old_ty);
    let from_in_hyp = if contains_expr(&old_ty, &from) {
        from.clone()
    } else if let Some(actual) = find_defeq_subterm(state, &goal, &old_ty, &from) {
        actual
    } else {
        return Err(TacticError::RewriteNoMatch {
            tactic: "rewrite_at".to_owned(),
            rule: "<term>".to_owned(),
            direction: if reverse { "backward" } else { "forward" }.to_owned(),
            searched_for: from.to_string(),
            focus: old_ty.to_string(),
            focus_path: vec![format!("hyp:{target_hyp}")],
            candidates: rewrite_candidate_summaries(&old_ty, &from, 5),
        });
    };
    let new_ty = replace_expr(&old_ty, &from_in_hyp, &to);
    let motive = abstract_over(&old_ty, &from_in_hyp);
    let eq_proof = if reverse {
        let symm = Expr::const_(Name::from_string("Eq.symm"), eq_levels.clone());
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(symm, eq_type.clone()), lhs.clone()),
                rhs.clone(),
            ),
            eq_proof_term.clone(),
        )
    } else {
        eq_proof_term.clone()
    };
    let eq_subst = Expr::const_(Name::from_string("Eq.subst"), eq_levels.clone());
    let h_cast = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(eq_subst, eq_type.clone()),
                        Expr::lam(BinderInfo::Default, eq_type.clone(), motive),
                    ),
                    from.clone(),
                ),
                to.clone(),
            ),
            eq_proof,
        ),
        Expr::fvar(target_fvar),
    );
    state.replace_local_decl_with_cast(target_fvar, new_ty, h_cast)
}

/// Rewrite the goal by applying a sequence of equality hypotheses.
///
/// Implements Lean 4's `rw [h1, h2, h3]` syntax. Each entry is a pair of
/// `(hyp_name, direction)` applied sequentially. If any rewrite fails, the
/// entire chain fails and the proof state is left at the point of failure.
///
/// # Example
/// ```text
/// h1 : a = b, h2 : b = c
/// goal : P(a)
/// rw [h1, h2]
/// -- after h1: P(b)
/// -- after h2: P(c)
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: Each `(hyp_name, direction)` refers to an equality hypothesis
/// ENSURES: On Ok, all rewrites applied sequentially
/// ENSURES: On Err, state reflects all rewrites completed before the failure
#[allow(dead_code)] // 2026-08-10: no caller; staged prototype kept per keep-and-annotate doctrine.
pub(crate) fn rewrite_chain(
    state: &mut ProofState,
    steps: &[(&str, RewriteDirection)],
) -> TacticResult {
    for (hyp_name, direction) in steps {
        rewrite(state, hyp_name, direction.is_reverse())?;
    }
    Ok(())
}
