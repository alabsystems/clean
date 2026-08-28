// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proof term construction for the simp tactic.
//!
//! Builds congruence, transitivity, funext, and forall_congr proof terms
//! used by the simplification engine when it needs propositional (non-definitional)
//! proof witnesses.

use clean_kernel::name::Name;
use clean_kernel::tc::whnf_proof::{CongrArgArgs, EqProofBuilder};
use clean_kernel::{BinderData, BinderInfo, Expr, ExprKind, Level};

use super::reduce::{contains_bvar, shift_expr};
use super::types::SimpResult;
use crate::tactic::core::{Goal, ProofState};

/// Chain two SimpResults: if `left` proves `a = b` and `right` proves `b = c`,
/// returns proof of `a = c` via `Eq.trans`.
///
/// # Contract
///
/// REQUIRES: `left.expr` is definitionally equal to the LHS that `right` was applied to
/// ENSURES: Result `.expr` == `right.expr` (the final simplified form)
/// ENSURES: If both proofs are `Some`, result proof is `Eq.trans(left, right)`
/// ENSURES: If either proof is `None` (definitional step), the other is preserved
pub(crate) fn mk_eq_trans(
    left: SimpResult,
    right: SimpResult,
    state: &ProofState,
    goal: &Goal,
) -> SimpResult {
    let proof = match (left.proof, right.proof) {
        (None, p) => p,
        (p, None) => p,
        (Some(p1), Some(p2)) => {
            // If mk_eq_trans_expr fails (type inference error), fall back to
            // p2 rather than None. Returning None here would violate the
            // invariant that proof=None means "definitional change only" — both
            // p1 and p2 are non-definitional proofs so the combined result must
            // also be non-definitional. The kernel catches the type mismatch
            // (p2 : b = c, not a = c) if the proof is consumed.
            Some(mk_eq_trans_expr(state, goal, &p1, &p2).unwrap_or(p2))
        }
    };
    SimpResult {
        expr: right.expr,
        proof,
    }
}

/// Build `@Eq.trans α a b c p1 p2` by inferring types from the proofs.
///
/// `p1 : @Eq α a b` and `p2 : @Eq α b c` → result : `@Eq α a c`.
/// Returns `None` if type inference fails.
///
/// # Contract
///
/// REQUIRES: `p1` has type `@Eq α a b` for some `α`, `a`, `b`
/// REQUIRES: `p2` has type `@Eq α b c` for the same `α` and `b`
/// ENSURES: On Some, result is `@Eq.trans α a b c p1 p2` with type `@Eq α a c`
/// ENSURES: On None, type inference failed for `p1` or `p2`
pub(crate) fn mk_eq_trans_expr(
    state: &ProofState,
    goal: &Goal,
    p1: &Expr,
    p2: &Expr,
) -> Option<Expr> {
    let p1_ty = state.infer_type(goal, p1).ok()?;
    let (eq_ty, a, _b) = super::expr::extract_equality_full(&p1_ty)?;
    let p2_ty = state.infer_type(goal, p2).ok()?;
    let (_, b, c) = super::expr::extract_equality_full(&p2_ty)?;
    let u = get_sort_level(state, goal, &eq_ty)?;

    Some(EqProofBuilder::mk_eq_trans(
        u,
        eq_ty,
        a,
        b,
        c,
        p1.clone(),
        p2.clone(),
    ))
}

/// Build `@Eq.symm α a b h` by inferring types from the proof.
///
/// `h : @Eq α a b` → result : `@Eq α b a`.
/// Returns `None` if type inference fails.
///
/// # Contract
///
/// REQUIRES: `h` has type `@Eq α a b` for some `α`, `a`, `b`
/// ENSURES: On Some, result is `@Eq.symm α a b h` with type `@Eq α b a`
/// ENSURES: On None, type inference failed for `h`
///
/// Part of #2442: enables reverse axiom applications in multi-step ring proofs.
pub(crate) fn mk_eq_symm_expr(state: &ProofState, goal: &Goal, h: &Expr) -> Option<Expr> {
    let h_ty = state.infer_type(goal, h).ok()?;
    let (eq_ty, a, b) = super::expr::extract_equality_full(&h_ty)?;
    let u = get_sort_level(state, goal, &eq_ty)?;
    Some(EqProofBuilder::mk_eq_symm(u, eq_ty, a, b, h.clone()))
}

/// Build `@Eq.refl α a` by inferring the type of `a`.
///
/// Returns `None` if type inference fails.
///
/// Part of #2442: base case for recursive ring axiom proof construction.
pub(crate) fn mk_eq_refl_expr(state: &ProofState, goal: &Goal, a: &Expr) -> Option<Expr> {
    let alpha = state.infer_type(goal, a).ok()?;
    let u = get_sort_level(state, goal, &alpha)?;
    Some(EqProofBuilder::mk_eq_refl(u, alpha, a.clone()))
}

/// Extract the universe level from a type: given α, infer α : Sort u and return u.
///
/// # Contract
///
/// REQUIRES: `ty` is a well-typed expression in the current environment
/// ENSURES: On Some, returns `u` such that `ty : Sort u`
/// ENSURES: On None, `ty` is not a type (its type is not a Sort)
pub(crate) fn get_sort_level(state: &ProofState, goal: &Goal, ty: &Expr) -> Option<Level> {
    let sort = state.infer_type(goal, ty).ok()?;
    match sort.kind() {
        ExprKind::Sort(level) => Some(level.clone()),
        _ => None,
    }
}

/// Build `funext` proof for lambda body simplification.
///
/// Given `body_proof : body_old = body_new` (both may contain BVar(0) referring to
/// the lambda parameter), produces proof of `(λ x : ty, body_old) = (λ x : ty, body_new)`
/// using `funext : {α} {β} {f} {g} → (∀ x, f x = g x) → f = g`.
///
/// # Contract
///
/// REQUIRES: `body_proof` has type `body_old = body_new` (under the binder)
/// REQUIRES: `ty` is the binder domain type
/// REQUIRES: Codomain must not contain BVar(0) (non-dependent case only)
/// ENSURES: On Some, result is `@funext α β f g h` with type `(λ x, body_old) = (λ x, body_new)`
/// ENSURES: On None, codomain is dependent or type inference failed
pub(crate) fn mk_funext(
    state: &ProofState,
    goal: &Goal,
    ty: &Expr,
    body_old: &Expr,
    body_new: &Expr,
    body_proof: &Expr,
) -> Option<Expr> {
    // Fail closed rather than mint a term naming a constant the environment
    // does not have: Clean's own prelude is not guaranteed to carry `funext`,
    // and an `UnknownConst` at the kernel is a worse outcome than simp
    // reporting the step as unproved. (Reachable since `simp::binder` opened
    // binders — before that, `body_proof` was always `None` here.)
    state.env().get_const(&Name::from_string("funext"))?;

    // Infer α (domain type) universe level
    let u = get_sort_level(state, goal, ty)?;

    // Infer β (codomain) from the type of the original lambda.
    // The lambda (λ x : α, body) has type (∀ x : α, T) where T is the body type.
    let lam_old = Expr::lam(BinderInfo::Default, ty.clone(), body_old.clone());
    let lam_ty = state.infer_type(goal, &lam_old).ok()?;
    let codomain = match lam_ty.kind() {
        ExprKind::Pi(_bi, _dom, cod) => cod.as_ref().clone(),
        _ => return None,
    };

    // v = universe level of the codomain.
    // For non-dependent case: codomain has no BVar(0), so we can directly get its sort.
    // For dependent case: codomain contains BVar(0), can't infer sort directly — bail out
    // rather than silently producing a wrong universe level.
    let v = if !contains_bvar(&codomain, 0) {
        get_sort_level(state, goal, &codomain)?
    } else {
        return None;
    };

    // β : α → Sort v  (the codomain as a function of the argument)
    let beta = Expr::lam(BinderInfo::Default, ty.clone(), codomain);

    let f = Expr::lam(BinderInfo::Default, ty.clone(), body_old.clone());
    let g = Expr::lam(BinderInfo::Default, ty.clone(), body_new.clone());
    // h : ∀ x : α, body_old[x] = body_new[x]  (the pointwise proof wrapped in a lambda)
    let h = Expr::lam(BinderInfo::Default, ty.clone(), body_proof.clone());

    // @funext α β f g h
    let mut proof = Expr::const_(Name::from_string("funext"), vec![u, v]);
    proof = Expr::app(proof, ty.clone());
    proof = Expr::app(proof, beta);
    proof = Expr::app(proof, f);
    proof = Expr::app(proof, g);
    proof = Expr::app(proof, h);
    Some(proof)
}

/// Build a `forall_congr` proof for Pi body simplification.
///
/// Given `body_proof : body_old = body_new` (both under a Pi binder, may contain BVar(0)),
/// produces proof of `(∀ x : ty, body_old) = (∀ x : ty, body_new)`.
///
/// Only works for Prop-valued Pi types (∀ x, P x where P : Prop).
///
/// # Which `forall_congr`
///
/// Lean 4 core (`Init/SimpLemmas.lean`) declares
///
/// ```text
/// theorem forall_congr {α : Sort u} {p q : α → Prop}
///     (h : ∀ a, p a = q a) : (∀ a, p a) = (∀ a, q a)
/// ```
///
/// — an **`Eq`** in, an **`Eq`** out. This builder used to emit the
/// `Iff`-shaped Mathlib-style variant instead, wrapping the body proof in
/// `iff_of_eq` and the result in `propext`. That term is ill-typed against the
/// real constant and references `iff_of_eq`, which Clean's own prelude does not
/// even declare. It went unnoticed because the path was unreachable: the body
/// proof was always `None` under a binder (see `simp::binder`), and the one
/// test covering the shape asserted head names without ever kernel-checking.
/// Opening binders made it reachable, so it is now built to Lean's signature —
/// the body proof IS the `h` the constant wants, and no `propext` is involved.
///
/// # Fail-closed
///
/// Returns `None` when the environment has no `forall_congr`, or has one whose
/// conclusion is not an equation (a differently-shaped homonym). Dropping the
/// proof restores the pre-binder-opening behaviour for that step — `simp` then
/// reports the change as non-definitional through `replace_target_def_eq`
/// rather than handing the kernel a term built against a signature that is not
/// there.
///
/// # Contract
///
/// REQUIRES: `body_proof` has type `body_old = body_new` (under the Pi binder)
/// REQUIRES: `ty` is the Pi binder domain type
/// REQUIRES: `(∀ x : ty, body_old) : Prop` (Pi type must be Prop-valued)
/// ENSURES: On Some, result proves `(∀ x : ty, body_old) = (∀ x : ty, body_new)`
/// ENSURES: On None, Pi is non-Prop, `forall_congr` is absent or wrongly
///   shaped, or type inference failed
pub(crate) fn mk_forall_congr(
    state: &ProofState,
    goal: &Goal,
    ty: &Expr,
    body_old: &Expr,
    body_new: &Expr,
    body_proof: &Expr,
) -> Option<Expr> {
    // Check that the Pi type is Prop-valued (Sort 0).
    // forall_congr requires p q : α → Prop, and propext requires Prop equality.
    let pi_old = Expr::pi(BinderInfo::Default, ty.clone(), body_old.clone());
    let pi_old_ty = state.infer_type(goal, &pi_old).ok()?;
    match pi_old_ty.kind() {
        ExprKind::Sort(level) if level.is_zero() => {}
        _ => return None, // Non-Prop Pi — cannot use forall_congr
    }

    // The environment must actually carry Lean's `forall_congr`, and it must
    // conclude in an equation. A missing or Iff-shaped homonym means no proof.
    let forall_congr_name = Name::from_string("forall_congr");
    let decl = state.env().get_const(&forall_congr_name)?;
    let (_conclusion_lhs, _conclusion_rhs) = super::expr::extract_equality_from_type(&decl.type_)?;

    // Universe level of domain α
    let u = get_sort_level(state, goal, ty)?;

    // p = λ x : α, body_old   and   q = λ x : α, body_new
    let p = Expr::lam(BinderInfo::Default, ty.clone(), body_old.clone());
    let q = Expr::lam(BinderInfo::Default, ty.clone(), body_new.clone());

    // h = λ x : α, body_proof   :   ∀ a, p a = q a   (beta)
    let h = Expr::lam(BinderInfo::Default, ty.clone(), body_proof.clone());

    // @forall_congr.{u} α p q h : (∀ a, p a) = (∀ a, q a)
    let mut proof = Expr::const_(forall_congr_name, vec![u]);
    proof = Expr::app(proof, ty.clone());
    proof = Expr::app(proof, p);
    proof = Expr::app(proof, q);
    proof = Expr::app(proof, h);
    Some(proof)
}

/// Build a congruence proof for rewriting a nondependent Pi domain.
///
/// Given `domain_proof : old_domain = new_domain`, produces a proof of
/// `(old_domain -> body) = (new_domain -> body)` by congruence over
/// `fun domain => forall (_ : domain), body`.
///
/// This intentionally rejects dependent bodies: changing the domain while the
/// body references the binder needs a stronger dependent forall congruence.
pub(crate) fn mk_pi_domain_congr(
    state: &ProofState,
    goal: &Goal,
    bi: BinderData,
    old_domain: &Expr,
    new_domain: &Expr,
    body: &Expr,
    domain_proof: &Expr,
) -> Option<Expr> {
    if contains_bvar(body, 0) {
        return None;
    }

    let domain_type = state.infer_type(goal, old_domain).ok()?;
    let body_under_lambda = shift_expr(body, 1);
    let pi_family = Expr::lam(
        BinderInfo::Default,
        domain_type,
        Expr::pi(bi, Expr::bvar(0), body_under_lambda),
    );

    mk_congr_arg(
        state,
        goal,
        &pi_family,
        old_domain,
        new_domain,
        domain_proof,
    )
}

/// Build a proof that rewrites the LHS of an equality target.
///
/// Given `h : old_lhs = new_lhs`, produces a proof of
/// `(@Eq α old_lhs rhs) = (@Eq α new_lhs rhs)`.
///
/// Uses `congrFun (congrArg (@Eq α) h) rhs`:
/// 1. `congrArg (@Eq α) h` proves `(@Eq α) old_lhs = (@Eq α) new_lhs`
/// 2. `congrFun ... rhs` proves `(@Eq α old_lhs) rhs = (@Eq α new_lhs) rhs`
///
/// # Contract
///
/// REQUIRES: `h` has type `@Eq α old_lhs new_lhs`
/// REQUIRES: `eq_type` is `α`, the type being compared
/// ENSURES: On Some, result has type `(@Eq α old_lhs rhs) = (@Eq α new_lhs rhs)`
/// ENSURES: On None, type inference failed
pub(crate) fn mk_eq_lhs_congr(
    state: &ProofState,
    goal: &Goal,
    eq_type: &Expr,
    old_lhs: &Expr,
    new_lhs: &Expr,
    rhs: &Expr,
    h: &Expr,
) -> Option<Expr> {
    let u = get_sort_level(state, goal, eq_type)?;
    // @Eq.{u} α : α → α → Prop
    let eq_alpha = Expr::app(
        Expr::const_(Name::from_string("Eq"), vec![u]),
        eq_type.clone(),
    );

    // Step 1: congrArg (@Eq α) h
    // Proves: (@Eq α) old_lhs = (@Eq α) new_lhs
    let inner = mk_congr_arg(state, goal, &eq_alpha, old_lhs, new_lhs, h)?;

    // Step 2: congrFun inner rhs
    // Proves: (@Eq α old_lhs) rhs = (@Eq α new_lhs) rhs
    let old_partial = Expr::app(eq_alpha.clone(), old_lhs.clone());
    let new_partial = Expr::app(eq_alpha, new_lhs.clone());
    mk_congr_fun(state, goal, &old_partial, &new_partial, rhs, &inner)
}

/// Build `congrArg` proof: given `h : a₁ = a₂`, produce proof of `f a₁ = f a₂`.
///
/// `congrArg : {α : Sort u} → {β : Sort v} → {a₁ a₂ : α} → (f : α → β) → a₁ = a₂ → f a₁ = f a₂`
///
/// # Contract
///
/// REQUIRES: `h` has type `@Eq α a1 a2`
/// REQUIRES: `f` has type `α → β` for some `β`
/// ENSURES: On Some, result has type `@Eq β (f a1) (f a2)`
/// ENSURES: On None, type inference failed for `a1`, `f`, or sort levels
pub(crate) fn mk_congr_arg(
    state: &ProofState,
    goal: &Goal,
    f: &Expr,
    a1: &Expr,
    a2: &Expr,
    h: &Expr,
) -> Option<Expr> {
    let alpha = state.infer_type(goal, a1).ok()?;
    let beta = state
        .infer_type(goal, &Expr::app(f.clone(), a1.clone()))
        .ok()?;
    let u = get_sort_level(state, goal, &alpha)?;
    let v = get_sort_level(state, goal, &beta)?;
    Some(EqProofBuilder::mk_congr_arg(CongrArgArgs {
        u,
        v,
        alpha,
        beta,
        a1: a1.clone(),
        a2: a2.clone(),
        f: f.clone(),
        h: h.clone(),
    }))
}

/// Build `congrFun'` proof: given `h : f = g`, produce proof of `f a = g a`.
///
/// `congrFun' : {α : Sort u} → {β : Sort v} → {f g : α → β} → f = g → (a : α) → f a = g a`
///
/// # Contract
///
/// REQUIRES: `h` has type `@Eq (α → β) f_old f_new`
/// REQUIRES: `a` has type `α`
/// ENSURES: On Some, result has type `@Eq β (f_old a) (f_new a)`
/// ENSURES: On None, type inference failed for `a`, `f_old`, or sort levels
pub(crate) fn mk_congr_fun(
    state: &ProofState,
    goal: &Goal,
    f_old: &Expr,
    f_new: &Expr,
    a: &Expr,
    h: &Expr,
) -> Option<Expr> {
    let alpha = state.infer_type(goal, a).ok()?;
    let beta = state
        .infer_type(goal, &Expr::app(f_old.clone(), a.clone()))
        .ok()?;
    let u = get_sort_level(state, goal, &alpha)?;
    let v = get_sort_level(state, goal, &beta)?;
    Some(EqProofBuilder::mk_congr_fun(
        u,
        v,
        alpha,
        beta,
        f_old.clone(),
        f_new.clone(),
        h.clone(),
        a.clone(),
    ))
}

/// Build `congr` proof: given `h₁ : f₁ = f₂` and `h₂ : a₁ = a₂`, produce proof of `f₁ a₁ = f₂ a₂`.
///
/// `congr : {α : Sort u} → {β : Sort v} → {f₁ f₂ : α → β} → {a₁ a₂ : α} → f₁ = f₂ → a₁ = a₂ → f₁ a₁ = f₂ a₂`
///
/// # Contract
///
/// REQUIRES: `h_f` has type `@Eq (α → β) f_old f_new`
/// REQUIRES: `h_a` has type `@Eq α a_old a_new`
/// ENSURES: On Some, result has type `@Eq β (f_old a_old) (f_new a_new)`
/// ENSURES: On None, type inference failed for arguments or sort levels
pub(crate) fn mk_congr(
    state: &ProofState,
    goal: &Goal,
    f_old: &Expr,
    f_new: &Expr,
    a_old: &Expr,
    a_new: &Expr,
    h_f: &Expr,
    h_a: &Expr,
) -> Option<Expr> {
    let alpha = state.infer_type(goal, a_old).ok()?;
    let beta = state
        .infer_type(goal, &Expr::app(f_old.clone(), a_old.clone()))
        .ok()?;
    let u = get_sort_level(state, goal, &alpha)?;
    let v = get_sort_level(state, goal, &beta)?;
    Some(EqProofBuilder::mk_congr(
        u,
        v,
        alpha,
        beta,
        f_old.clone(),
        f_new.clone(),
        a_old.clone(),
        a_new.clone(),
        h_f.clone(),
        h_a.clone(),
    ))
}
