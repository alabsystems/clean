// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! C008 induction proof builders: base/step types, values, and Nat.rec proof.
//!
//! Split from `nn_verify_ibp_tightness_defs` for file-size compliance.
//!
//! Contains:
//! - `build_inner_bound_prop` — inner proposition at each k (LE bound)
//! - `build_ibp_tightness_base_type` — base case type (k=0)
//! - `build_ibp_tightness_step_type` — inductive step type (k -> k+1)
//! - `build_ibp_tightness_nat_induction_proof` — Nat.rec proof combining the
//!   base + step (now honest admitted `Declaration::Axiom`s)
//!
//! Part of #3374 / soundness-certificate capstone: the C008 base/step are
//! honest admitted axioms (no sorry); the inductive theorem composes them via
//! `Nat.rec`.

use super::nn_verify_ibp_tightness::IbpTightnessConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

// =============================================================================
// Inner proposition helper for Nat.rec induction
// =============================================================================

/// Build the inner bound proposition at a given `k` expression,
/// with all network parameters already allocated as free variables.
///
/// ```text
/// ibp_width (output_dim k) (ibp_propagate k output_dim weight bias (eps_ball ...))
///   <= 2 * eps * norm_product k norms
/// ```
///
/// Analogous to `build_inner_prop` in `nn_verify_blockwise_crown_defs.rs`.
///
/// Exposed `pub(super)` (under the alias `inner_bound_prop_at`) so the R-weak
/// `ibp_tightness_step` proof in `nn_verify_ibp_tightness_step_value` can build
/// the (consumed-but-unused) induction-hypothesis binder type identically.
pub(super) fn inner_bound_prop_at(
    c: &IbpTightnessConsts,
    b: &EnvDeclBuilder,
    k: &Expr,
    output_dim: &Expr,
    weight: &Expr,
    bias: &Expr,
    center: &Expr,
    eps: &Expr,
) -> Expr {
    build_inner_bound_prop(c, b, k, output_dim, weight, bias, center, eps)
}

fn build_inner_bound_prop(
    c: &IbpTightnessConsts,
    b: &EnvDeclBuilder,
    k: &Expr,
    output_dim: &Expr,
    weight: &Expr,
    bias: &Expr,
    center: &Expr,
    eps: &Expr,
) -> Expr {
    let input_bounds = c.eps_ball_app(
        c.out_dim(output_dim, c.nat_zero.clone()),
        center.clone(),
        eps.clone(),
    );
    let propagated = c.ibp_propagate_app(
        k.clone(),
        output_dim.clone(),
        weight.clone(),
        bias.clone(),
        input_bounds,
    );
    let lhs = c.ibp_width_app(c.out_dim(output_dim, k.clone()), propagated);
    let norms = c.norm_lambda(b, k, output_dim, weight);
    let rhs = c.base.mul(
        c.base.mul(c.two(), eps.clone()),
        c.norm_product_app(k.clone(), norms),
    );
    c.base.rat_le(lhs, rhs)
}

// =============================================================================
// Base case axiom type
// =============================================================================

/// Build type for `NNVerify.ibp_tightness_base`:
/// ```text
/// forall (output_dim : Nat -> Nat)
///   (weight : (i : Nat) -> NNMat (output_dim (i+1)) (output_dim i))
///   (bias : (i : Nat) -> NNVec (output_dim (i+1)))
///   (center : NNVec (output_dim 0))
///   (eps : Rat),
///   Rat.le Rat.zero eps ->
///   ibp_width (output_dim 0) (ibp_propagate 0 output_dim weight bias (eps_ball ...))
///     <= 2 * eps * norm_product 0 norms
/// ```
///
/// The base case of induction at k=0. Encodes that an eps-ball input has
/// width bounded by 2*eps (since propagate at 0 is identity and norm_product
/// at 0 is 1).
///
/// # Statement redesign (designs/2026-04-18-c008-statement-redesign.md)
///
/// The `Rat.le Rat.zero eps` hypothesis is REQUIRED. Without it the base
/// case is mathematically false: `eps_ball` currently returns zero-width
/// bounds so LHS = 0, but `2 * eps * 1` can be negative when `eps < 0`.
/// The hypothesis matches the mathematical intent (eps is a perturbation
/// radius, non-negative by definition).
pub(super) fn build_ibp_tightness_base_type(c: &IbpTightnessConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let output_dim_ty = c.output_dim_ty();
    let (od_id, output_dim) = b.fresh_local(output_dim_ty.clone());
    let weight_ty = c.weight_family_ty(&b, &output_dim);
    let (w_id, weight) = b.fresh_local(weight_ty.clone());
    let bias_ty = c.bias_family_ty(&b, &output_dim);
    let (bias_id, bias) = b.fresh_local(bias_ty.clone());
    let center_ty = c.center_ty(&output_dim);
    let (center_id, center) = b.fresh_local(center_ty.clone());
    let (eps_id, eps) = b.fresh_local(c.base.rat.clone());
    let nonneg_ty = c.base.rat_le(c.base.rat_zero.clone(), eps.clone());
    let (h_nonneg_id, _h_nonneg) = b.fresh_local(nonneg_ty.clone());

    let inner = build_inner_bound_prop(
        c,
        &b,
        &c.nat_zero.clone(),
        &output_dim,
        &weight,
        &bias,
        &center,
        &eps,
    );

    let e = b.mk_pi(h_nonneg_id, BinderInfo::Default, nonneg_ty, inner);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.base.rat.clone(), e);
    let e = b.mk_pi(center_id, BinderInfo::Default, center_ty, e);
    let e = b.mk_pi(bias_id, BinderInfo::Default, bias_ty, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, weight_ty, e);
    let e = b.mk_pi(od_id, BinderInfo::Default, output_dim_ty, e);
    b.finish(e)
}

// =============================================================================
// Base case CONSTRUCTIVE proof (#3490 T6 / #3476)
// =============================================================================

/// Build the constructive proof term for `NNVerify.ibp_tightness_base`.
///
/// The base case at `k = 0` states (after the `output_dim … eps` binders and
/// the `h_nonneg : Rat.le 0 eps` hypothesis):
/// ```text
/// ibp_width (output_dim 0)
///   (ibp_propagate 0 output_dim weight bias (eps_ball (output_dim 0) center eps))
///   ≤ 2 * eps * norm_product 0 norms
/// ```
///
/// Proof architecture (zero domain-specific axioms; closure ⊆ FOUNDATIONAL ∪
/// the constructive Rat/NNVerify helper Theorems):
///
/// * The LHS is collapsed to `Rat.zero` by the kernel-checked Theorem
///   `NNVerify.eps_ball_width_is_zero (output_dim 0) center eps`. The kernel
///   first ι-reduces `ibp_propagate 0 …` (the zero-case of its `Nat.rec` is the
///   identity) so the LHS is definitionally
///   `ibp_width (output_dim 0) (eps_ball (output_dim 0) center eps)`, which that
///   Theorem equates to `Rat.zero`.
/// * The RHS obligation `Rat.zero ≤ 2 * eps * norm_product 0 norms` is closed by
///   `Rat.mul_nonneg`: `2 * eps ≥ 0` (from `0 ≤ 2` and `h_nonneg : 0 ≤ eps`)
///   and `norm_product 0 norms ≥ 0` (it ι-reduces to `Rat.one`, so `0 ≤ 1`
///   discharges it definitionally).
/// * The two are combined by `NNVerify.le_of_eq_of_le`.
///
/// HONESTY: this leans on `eps_ball`'s registered zero-width placeholder body
/// (`eps_ball n c e ≡ IntervalBounds.mk n 0⃗ 0⃗ _`). The proof is a genuine
/// `Nat.rec`-free assembly over real kernel reductions, not a masquerade — but
/// the LHS is `0` only because the placeholder ball has zero width. The
/// non-negativity hypothesis `h_nonneg` is consumed genuinely (a negative `eps`
/// makes the RHS negative and the statement false).
pub(super) fn build_ibp_tightness_base_value(c: &IbpTightnessConsts) -> Expr {
    let le_of_eq_of_le = Expr::const_(Name::from_string("NNVerify.le_of_eq_of_le"), vec![]);
    let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
    let eps_ball_width_is_zero =
        Expr::const_(Name::from_string("NNVerify.eps_ball_width_is_zero"), vec![]);
    let zero_le_one = Expr::const_(Name::from_string("NNVerify.rat_zero_le_one"), vec![]);
    let zero_le_two = Expr::const_(Name::from_string("NNVerify.rat_zero_le_two"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let output_dim_ty = c.output_dim_ty();
    let (od_id, output_dim) = b.fresh_local(output_dim_ty.clone());
    let weight_ty = c.weight_family_ty(&b, &output_dim);
    let (w_id, weight) = b.fresh_local(weight_ty.clone());
    let bias_ty = c.bias_family_ty(&b, &output_dim);
    let (bias_id, bias) = b.fresh_local(bias_ty.clone());
    let center_ty = c.center_ty(&output_dim);
    let (center_id, center) = b.fresh_local(center_ty.clone());
    let (eps_id, eps) = b.fresh_local(c.base.rat.clone());
    let nonneg_ty = c.base.rat_le(c.base.rat_zero.clone(), eps.clone());
    let (h_nonneg_id, h_nonneg) = b.fresh_local(nonneg_ty.clone());

    let out0 = c.out_dim(&output_dim, c.nat_zero.clone());

    // LHS: ibp_width (output_dim 0) (ibp_propagate 0 … (eps_ball (output_dim 0) center eps))
    let input_bounds = c.eps_ball_app(out0.clone(), center.clone(), eps.clone());
    let propagated = c.ibp_propagate_app(
        c.nat_zero.clone(),
        output_dim.clone(),
        weight.clone(),
        bias.clone(),
        input_bounds,
    );
    let lhs = c.ibp_width_app(out0.clone(), propagated);

    // RHS: 2 * eps * norm_product 0 norms
    let norms = c.norm_lambda(&b, &c.nat_zero.clone(), &output_dim, &weight);
    let two_eps = c.base.mul(c.two(), eps.clone());
    let np0 = c.norm_product_app(c.nat_zero.clone(), norms);
    let rhs = c.base.mul(two_eps.clone(), np0.clone());

    // h_eq : ibp_width (output_dim 0) (eps_ball (output_dim 0) center eps) = Rat.zero
    // (def-eq to `lhs = Rat.zero` after ι on ibp_propagate at 0).
    let h_eq = Expr::apps(
        eps_ball_width_is_zero,
        [out0.clone(), center.clone(), eps.clone()],
    );

    // h_2eps : 0 ≤ 2 * eps  via  Rat.mul_nonneg 2 eps (0 ≤ 2) h_nonneg.
    let h_2eps = Expr::apps(
        mul_nonneg.clone(),
        [c.two(), eps.clone(), zero_le_two, h_nonneg],
    );
    // h_rhs : 0 ≤ 2 * eps * norm_product 0 norms  via Rat.mul_nonneg.
    // The second factor `norm_product 0 norms` ι-reduces to `Rat.one`, so the
    // `0 ≤ norm_product 0 norms` argument is discharged definitionally by
    // `rat_zero_le_one : 0 ≤ Rat.one`.
    let h_rhs = Expr::apps(mul_nonneg, [two_eps, np0, h_2eps, zero_le_one]);

    // le_of_eq_of_le lhs Rat.zero rhs h_eq h_rhs : lhs ≤ rhs.
    let body = Expr::apps(
        le_of_eq_of_le,
        [lhs, c.base.rat_zero.clone(), rhs, h_eq, h_rhs],
    );

    let e = b.mk_lam(h_nonneg_id, BinderInfo::Default, nonneg_ty, body);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.base.rat.clone(), e);
    let e = b.mk_lam(center_id, BinderInfo::Default, center_ty, e);
    let e = b.mk_lam(bias_id, BinderInfo::Default, bias_ty, e);
    let e = b.mk_lam(w_id, BinderInfo::Default, weight_ty, e);
    let e = b.mk_lam(od_id, BinderInfo::Default, output_dim_ty, e);
    b.finish(e)
}

// =============================================================================
// Inductive step type
// =============================================================================

/// Build type for `NNVerify.ibp_tightness_step`:
/// ```text
/// forall (k : Nat) (output_dim : Nat -> Nat)
///   (weight : (i : Nat) -> NNMat (output_dim (i+1)) (output_dim i))
///   (bias : (i : Nat) -> NNVec (output_dim (i+1)))
///   (center : NNVec (output_dim 0))
///   (eps : Rat),
///   Rat.le Rat.zero eps ->
///   (bound at k) -> (bound at k+1)
/// ```
///
/// Takes the induction hypothesis at k and produces the result at succ k.
/// The mathematical content relies on ibp_width_affine_le (affine layer
/// multiplies width by infinity norm) and ibp_width_relu_le (ReLU
/// does not increase width).
///
/// Statement redesign (designs/2026-04-18-c008-statement-redesign.md):
/// carries the `eps >= 0` hypothesis. It is NOT used by the inner_bound
/// propositions (they are stated in terms of eps directly), but the step
/// proof will use `h_nonneg` together with `mul_nonneg_le_left` to combine
/// the per-layer norm amplification. The IH does not carry `h_nonneg` again
/// — it is already in scope.
pub(super) fn build_ibp_tightness_step_type(c: &IbpTightnessConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let output_dim_ty = c.output_dim_ty();
    let (od_id, output_dim) = b.fresh_local(output_dim_ty.clone());
    let weight_ty = c.weight_family_ty(&b, &output_dim);
    let (w_id, weight) = b.fresh_local(weight_ty.clone());
    let bias_ty = c.bias_family_ty(&b, &output_dim);
    let (bias_id, bias) = b.fresh_local(bias_ty.clone());
    let center_ty = c.center_ty(&output_dim);
    let (center_id, center) = b.fresh_local(center_ty.clone());
    let (eps_id, eps) = b.fresh_local(c.base.rat.clone());
    let nonneg_ty = c.base.rat_le(c.base.rat_zero.clone(), eps.clone());
    let (h_nonneg_id, _h_nonneg) = b.fresh_local(nonneg_ty.clone());

    let ih = build_inner_bound_prop(c, &b, &k, &output_dim, &weight, &bias, &center, &eps);
    let k_succ = Expr::app(c.nat_succ.clone(), k);
    let concl = build_inner_bound_prop(c, &b, &k_succ, &output_dim, &weight, &bias, &center, &eps);
    let step_body = Expr::pi(BinderInfo::Default, ih, concl);

    let e = b.mk_pi(h_nonneg_id, BinderInfo::Default, nonneg_ty, step_body);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.base.rat.clone(), e);
    let e = b.mk_pi(center_id, BinderInfo::Default, center_ty, e);
    let e = b.mk_pi(bias_id, BinderInfo::Default, bias_ty, e);
    let e = b.mk_pi(w_id, BinderInfo::Default, weight_ty, e);
    let e = b.mk_pi(od_id, BinderInfo::Default, output_dim_ty, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Nat.rec induction proof for ibp_tightness_bound_inductive
// =============================================================================

/// Build constructive proof term for `NNVerify.ibp_tightness_bound_inductive`.
///
/// Previously an axiom, this is now a `Declaration::Theorem` with a proof
/// term built from `Nat.rec` combining the base and step axioms:
///
/// ```text
/// fun (k : Nat) (output_dim : Nat -> Nat) (weight : ...) (bias : ...)
///     (center : NNVec (output_dim 0)) (eps : Rat) (h_nonneg : Rat.le 0 eps) =>
///   @Nat.rec (fun k => bound_prop k)
///     (ibp_tightness_base output_dim weight bias center eps h_nonneg)
///     (fun n ih => ibp_tightness_step n output_dim weight bias center eps h_nonneg ih)
///     k
/// ```
///
/// Part of #3374: replace C008 axioms with constructive proof terms.
/// Statement redesign (2026-04-18): thread `h_nonneg : Rat.le 0 eps` through
/// `Nat.rec`. The hypothesis is bound outside the recursor and passed to both
/// base and step applications. The motive still quantifies over `k` only.
pub(super) fn build_ibp_tightness_nat_induction_proof(c: &IbpTightnessConsts) -> Expr {
    let nat_rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::zero()], // Sort 0 = Prop target
    );
    let base_const = Expr::const_(Name::from_string("NNVerify.ibp_tightness_base"), vec![]);
    let step_const = Expr::const_(Name::from_string("NNVerify.ibp_tightness_step"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (k_id, k) = b.fresh_local(c.base.nat.clone());
    let output_dim_ty = c.output_dim_ty();
    let (od_id, output_dim) = b.fresh_local(output_dim_ty.clone());
    let weight_ty = c.weight_family_ty(&b, &output_dim);
    let (w_id, weight) = b.fresh_local(weight_ty.clone());
    let bias_ty = c.bias_family_ty(&b, &output_dim);
    let (bias_id, bias) = b.fresh_local(bias_ty.clone());
    let center_ty = c.center_ty(&output_dim);
    let (center_id, center) = b.fresh_local(center_ty.clone());
    let (eps_id, eps) = b.fresh_local(c.base.rat.clone());
    let nonneg_ty = c.base.rat_le(c.base.rat_zero.clone(), eps.clone());
    let (h_nonneg_id, h_nonneg) = b.fresh_local(nonneg_ty.clone());

    // Motive: fun k => bound_prop k (the LE proposition at each k)
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (mk_id, mk) = ch.fresh_local(c.base.nat.clone());
        let inner = build_inner_bound_prop(c, &ch, &mk, &output_dim, &weight, &bias, &center, &eps);
        let r = ch.mk_lam(mk_id, BinderInfo::Default, c.base.nat.clone(), inner);
        ch.finish_child(r)
    };

    // Zero case: ibp_tightness_base output_dim weight bias center eps h_nonneg
    let zero_case = Expr::apps(
        base_const,
        [
            output_dim.clone(),
            weight.clone(),
            bias.clone(),
            center.clone(),
            eps.clone(),
            h_nonneg.clone(),
        ],
    );

    // Succ case: fun n ih => ibp_tightness_step n output_dim weight bias center eps h_nonneg ih
    let succ_case = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = ch.fresh_local(c.base.nat.clone());
        let ih_ty = build_inner_bound_prop(c, &ch, &n, &output_dim, &weight, &bias, &center, &eps);
        let (ih_id, ih) = ch.fresh_local(ih_ty.clone());
        let body = Expr::apps(
            step_const,
            [
                n.clone(),
                output_dim.clone(),
                weight.clone(),
                bias.clone(),
                center.clone(),
                eps.clone(),
                h_nonneg.clone(),
                ih,
            ],
        );
        let r = ch.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
        let r = ch.mk_lam(n_id, BinderInfo::Default, c.base.nat.clone(), r);
        ch.finish_child(r)
    };

    // Nat.rec motive zero_case succ_case k
    let rec_result = Expr::apps(nat_rec, [motive, zero_case, succ_case, k.clone()]);

    let e = b.mk_lam(h_nonneg_id, BinderInfo::Default, nonneg_ty, rec_result);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.base.rat.clone(), e);
    let e = b.mk_lam(center_id, BinderInfo::Default, center_ty, e);
    let e = b.mk_lam(bias_id, BinderInfo::Default, bias_ty, e);
    let e = b.mk_lam(w_id, BinderInfo::Default, weight_ty, e);
    let e = b.mk_lam(od_id, BinderInfo::Default, output_dim_ty, e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.base.nat.clone(), e);
    b.finish(e)
}
