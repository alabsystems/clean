// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Q RHS` proof for T12 `to_ibp_sound` — the goal with `x` replaced by the
//! containment witness `RHS = center + G·ε`.
//!
//! `Q RHS ≡ ∀ i, (center i − radius i ≤ RHS i) ∧ (RHS i ≤ center i + radius i)`,
//! with `RHS i ≡ center i + sᵢ`, `sᵢ = Σⱼ (G i j · εⱼ)`, `radius i = Σⱼ |G i j|`.
//!
//! Per `i` (`s := Σⱼ (G i j · εⱼ)`, `r := Σⱼ |G i j|`, `ci := center i`):
//!   * **upper** `ci + s ≤ ci + r`: `Rat.add_le_add_left s r h_s_le_r ci`, with
//!     `h_s_le_r : s ≤ r` from `Fin.sum_le` and the per-summand `upper_summand`.
//!   * **lower** `ci − r ≤ ci + s` (`ci − r ≡ ci + (−r)`):
//!     `Rat.add_le_add_left (−r) s h_negr_le_s ci`, with `h_negr_le_s : −r ≤ s`
//!     obtained by `Fin.sum_le` over `lower_summand` giving `Σⱼ(−|G i j|) ≤ s`,
//!     then transporting the LHS `Σⱼ(−|G i j|) → −r` via `Fin.sum_neg`.

use super::nn_verify_zonotope_to_ibp_sound_proof::T12Consts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Build `Q RHS : ∀ i, (ci − r ≤ RHS i) ∧ (RHS i ≤ ci + r)`.
///
/// `RHS i` is reconstructed here in its reduced `ci + Σⱼ (G i j · εⱼ)` form
/// (def-eq to the caller's `NNVec.add center (NNMat.mulVec gens ε) i`), so no
/// separate `rhs` term is threaded in.
#[allow(clippy::too_many_arguments)]
pub(super) fn build_q_at_rhs(
    h: &T12Consts,
    parent: &EnvDeclBuilder,
    n: &Expr,
    k: &Expr,
    center: &Expr,
    gens: &Expr,
    eps: &Expr,
    hbound: &Expr,
) -> Expr {
    let fin_n = Expr::app(h.fin.clone(), n.clone());
    let mut ch = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = ch.fresh_local(fin_n.clone());

    let center_i = Expr::app(center.clone(), i.clone());
    let gens_i = Expr::app(gens.clone(), i.clone());
    // RHS i (def-eq to ci + s); we use the explicit reduced form ci + s where
    // s = Fin.sum k (fun j => Rat.mul (G i j) (ε j)).
    let f_t = summand_fn_t(h, &ch, k, &gens_i, eps);
    let f_abs = summand_fn_abs(h, &ch, k, &gens_i);
    let f_neg_abs = summand_fn_neg_abs(h, &ch, k, &gens_i);
    let s = h.sum_pub(k, f_t.clone());
    let r = h.sum_pub(k, f_abs.clone());
    let rhs_i = h.add_pub(center_i.clone(), s.clone());

    // h_s_le_r : s ≤ r  via Fin.sum_le k f_t f_abs (fun j => upper_summand …).
    let pw_upper = pointwise_upper(h, &ch, k, &gens_i, eps, hbound);
    let h_s_le_r = Expr::apps(
        h.fin_sum_le.clone(),
        [k.clone(), f_t.clone(), f_abs.clone(), pw_upper],
    );
    // upper : ci + s ≤ ci + r  via Rat.add_le_add_left s r h_s_le_r ci.
    let upper = Expr::apps(
        h.add_le_add_left.clone(),
        [s.clone(), r.clone(), h_s_le_r, center_i.clone()],
    );

    // h_negsum_le_s : Σⱼ(−|G i j|) ≤ s  via Fin.sum_le k f_neg_abs f_t (lower).
    let pw_lower = pointwise_lower(h, &ch, k, &gens_i, eps, hbound);
    let neg_sum = h.sum_pub(k, f_neg_abs.clone());
    let h_negsum_le_s = Expr::apps(
        h.fin_sum_le.clone(),
        [k.clone(), f_neg_abs, f_t.clone(), pw_lower],
    );
    // Fin.sum_neg k f_abs : Σⱼ(−|G i j|) = −(Σⱼ|G i j|) = −r.
    let h_sum_neg = Expr::apps(h.fin_sum_neg.clone(), [k.clone(), f_abs]);
    let neg_r = Expr::app(h.rat_neg.clone(), r.clone());
    // transport LHS Σⱼ(−|G i j|) → −r.
    let h_negr_le_s = transport_le_lhs(
        h,
        &ch,
        s.clone(),
        neg_sum,
        neg_r.clone(),
        h_negsum_le_s,
        h_sum_neg,
    );
    // lower : ci + (−r) ≤ ci + s  via Rat.add_le_add_left (−r) s h_negr_le_s ci.
    //   (goal LHS `ci − r ≡ ci + (−r)`; goal RHS `RHS i ≡ ci + s`.)
    let lower = Expr::apps(
        h.add_le_add_left.clone(),
        [neg_r, s, h_negr_le_s, center_i.clone()],
    );

    // And.intro (ci − r ≤ RHS i) (RHS i ≤ ci + r) lower upper.
    let sub_ci_r = Expr::apps(
        Expr::const_(Name::from_string("Rat.sub"), vec![]),
        [center_i.clone(), r.clone()],
    );
    let upper_term = h.add_pub(center_i, r);
    let p_lo = h.rat_le_pub(sub_ci_r, rhs_i.clone());
    let p_hi = h.rat_le_pub(rhs_i, upper_term);
    let conj = Expr::apps(h.and_intro.clone(), [p_lo, p_hi, lower, upper]);

    ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, conj))
}

/// `fun (j : Fin k) => Rat.mul (G i j) (ε j)`.
fn summand_fn_t(
    h: &T12Consts,
    parent: &EnvDeclBuilder,
    k: &Expr,
    gens_i: &Expr,
    eps: &Expr,
) -> Expr {
    let fin_k = Expr::app(h.fin.clone(), k.clone());
    let mut d = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = d.fresh_local(fin_k.clone());
    let body = Expr::apps(
        h.rat_mul.clone(),
        [
            Expr::app(gens_i.clone(), j.clone()),
            Expr::app(eps.clone(), j),
        ],
    );
    d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k, body))
}

/// `fun (j : Fin k) => Rat.abs (G i j)`.
fn summand_fn_abs(h: &T12Consts, parent: &EnvDeclBuilder, k: &Expr, gens_i: &Expr) -> Expr {
    let fin_k = Expr::app(h.fin.clone(), k.clone());
    let mut d = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = d.fresh_local(fin_k.clone());
    let body = Expr::app(h.rat_abs.clone(), Expr::app(gens_i.clone(), j));
    d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k, body))
}

/// `fun (j : Fin k) => Rat.neg (Rat.abs (G i j))`.
fn summand_fn_neg_abs(h: &T12Consts, parent: &EnvDeclBuilder, k: &Expr, gens_i: &Expr) -> Expr {
    let fin_k = Expr::app(h.fin.clone(), k.clone());
    let mut d = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = d.fresh_local(fin_k.clone());
    let body = Expr::app(
        h.rat_neg.clone(),
        Expr::app(h.rat_abs.clone(), Expr::app(gens_i.clone(), j)),
    );
    d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k, body))
}

/// `fun (j : Fin k) => upper_summand (G i j) (ε j) (hbound j)
///   : Rat.mul (G i j)(ε j) ≤ Rat.abs (G i j)`.
fn pointwise_upper(
    h: &T12Consts,
    parent: &EnvDeclBuilder,
    k: &Expr,
    gens_i: &Expr,
    eps: &Expr,
    hbound: &Expr,
) -> Expr {
    let fin_k = Expr::app(h.fin.clone(), k.clone());
    let mut d = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = d.fresh_local(fin_k.clone());
    let g = Expr::app(gens_i.clone(), j.clone());
    let e = Expr::app(eps.clone(), j.clone());
    let hbound_j = Expr::app(hbound.clone(), j);
    let body = h.summand.upper_summand(&d, g, e, hbound_j);
    d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k, body))
}

/// `fun (j : Fin k) => lower_summand (G i j) (ε j) (hbound j)
///   : Rat.neg (Rat.abs (G i j)) ≤ Rat.mul (G i j)(ε j)`.
fn pointwise_lower(
    h: &T12Consts,
    parent: &EnvDeclBuilder,
    k: &Expr,
    gens_i: &Expr,
    eps: &Expr,
    hbound: &Expr,
) -> Expr {
    let fin_k = Expr::app(h.fin.clone(), k.clone());
    let mut d = EnvDeclBuilder::child_of(parent);
    let (j_id, j) = d.fresh_local(fin_k.clone());
    let g = Expr::app(gens_i.clone(), j.clone());
    let e = Expr::app(eps.clone(), j.clone());
    let hbound_j = Expr::app(hbound.clone(), j);
    let body = h.summand.lower_summand(&d, g, e, hbound_j);
    d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k, body))
}

/// Transport `h_le : Rat.le a rhs` to `Rat.le b rhs` along `h_eq : a = b`.
fn transport_le_lhs(
    h: &T12Consts,
    parent: &EnvDeclBuilder,
    rhs: Expr,
    a: Expr,
    b: Expr,
    h_le: Expr,
    h_eq: Expr,
) -> Expr {
    let motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = d.fresh_local(h.rat.clone());
        let body = h.rat_le_pub(x, rhs.clone());
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, h.rat.clone(), body))
    };
    Expr::apps(
        h.eq_subst.clone(),
        [h.rat.clone(), motive, a, b, h_eq, h_le],
    )
}
