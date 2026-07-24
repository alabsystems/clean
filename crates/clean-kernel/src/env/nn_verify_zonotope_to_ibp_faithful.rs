// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Faithful `NNVerify.Zonotope.to_ibp` body + its constructive `valid` proof.
//!
//! Replaces the historical FAKE zero-interval carrier (`fun n k _z =>
//! IntervalBounds.mk n (fun _=>0)(fun _=>0)(fun _=> Rat.le_refl 0)`) with the
//! mathematically faithful element-wise range
//!
//! ```text
//! radius_i = Fin.sum k (fun j => Rat.abs (z.generators i j))
//! lower_i  = Rat.sub (z.center i) radius_i
//! upper_i  = Rat.add (z.center i) radius_i
//! ```
//!
//! and a REAL `valid : ∀ i, lower_i ≤ upper_i` proof: `radius_i ≥ 0` (every
//! summand is `Rat.abs … ≥ 0` via `Rat.abs_nonneg`, lifted by
//! `Fin.sum_nonneg`), so `center_i - radius_i ≤ center_i ≤ center_i + radius_i`.
//!
//! The `valid` proof needs only `Rat.abs_nonneg`, `Fin.sum_nonneg`,
//! `Rat.le_add_of_nonneg_right` (`a ≤ a + nonneg`), `Rat.add_le_add_left`
//! (monotone left-add), and `Rat.le_trans` — all present in BOTH the default
//! and the overlays build (as honest axioms or constructive theorems over the
//! sound carrier), so the faithful body type-checks unconditionally.
//!
//! Mirrors the `valid`-proof construction technique of
//! `nn_verify_ibp_linear_define::build_ibp_linear_bounds_value`.

use super::nn_verify_zonotope::ZonotopeConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached constants for the faithful `to_ibp` body + its `valid` proof.
pub(super) struct ToIbpConsts {
    pub(super) ib_mk: Expr,
    pub(super) rat_abs: Expr,
    pub(super) rat_add: Expr,
    pub(super) rat_sub: Expr,
    pub(super) fin_sum: Expr,
    pub(super) abs_nonneg: Expr,
    pub(super) fin_sum_nonneg: Expr,
    pub(super) le_add_of_nonneg_right: Expr,
    pub(super) add_le_add_left: Expr,
    pub(super) le_trans: Expr,
}

impl ToIbpConsts {
    pub(super) fn new() -> Self {
        let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            ib_mk: c("NNVerify.IntervalBounds.mk"),
            rat_abs: c("Rat.abs"),
            rat_add: c("Rat.add"),
            rat_sub: c("Rat.sub"),
            fin_sum: c("Fin.sum"),
            abs_nonneg: c("Rat.abs_nonneg"),
            fin_sum_nonneg: c("Fin.sum_nonneg"),
            le_add_of_nonneg_right: c("Rat.le_add_of_nonneg_right"),
            add_le_add_left: c("Rat.add_le_add_left"),
            le_trans: c("Rat.le_trans"),
        }
    }

    /// `radius i := Fin.sum k (fun (j : Fin k) => Rat.abs (gens i j))`.
    fn radius(&self, parent: &EnvDeclBuilder, fin_k: &Expr, k: &Expr, gens_i: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let (j_id, j) = ch.fresh_local(fin_k.clone());
        let gij = Expr::app(gens_i.clone(), j);
        let body = Expr::app(self.rat_abs.clone(), gij);
        let summand = ch.finish_child(ch.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body));
        Expr::apps(self.fin_sum.clone(), [k.clone(), summand])
    }
}

/// Build the faithful `to_ibp` value:
/// `fun (n k : Nat) (z : Zonotope n k) =>
///    IntervalBounds.mk n lower upper valid`.
pub(super) fn build_to_ibp_value(c: &ZonotopeConsts) -> Expr {
    let h = ToIbpConsts::new();
    let zono_name = Name::from_string("NNVerify.Zonotope");

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let zono_nk = c.zono_of(n.clone(), k.clone());
    let (z_id, z) = b.fresh_local(zono_nk.clone());

    let fin_n = Expr::app(c.fin.clone(), n.clone());
    let fin_k = Expr::app(c.fin.clone(), k.clone());
    let center = Expr::proj(zono_name.clone(), 0, z.clone());
    let gens = Expr::proj(zono_name.clone(), 1, z);

    // lower : NNVec n := fun i => Rat.sub (center i) (radius i).
    let lower_fn = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let gens_i = Expr::app(gens.clone(), i.clone());
        let center_i = Expr::app(center.clone(), i.clone());
        let radius = h.radius(&ch, &fin_k, &k, &gens_i);
        let body = Expr::apps(h.rat_sub.clone(), [center_i, radius]);
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), body))
    };
    // upper : NNVec n := fun i => Rat.add (center i) (radius i).
    let upper_fn = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let gens_i = Expr::app(gens.clone(), i.clone());
        let center_i = Expr::app(center.clone(), i.clone());
        let radius = h.radius(&ch, &fin_k, &k, &gens_i);
        let body = Expr::apps(h.rat_add.clone(), [center_i, radius]);
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), body))
    };
    // valid : ∀ (i : Fin n), lower i ≤ upper i.
    let valid_fn = build_to_ibp_valid(c, &h, &b, &fin_n, &fin_k, &k, &center, &gens);

    let result = Expr::apps(h.ib_mk.clone(), [n.clone(), lower_fn, upper_fn, valid_fn]);
    let e = b.mk_lam(z_id, BinderInfo::Default, zono_nk, result);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `valid : ∀ (i : Fin n), Rat.sub (center i)(radius i) ≤ Rat.add (center i)(radius i)`.
///
/// Per `i`: let `r := radius i`, `ci := center i`.
/// - `h_rnn : 0 ≤ r`              via `Fin.sum_nonneg k absrow (fun j => Rat.abs_nonneg (gens i j))`.
/// - `h_up  : ci ≤ ci + r`        via `Rat.le_add_of_nonneg_right ci r h_rnn`.
/// - `h_lo  : ci - r ≤ ci`        via `Rat.add_le_add_left (-r) 0 h_neg ci` retyped
///   — instead we go through the `ci - r ≤ ci ≤ ci + r` chain using `le_trans`.
///   For `ci - r ≤ ci` we reuse `le_add_of_nonneg_right` on `-? ` is awkward, so we
///   build it directly: `Rat.sub ci r ≡ Rat.add ci (Rat.neg r)`, and
///   `Rat.add ci (Rat.neg r) ≤ Rat.add ci 0` by `add_le_add_left (Rat.neg r) 0 h_neg_r_le_0 ci`,
///   with `Rat.add ci 0 ≡ ci`. Then `le_trans` with `h_up`.
#[allow(clippy::too_many_arguments)]
fn build_to_ibp_valid(
    c: &ZonotopeConsts,
    h: &ToIbpConsts,
    parent: &EnvDeclBuilder,
    fin_n: &Expr,
    fin_k: &Expr,
    k: &Expr,
    center: &Expr,
    gens: &Expr,
) -> Expr {
    let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
    let rat_neg = c.rat_neg.clone();

    let mut ch = EnvDeclBuilder::child_of(parent);
    let (i_id, i) = ch.fresh_local(fin_n.clone());
    let gens_i = Expr::app(gens.clone(), i.clone());
    let center_i = Expr::app(center.clone(), i.clone());
    let radius = h.radius(&ch, fin_k, k, &gens_i);

    // absrow : Fin k → Rat := fun j => Rat.abs (gens i j).
    let absrow = {
        let mut d = EnvDeclBuilder::child_of(&ch);
        let (j_id, j) = d.fresh_local(fin_k.clone());
        let body = Expr::app(h.rat_abs.clone(), Expr::app(gens_i.clone(), j));
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    // pointwise : ∀ j, 0 ≤ Rat.abs (gens i j)  via Rat.abs_nonneg (gens i j).
    let pointwise = {
        let mut d = EnvDeclBuilder::child_of(&ch);
        let (j_id, j) = d.fresh_local(fin_k.clone());
        let body = Expr::app(h.abs_nonneg.clone(), Expr::app(gens_i.clone(), j));
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_k.clone(), body))
    };
    // h_rnn : 0 ≤ radius i.
    let h_rnn = Expr::apps(h.fin_sum_nonneg.clone(), [k.clone(), absrow, pointwise]);

    // h_up : center i ≤ Rat.add (center i)(radius i).
    let h_up = Expr::apps(
        h.le_add_of_nonneg_right.clone(),
        [center_i.clone(), radius.clone(), h_rnn.clone()],
    );

    // h_neg_le : Rat.neg (radius i) ≤ 0  via Rat.neg_le_neg-free route:
    //   `Rat.neg_le_neg 0 (radius i) h_rnn : Rat.neg (radius i) ≤ Rat.neg 0`,
    //   and `Rat.neg 0 ≡ 0` (def-eq via the live quotient carrier), so it
    //   retypes at `Rat.neg (radius i) ≤ 0`.
    let neg_le_neg = Expr::const_(Name::from_string("Rat.neg_le_neg"), vec![]);
    let h_neg_le = Expr::apps(neg_le_neg, [rat_zero.clone(), radius.clone(), h_rnn]);

    // h_lo_pre : Rat.add (center i)(Rat.neg (radius i)) ≤ Rat.add (center i) 0
    //   via Rat.add_le_add_left (Rat.neg (radius i)) 0 h_neg_le (center i).
    // `Rat.add (center i) 0 ≡ center i` (Rat.add_zero is def-eq? no — use le_trans
    // against h_up whose LHS is center i; bridge via `Rat.add_zero`).
    let neg_r = Expr::app(rat_neg, radius.clone());
    let h_lo_pre = Expr::apps(
        h.add_le_add_left.clone(),
        [neg_r.clone(), rat_zero.clone(), h_neg_le, center_i.clone()],
    );
    // `Rat.sub (center i)(radius i) ≡ Rat.add (center i)(Rat.neg (radius i))`
    // definitionally, so `h_lo_pre : (center i - radius i) ≤ Rat.add (center i) 0`.
    // Bridge `Rat.add (center i) 0 = center i` via `Rat.add_zero (center i)`,
    // transporting the RHS of h_lo_pre with Eq.subst.
    let add_zero = Expr::const_(Name::from_string("Rat.add_zero"), vec![]);
    let h_addzero = Expr::app(add_zero, center_i.clone());
    let sub_ci_r = Expr::apps(h.rat_sub.clone(), [center_i.clone(), radius.clone()]);
    let add_ci_0 = Expr::apps(h.rat_add.clone(), [center_i.clone(), rat_zero.clone()]);
    let h_lo = transport_le_rhs(
        &ch,
        sub_ci_r.clone(),
        add_ci_0,
        center_i.clone(),
        h_lo_pre,
        h_addzero,
    );

    // valid_i : (center i - radius i) ≤ Rat.add (center i)(radius i)
    //   via le_trans (center i - radius i) (center i) (center i + radius i) h_lo h_up.
    let upper_i = Expr::apps(h.rat_add.clone(), [center_i.clone(), radius]);
    let valid_i = Expr::apps(
        h.le_trans.clone(),
        [sub_ci_r, center_i, upper_i, h_lo, h_up],
    );
    ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n.clone(), valid_i))
}

/// Transport `h : Rat.le lhs a` to `Rat.le lhs b` along `h_eq : a = b`.
///
/// `@Eq.subst.{1} Rat (fun x => LE.le @Rat instLERat lhs x) a b h_eq h`.
/// `lhs` may reference parent FVars, so the motive lambda is built with a
/// `child_of` builder (it owns only its own `x`).
fn transport_le_rhs(
    parent: &EnvDeclBuilder,
    lhs: Expr,
    a: Expr,
    b: Expr,
    h: Expr,
    h_eq: Expr,
) -> Expr {
    let rat = Expr::const_(Name::from_string("Rat"), vec![]);
    let le_le = Expr::const_(
        Name::from_string("LE.le"),
        vec![crate::level::Level::zero()],
    );
    let inst = Expr::const_(Name::from_string("instLERat"), vec![]);
    let eq_subst = Expr::const_(
        Name::from_string("Eq.subst"),
        vec![crate::level::Level::succ(crate::level::Level::zero())],
    );
    // motive : Rat → Prop := fun x => LE.le @Rat instLERat lhs x.
    let motive = {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = d.fresh_local(rat.clone());
        let body = Expr::apps(le_le, [rat.clone(), inst, lhs, x]);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, rat.clone(), body))
    };
    Expr::apps(eq_subst, [rat, motive, a, b, h_eq, h])
}
