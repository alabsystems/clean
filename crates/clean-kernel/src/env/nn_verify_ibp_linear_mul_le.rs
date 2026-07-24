// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T3 (#3490, #3476): Constructive proof term for `NNVerify.mul_nonneg_le_left`.
//!
//! Promotes `mul_nonneg_le_left` from sorry-inhabited `Declaration::Opaque`
//! to a constructive `Declaration::Theorem`. The proof uses only the
//! foundational ordered-field axiom `Rat.mul_nonneg` plus the field→order
//! bridging lemmas from `nn_verify_rat_ordering` (#3503):
//!
//! * `Rat.sub_nonneg_of_le` — `a ≤ b → 0 ≤ b - a`
//! * `Rat.mul_sub`          — `a * (b - c) = a*b - a*c`
//! * `Rat.le_of_sub_nonneg` — `0 ≤ b - a → a ≤ b`
//!
//! ## Proof chain
//!
//! Given `w a b : Rat`, `h_w_nn : 0 ≤ w`, `h_ab : a ≤ b`:
//!
//! 1. `h_ba_nn : 0 ≤ b - a`            — `Rat.sub_nonneg_of_le a b h_ab`
//! 2. `h_prod_nn : 0 ≤ w * (b - a)`    — `Rat.mul_nonneg w (b - a) h_w_nn h_ba_nn`
//! 3. `h_dist : w * (b - a) = w*b - w*a` — `Rat.mul_sub w b a`
//! 4. `h_wbwa_nn : 0 ≤ w*b - w*a`      — `Eq.subst` with motive `λ x, 0 ≤ x`
//!                                        transporting `h_prod_nn` along `h_dist`
//! 5. `w*a ≤ w*b`                      — `Rat.le_of_sub_nonneg (w*a) (w*b) h_wbwa_nn`
//!
//! Split into its own module to keep `nn_verify_ibp_linear.rs` under the
//! 500-line limit and match the existing `nn_verify_ibp_linear_transport.rs`
//! pattern for T2 (#3490).
//!
//! ## Closure impact
//!
//! The C008 `ibp_tightness_bound_inductive` closure does NOT reference
//! `mul_nonneg_le_left` directly, so this promotion has no effect on the
//! C008 ratchet. The `ibp_linear_sound` closure (T80 theorem) gains
//! `Rat.mul_nonneg`, `Rat.mul_sub`, `Rat.sub_nonneg_of_le`,
//! `Rat.le_of_sub_nonneg`, `Rat.add_neg_self`, `Rat.mul_neg`,
//! `Rat.add_zero`, `Rat.add_comm`, `Rat.add_assoc`, `Rat.zero_add`,
//! `Rat.add_left_neg`, `Rat.add_le_add_left`, `Rat.left_distrib` —
//! all honest ordered-field axioms — and LOSES `sorry` (through this
//! lemma; other opaques still contain sorry so the global closure keeps
//! it until those are also promoted).
//!
//! Part of #3490 T3 / blocker #3503 landed.

use super::decl_builder::EnvDeclBuilder;
use super::nn_verify_ibp_linear::IbpLinearConsts;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// `Eq.subst.{1} @Rat motive @a @b h_eq h_motive_a` for α = Rat.
///
/// Produces `motive b` from `h_eq : Eq a b` and `h_motive_a : motive a`.
fn eq_subst_rat(
    c: &IbpLinearConsts,
    motive: Expr,
    a: Expr,
    b: Expr,
    h_eq: Expr,
    h_motive_a: Expr,
) -> Expr {
    let eq_subst = Expr::const_(
        Name::from_string("Eq.subst"),
        vec![Level::succ(Level::zero())],
    );
    Expr::apps(eq_subst, [c.rat.clone(), motive, a, b, h_eq, h_motive_a])
}

/// Build the constructive proof term for `NNVerify.mul_nonneg_le_left`.
///
/// Shape:
/// ```text
/// fun (w a b : Rat) (h_w_nn : 0 ≤ w) (h_ab : a ≤ b) =>
///   let h_ba_nn   := @Rat.sub_nonneg_of_le a b h_ab
///   let h_prod_nn := @Rat.mul_nonneg w (Rat.sub b a) h_w_nn h_ba_nn
///   let h_dist    := @Rat.mul_sub w b a
///   let h_wbwa_nn :=
///     @Eq.subst.{1} Rat
///       (fun x => Rat.le 0 x)
///       (Rat.mul w (Rat.sub b a))
///       (Rat.sub (Rat.mul w b) (Rat.mul w a))
///       h_dist h_prod_nn
///   @Rat.le_of_sub_nonneg (Rat.mul w a) (Rat.mul w b) h_wbwa_nn
/// ```
pub(super) fn build_mul_nonneg_le_left_proof(c: &IbpLinearConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (w_id, w) = b.fresh_local(c.rat.clone());
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());

    let h_w_nn_ty = c.rat_le(c.rat_zero.clone(), w.clone());
    let h_ab_ty = c.rat_le(a.clone(), bv.clone());
    let (h_w_id, h_w) = b.fresh_local(h_w_nn_ty.clone());
    let (h_ab_id, h_ab) = b.fresh_local(h_ab_ty.clone());

    // Expressions we'll reuse.
    let b_sub_a = {
        let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
        Expr::apps(rat_sub, [bv.clone(), a.clone()])
    };
    let w_times_bsa = c.mul(w.clone(), b_sub_a.clone());
    let wb = c.mul(w.clone(), bv.clone());
    let wa = c.mul(w.clone(), a.clone());
    let wb_sub_wa = {
        let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
        Expr::apps(rat_sub, [wb.clone(), wa.clone()])
    };

    // 1. h_ba_nn : Rat.le 0 (b - a)  via  @Rat.sub_nonneg_of_le a b h_ab
    let sub_nonneg_of_le = Expr::const_(Name::from_string("Rat.sub_nonneg_of_le"), vec![]);
    let h_ba_nn = Expr::apps(sub_nonneg_of_le, [a.clone(), bv.clone(), h_ab]);

    // 2. h_prod_nn : Rat.le 0 (w * (b - a))
    //    via  @Rat.mul_nonneg w (b - a) h_w_nn h_ba_nn
    let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
    let h_prod_nn = Expr::apps(mul_nonneg, [w.clone(), b_sub_a.clone(), h_w, h_ba_nn]);

    // 3. h_dist : w * (b - a) = w*b - w*a  via  @Rat.mul_sub w b a
    let mul_sub = Expr::const_(Name::from_string("Rat.mul_sub"), vec![]);
    let h_dist = Expr::apps(mul_sub, [w.clone(), bv.clone(), a.clone()]);

    // 4. motive : Rat → Prop = fun x => Rat.le 0 x
    let motive = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(c.rat_zero.clone(), x);
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    // Eq.subst motive (w*(b-a)) (w*b - w*a) h_dist h_prod_nn
    //   : motive (w*b - w*a) = Rat.le 0 (w*b - w*a)
    let h_wbwa_nn = eq_subst_rat(c, motive, w_times_bsa, wb_sub_wa, h_dist, h_prod_nn);

    // 5. @Rat.le_of_sub_nonneg (w*a) (w*b) h_wbwa_nn : Rat.le (w*a) (w*b)
    let le_of_sub_nonneg = Expr::const_(Name::from_string("Rat.le_of_sub_nonneg"), vec![]);
    let body = Expr::apps(le_of_sub_nonneg, [wa, wb, h_wbwa_nn]);

    let e = b.mk_lam(h_ab_id, BinderInfo::Default, h_ab_ty, body);
    let e = b.mk_lam(h_w_id, BinderInfo::Default, h_w_nn_ty, e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}
