// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! T (#3490, Batch 0 final): Constructive proof term for
//! `NNVerify.mul_nonpos_le_left`.
//!
//! Promotes `mul_nonpos_le_left` from sorry-inhabited `Declaration::Opaque`
//! to a constructive `Declaration::Theorem`. Closes the last
//! `sorry_inhabit_pi` registration in `nn_verify_ibp_linear.rs`.
//!
//! Statement:
//! `∀ (w a b : Rat), w ≤ 0 → a ≤ b → w*b ≤ w*a`.
//!
//! ## Axioms used (all pre-existing, no new axioms)
//!
//! Foundational (ordered-field axioms + Rat instances):
//! * `Rat.add_le_add_left`   (`∀ a b, a ≤ b → ∀ c, c+a ≤ c+b`)
//! * `Rat.add_left_neg`      (`(-a) + a = 0`)
//! * `Rat.add_neg_self`      (`a + (-a) = 0`)
//! * `Rat.add_zero`          (`a + 0 = a`)
//! * `Rat.add_comm`          (`a + b = b + a`)
//! * `Rat.add_right_cancel`  (`a + b = c + b → a = c`)
//! * `Rat.mul_nonneg`        (`0 ≤ a → 0 ≤ b → 0 ≤ a*b`)
//! * `Rat.mul_sub`           (`a*(b - c) = a*b - a*c`)
//! * `Rat.mul_neg`           (`a*(-b) = -(a*b)`)
//! * `Rat.mul_comm`          (`a*b = b*a`)
//! * `Rat.sub_nonneg_of_le`  (`a ≤ b → 0 ≤ b - a`)
//! * `Rat.le_of_sub_nonneg`  (`0 ≤ b - a → a ≤ b`)
//!
//! Kernel primitives: `Eq.subst`, `Eq.trans`, `Eq.symm`, `Eq.refl`, `congrArg`.
//!
//! Sibling theorems used:
//! * `NNVerify.mul_nonneg_le_left` (sorry-free Theorem from #3490 T3)
//!
//! ## Proof outline
//!
//! Given `w a b : Rat`, `h_w_np : w ≤ 0`, `h_ab : a ≤ b`:
//!
//! 1. Prove `h_neg_w_nn : 0 ≤ -w` from `h_w_np`:
//!    * `k1 : (-w) + w ≤ (-w) + 0` via `add_le_add_left w 0 h_w_np (-w)`.
//!    * Rewrite LHS with `add_left_neg w : (-w) + w = 0`, RHS with
//!      `add_zero (-w) : (-w) + 0 = -w` via two `Eq.subst` calls.
//!
//! 2. Apply sibling theorem:
//!    `ih : (-w)*a ≤ (-w)*b` := `NNVerify.mul_nonneg_le_left (-w) a b h_neg_w_nn h_ab`.
//!
//! 3. From `ih`, derive `0 ≤ (-w)*b - (-w)*a` via `sub_nonneg_of_le`.
//!
//! 4. Prove `(-w)*b - (-w)*a = w*a - w*b` via algebraic chain.
//!    Both sides unfold by `Rat.sub` delta to `add`/`neg` form:
//!    * LHS: `(-w)*b + (-((-w)*a))`
//!    * RHS: `w*a + (-(w*b))`
//!
//!    Sub-lemmas (proved inline):
//!    * `neg_w_mul_x_eq x : (-w)*x = -(w*x)` for each `x ∈ {a, b}`,
//!      composed from `mul_comm`, `mul_neg`, and `congrArg Rat.neg (mul_comm …)`.
//!    * `neg_neg_rat y : -(-y) = y`, proved via `add_left_neg (-y)`,
//!      `add_neg_self y`, and `add_right_cancel`.
//!
//!    Using these, rewrite both operands of LHS to cancel the double-negs
//!    and compose `add_comm` to match RHS.
//!
//! 5. Transport `0 ≤ (-w)*b - (-w)*a` along the equality from step 4 via
//!    `Eq.subst` with motive `λ x, 0 ≤ x` → `0 ≤ w*a - w*b`.
//!
//! 6. Apply `Rat.le_of_sub_nonneg (w*b) (w*a)` to obtain `w*b ≤ w*a`. QED.
//!
//! ## Closure impact
//!
//! The transitive axiom closure gains (beyond the sibling's closure):
//! `Rat.add_right_cancel`, `Rat.mul_comm`, `congrArg` — all honest. No
//! `sorry` in the transitive closure. This removes the LAST
//! `sorry_inhabit_pi` call-site in `nn_verify_ibp_linear.rs`.
//!
//! Part of #3490 Batch 0 final / #3476.

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

/// `Eq.trans.{1} @Rat @a @b @c h1 h2`.
fn eq_trans_rat(c: &IbpLinearConsts, a: Expr, b: Expr, d: Expr, h1: Expr, h2: Expr) -> Expr {
    let eq_trans = Expr::const_(
        Name::from_string("Eq.trans"),
        vec![Level::succ(Level::zero())],
    );
    Expr::apps(eq_trans, [c.rat.clone(), a, b, d, h1, h2])
}

/// `@congrArg.{1, 1} Rat Rat a b f h : Eq Rat (f a) (f b)`.
fn congr_arg_rat_rat(c: &IbpLinearConsts, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
    let one = Level::succ(Level::zero());
    let congr_arg = Expr::const_(Name::from_string("congrArg"), vec![one.clone(), one]);
    Expr::apps(congr_arg, [c.rat.clone(), c.rat.clone(), a, b, f, h])
}

/// `Rat.neg` constant.
fn rat_neg(_c: &IbpLinearConsts) -> Expr {
    Expr::const_(Name::from_string("Rat.neg"), vec![])
}

/// Build `neg x := Rat.neg x`.
fn neg(c: &IbpLinearConsts, x: Expr) -> Expr {
    Expr::app(rat_neg(c), x)
}

/// Build the constructive proof term for `NNVerify.mul_nonpos_le_left`:
/// `∀ w a b : Rat, w ≤ 0 → a ≤ b → w*b ≤ w*a`.
pub(super) fn build_mul_nonpos_le_left_proof(c: &IbpLinearConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (w_id, w) = b.fresh_local(c.rat.clone());
    let (a_id, a) = b.fresh_local(c.rat.clone());
    let (bv_id, bv) = b.fresh_local(c.rat.clone());

    let h_w_np_ty = c.rat_le(w.clone(), c.rat_zero.clone());
    let h_ab_ty = c.rat_le(a.clone(), bv.clone());
    let (h_w_id, h_w) = b.fresh_local(h_w_np_ty.clone());
    let (h_ab_id, h_ab) = b.fresh_local(h_ab_ty.clone());

    // Common subexpressions.
    let neg_w = neg(c, w.clone());
    let wa = c.mul(w.clone(), a.clone());
    let wb = c.mul(w.clone(), bv.clone());
    let neg_w_a = c.mul(neg_w.clone(), a.clone());
    let neg_w_b = c.mul(neg_w.clone(), bv.clone());
    let neg_wa = neg(c, wa.clone());
    let neg_wb = neg(c, wb.clone());
    let neg_neg_wa = neg(c, neg_wa.clone());

    // =========================================================
    // Step 1: h_neg_w_nn : 0 ≤ -w.
    // =========================================================
    // k1 : (-w) + w ≤ (-w) + 0  via  Rat.add_le_add_left w 0 h_w (-w).
    let add_le_add_left = Expr::const_(Name::from_string("Rat.add_le_add_left"), vec![]);
    let k1 = Expr::apps(
        add_le_add_left.clone(),
        [w.clone(), c.rat_zero.clone(), h_w, neg_w.clone()],
    );

    // e1 : (-w) + w = 0  via  Rat.add_left_neg w.
    let add_left_neg = Expr::const_(Name::from_string("Rat.add_left_neg"), vec![]);
    let e1 = Expr::app(add_left_neg, w.clone());

    // motive_k1 : fun x => x ≤ (-w) + 0
    let neg_w_plus_zero = c.add(neg_w.clone(), c.rat_zero.clone());
    let neg_w_plus_w = c.add(neg_w.clone(), w.clone());
    let motive_k1 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(x, neg_w_plus_zero.clone());
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    // k2 : 0 ≤ (-w) + 0
    let k2 = eq_subst_rat(c, motive_k1, neg_w_plus_w, c.rat_zero.clone(), e1, k1);

    // e2 : (-w) + 0 = -w  via  Rat.add_zero (-w).
    let add_zero = Expr::const_(Name::from_string("Rat.add_zero"), vec![]);
    let e2 = Expr::app(add_zero, neg_w.clone());

    // motive_k2 : fun x => 0 ≤ x
    let motive_k2 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(c.rat_zero.clone(), x);
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    // h_neg_w_nn : 0 ≤ -w
    let h_neg_w_nn = eq_subst_rat(c, motive_k2, neg_w_plus_zero, neg_w.clone(), e2, k2);

    // =========================================================
    // Step 2: ih : (-w)*a ≤ (-w)*b  via sibling `NNVerify.mul_nonneg_le_left`.
    // =========================================================
    let mul_nonneg_le_left = Expr::const_(Name::from_string("NNVerify.mul_nonneg_le_left"), vec![]);
    let ih = Expr::apps(
        mul_nonneg_le_left,
        [neg_w.clone(), a.clone(), bv.clone(), h_neg_w_nn, h_ab],
    );

    // =========================================================
    // Step 3: h_sub_nn : 0 ≤ (-w)*b - (-w)*a  via Rat.sub_nonneg_of_le.
    // =========================================================
    let sub_nonneg_of_le = Expr::const_(Name::from_string("Rat.sub_nonneg_of_le"), vec![]);
    let h_sub_nn = Expr::apps(sub_nonneg_of_le, [neg_w_a.clone(), neg_w_b.clone(), ih]);
    // h_sub_nn has type `0 ≤ Rat.sub ((-w)*b) ((-w)*a)`, which by delta on
    // Rat.sub is `0 ≤ (-w)*b + (-((-w)*a))`.

    // =========================================================
    // Step 4: prove eq_chain : (-w)*b + (-((-w)*a)) = w*a + (-(w*b)).
    // =========================================================
    //
    // Sub-step 4a: ident_b : (-w)*b = -(w*b).
    //   Chain: (-w)*b = b*(-w) = -(b*w) = -(w*b).
    let mul_comm = Expr::const_(Name::from_string("Rat.mul_comm"), vec![]);
    let mul_neg = Expr::const_(Name::from_string("Rat.mul_neg"), vec![]);
    let b_times_w = c.mul(bv.clone(), w.clone());
    let b_times_neg_w = c.mul(bv.clone(), neg_w.clone());
    let neg_b_times_w = neg(c, b_times_w.clone());
    // e_b1 : (-w)*b = b*(-w)
    let e_b1 = Expr::apps(mul_comm.clone(), [neg_w.clone(), bv.clone()]);
    // e_b2 : b*(-w) = -(b*w)
    let e_b2 = Expr::apps(mul_neg.clone(), [bv.clone(), w.clone()]);
    // e_b3a : b*w = w*b
    let e_b3a = Expr::apps(mul_comm.clone(), [bv.clone(), w.clone()]);
    // e_b3 : -(b*w) = -(w*b)  via congrArg neg e_b3a
    let e_b3 = congr_arg_rat_rat(c, b_times_w.clone(), wb.clone(), rat_neg(c), e_b3a);
    // ident_b : (-w)*b = -(w*b) via Eq.trans (e_b1 · e_b2) · e_b3
    let t_b_1 = eq_trans_rat(
        c,
        neg_w_b.clone(),
        b_times_neg_w.clone(),
        neg_b_times_w.clone(),
        e_b1,
        e_b2,
    );
    let ident_b = eq_trans_rat(
        c,
        neg_w_b.clone(),
        neg_b_times_w,
        neg_wb.clone(),
        t_b_1,
        e_b3,
    );

    // Sub-step 4a': ident_a : (-w)*a = -(w*a).  Mirror of ident_b.
    let a_times_w = c.mul(a.clone(), w.clone());
    let a_times_neg_w = c.mul(a.clone(), neg_w.clone());
    let neg_a_times_w = neg(c, a_times_w.clone());
    let e_a1 = Expr::apps(mul_comm.clone(), [neg_w.clone(), a.clone()]);
    let e_a2 = Expr::apps(mul_neg, [a.clone(), w.clone()]);
    let e_a3a = Expr::apps(mul_comm.clone(), [a.clone(), w.clone()]);
    let e_a3 = congr_arg_rat_rat(c, a_times_w.clone(), wa.clone(), rat_neg(c), e_a3a);
    let t_a_1 = eq_trans_rat(
        c,
        neg_w_a.clone(),
        a_times_neg_w.clone(),
        neg_a_times_w.clone(),
        e_a1,
        e_a2,
    );
    let ident_a = eq_trans_rat(
        c,
        neg_w_a.clone(),
        neg_a_times_w,
        neg_wa.clone(),
        t_a_1,
        e_a3,
    );

    // Sub-step 4b: neg_neg_wa : -(-(w*a)) = w*a.
    //   Proved inline via:
    //     h_lneg : (-(-(w*a))) + (-(w*a)) = 0   from Rat.add_left_neg (-(w*a))
    //     h_rneg : (w*a) + (-(w*a)) = 0         from Rat.add_neg_self (w*a)
    //     combine via Eq.trans (. · Eq.symm h_rneg) to get
    //          (-(-(w*a))) + (-(w*a)) = (w*a) + (-(w*a))
    //     then Rat.add_right_cancel: -(-(w*a)) = w*a.
    let add_left_neg_c = Expr::const_(Name::from_string("Rat.add_left_neg"), vec![]);
    let add_neg_self = Expr::const_(Name::from_string("Rat.add_neg_self"), vec![]);
    let add_right_cancel = Expr::const_(Name::from_string("Rat.add_right_cancel"), vec![]);
    let eq_symm = Expr::const_(
        Name::from_string("Eq.symm"),
        vec![Level::succ(Level::zero())],
    );
    // lhs_sum : (-(-(w*a))) + (-(w*a))
    let lhs_sum = c.add(neg_neg_wa.clone(), neg_wa.clone());
    // rhs_sum : (w*a) + (-(w*a))
    let rhs_sum = c.add(wa.clone(), neg_wa.clone());
    // h_lneg : (-(-(w*a))) + (-(w*a)) = 0  via  Rat.add_left_neg (-(w*a))
    let h_lneg = Expr::app(add_left_neg_c, neg_wa.clone());
    // h_rneg : (w*a) + (-(w*a)) = 0  via  Rat.add_neg_self (w*a)
    let h_rneg = Expr::app(add_neg_self, wa.clone());
    // h_rneg_sym : 0 = (w*a) + (-(w*a))
    let h_rneg_sym = Expr::apps(
        eq_symm.clone(),
        [c.rat.clone(), rhs_sum.clone(), c.rat_zero.clone(), h_rneg],
    );
    // Note: Eq.symm : ∀ {α} {a b : α}, a = b → b = a. With `h_rneg : (w*a) + (-(w*a)) = 0`,
    // symm yields `0 = (w*a) + (-(w*a))`. Arguments above are `a = rhs_sum`, `b = 0`.
    // h_combine : (-(-(w*a))) + (-(w*a)) = (w*a) + (-(w*a))
    let h_combine = eq_trans_rat(c, lhs_sum, c.rat_zero.clone(), rhs_sum, h_lneg, h_rneg_sym);
    // neg_neg_wa_eq : -(-(w*a)) = w*a
    let neg_neg_wa_eq = Expr::apps(
        add_right_cancel,
        [neg_neg_wa.clone(), neg_wa.clone(), wa.clone(), h_combine],
    );

    // Sub-step 4c: assemble full chain
    //   LHS_full = (-w)*b + (-((-w)*a))
    //   RHS_full = w*a + (-(w*b))
    //
    // Rewrite LHS_full step by step via Eq.subst:
    //   (i)   Use ident_b to rewrite (-w)*b → -(w*b):
    //         motive_i = λ x, x + (-((-w)*a))
    //         from refl (LHS_full), produce  -(w*b) + (-((-w)*a))
    //   (ii)  Use congrArg Rat.neg ident_a : -((-w)*a) = -(-(w*a))
    //         motive_ii = λ y, -(w*b) + y
    //         produce  -(w*b) + -(-(w*a))
    //   (iii) Use neg_neg_wa_eq : -(-(w*a)) = w*a
    //         motive_iii = λ z, -(w*b) + z
    //         produce  -(w*b) + (w*a)
    //   (iv)  Use add_comm to flip to w*a + -(w*b) = RHS_full.

    // lhs_full : (-w)*b + (-((-w)*a))
    let lhs_full = c.add(neg_w_b.clone(), neg(c, neg_w_a.clone()));
    // refl_lhs_full : lhs_full = lhs_full
    let eq_refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    let _refl_lhs_full = Expr::apps(eq_refl.clone(), [c.rat.clone(), lhs_full.clone()]);

    // We'll build the equality chain for `lhs_full = rhs_full` via four Eq.trans
    // steps over the concrete intermediate forms below.
    //
    // Intermediate forms (call these s0..s4, each an Expr):
    //   s0 = (-w)*b + (-((-w)*a))           = lhs_full
    //   s1 = -(w*b) + (-((-w)*a))
    //   s2 = -(w*b) + (-(-(w*a)))
    //   s3 = -(w*b) + (w*a)
    //   s4 = w*a + -(w*b)                    = rhs_full
    //
    // We build:
    //   p01 : s0 = s1  via congrArg (λ x, x + (-((-w)*a))) ident_b
    //   p12 : s1 = s2  via congrArg (λ y, -(w*b) + y) (congrArg Rat.neg ident_a)
    //   p23 : s2 = s3  via congrArg (λ z, -(w*b) + z) neg_neg_wa_eq
    //   p34 : s3 = s4  via Rat.add_comm -(w*b) (w*a)
    // Compose via Eq.trans.

    let s1 = c.add(neg_wb.clone(), neg(c, neg_w_a.clone()));
    let s2 = c.add(neg_wb.clone(), neg_neg_wa.clone());
    let s3 = c.add(neg_wb.clone(), wa.clone());
    let s4 = c.add(wa.clone(), neg_wb.clone());

    // p01: congrArg (fun x => x + (-((-w)*a))) ident_b
    let f_p01 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.add(x, neg(c, neg_w_a.clone()));
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    let p01 = congr_arg_rat_rat(c, neg_w_b.clone(), neg_wb.clone(), f_p01, ident_b);

    // For p12 we need: (-((-w)*a)) = (-(-(w*a))).  That's congrArg Rat.neg ident_a.
    let neg_of_neg_w_a = neg(c, neg_w_a.clone());
    let e_mid = congr_arg_rat_rat(c, neg_w_a.clone(), neg_wa.clone(), rat_neg(c), ident_a);
    // Now p12 = congrArg (λ y, -(w*b) + y) e_mid
    let f_p12 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (y_id, y) = ch.fresh_local(c.rat.clone());
        let body = c.add(neg_wb.clone(), y);
        let r = ch.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    let p12 = congr_arg_rat_rat(c, neg_of_neg_w_a, neg_neg_wa.clone(), f_p12, e_mid);

    // p23: congrArg (λ z, -(w*b) + z) neg_neg_wa_eq
    let f_p23 = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = ch.fresh_local(c.rat.clone());
        let body = c.add(neg_wb.clone(), z);
        let r = ch.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    let p23 = congr_arg_rat_rat(c, neg_neg_wa.clone(), wa.clone(), f_p23, neg_neg_wa_eq);

    // p34: Rat.add_comm -(w*b) (w*a)
    let p34 = Expr::apps(
        Expr::const_(Name::from_string("Rat.add_comm"), vec![]),
        [neg_wb.clone(), wa.clone()],
    );

    // Compose: s0 →s1 →s2 →s3 →s4 via Eq.trans.
    let t1 = eq_trans_rat(c, lhs_full.clone(), s1.clone(), s2.clone(), p01, p12);
    let t2 = eq_trans_rat(c, lhs_full.clone(), s2, s3.clone(), t1, p23);
    let eq_chain = eq_trans_rat(c, lhs_full.clone(), s3, s4.clone(), t2, p34);
    // eq_chain : lhs_full = rhs_full (where rhs_full = s4 = w*a + -(w*b))

    // =========================================================
    // Step 5: transport h_sub_nn along eq_chain.
    //
    // h_sub_nn : 0 ≤ lhs_full   (by delta of Rat.sub)
    // goal:     0 ≤ rhs_full   (which is 0 ≤ (w*a) - (w*b) by delta of Rat.sub reversed)
    // =========================================================
    let motive_transport = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = ch.fresh_local(c.rat.clone());
        let body = c.rat_le(c.rat_zero.clone(), x);
        let r = ch.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), body);
        ch.finish_child(r)
    };
    let h_nn_wa_sub_wb = eq_subst_rat(c, motive_transport, lhs_full, s4, eq_chain, h_sub_nn);
    // h_nn_wa_sub_wb : 0 ≤ w*a + -(w*b)  ≡ (by delta)  0 ≤ Rat.sub (w*a) (w*b)

    // =========================================================
    // Step 6: apply Rat.le_of_sub_nonneg (w*b) (w*a) : 0 ≤ (w*a) - (w*b) → w*b ≤ w*a.
    // =========================================================
    let le_of_sub_nonneg = Expr::const_(Name::from_string("Rat.le_of_sub_nonneg"), vec![]);
    let body = Expr::apps(le_of_sub_nonneg, [wb.clone(), wa.clone(), h_nn_wa_sub_wb]);

    // Wrap lambdas
    let e = b.mk_lam(h_ab_id, BinderInfo::Default, h_ab_ty, body);
    let e = b.mk_lam(h_w_id, BinderInfo::Default, h_w_np_ty, e);
    let e = b.mk_lam(bv_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}
