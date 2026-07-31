// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — Stage B3 (3/n): the cube dyadic-floor STRICT UPPER bound.
//!
//! # Why this module exists
//!
//! The keystone cube squeeze needs both halves around `k_n := Rat.cbrtDyadicNum x n`:
//!
//! ```text
//!   LOWER (done, algebra_nnreal_cbrt_invariant.rs):  (ofNat k_n)³ ≤ x · 8^n
//!   UPPER (this module):                              x · 8^n < (ofNat (k_n+1))³
//! ```
//!
//! Together they pin `a_n = k_n/2^n` to within `((k_n+1)³−k_n³)/8^n → 0` of `cbrt x`.
//!
//! # DOMAIN RESTRICTION (load-bearing, honest)
//!
//! As in the sqrt layer, the strict upper bound is FALSE for `x ≥ 1` (the
//! recursion hardcodes `k_0 = 0`, so `k_n < 2^n` and the approximation saturates
//! below 1). The bound carries the hypothesis `Rat.lt x Rat.one`:
//!
//! ```text
//!   Rat.cbrtDyadicNum_cube_lt_succ :
//!     0 ≤ x → x < 1 → ∀ n, Rat.lt (x · cbrtDyadicPow8 n) ((ofNat (Nat.succ k_n))³)
//! ```
//!
//! Faithful on `x ∈ [0,1)` (the KKL range; influences `Inf_i ∈ [0,1]`).
//! The hypothesis `x < 1` is used ONLY in the base case `n = 0`.
//!
//! # Proof (Nat.rec over n, Prop motive; mirrors the sqrt upper bound)
//!
//! - BASE `n = 0`: `k_0 ≡ 0`, `8^0 ≡ 1`, so the goal is `x·1 < (ofNat 1)³`.
//!   `x·1 = x` (`Rat.mul_one`) and `(ofNat 1)³ = ((1·1)·1) ≡ 1` (two `mul_one`,
//!   `ofNat 1 ≡ Rat.one` defeq); transport `x < 1`.
//! - STEP `P n → P (n+1)`: dependent `Bool.rec.{0}` on the cube digit test.
//!     * FALSE (`Bool.rec ≡ 2k`, `succ(2k) = 2k+1`): `Rat.lt_of_ble_eq_false`
//!       (landed) gives `x·8^{n+1} < (ofNat(2k+1))³` directly.
//!     * TRUE (`Bool.rec ≡ 2k+1`, `succ(2k+1) = 2(k+1)`): scale the IH by 8 via
//!       `Rat.mul_lt_mul_of_pos_left (ofNat 8)`, transport the LHS to `x·8^{n+1}`
//!       and the RHS to `(ofNat(2(k+1)))³` through the cube scale identity
//!       (the `CbrtInvConsts::cube_scale_eq` helper) instantiated at `k+1`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::algebra_nnreal_cbrt_invariant::CbrtInvConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the cube strict upper bound.
pub(crate) struct CbrtUpperConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_lt: Expr,
    rat_le: Expr,
    rat_mul: Expr,
    rat_ofnat: Expr,
    rat_cbrt_num: Expr,
    rat_cbrt_pow8: Expr,
    rat_ble: Expr,
    bool_ty: Expr,
    bool_true: Expr,
    bool_false: Expr,
    rat_mul_one: Expr,
    rat_mul_assoc: Expr,
    rat_mul_comm: Expr,
    rat_mul_lt_pos_left: Expr,
    rat_lt_of_ble_eq_false: Expr,
    rat_zero_lt_eight: Expr,
    // Recursors / Eq toolkit.
    nat_rec_prop: Expr,
    bool_rec_nat: Expr,
    bool_rec_prop: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    eq_subst_prop: Expr,
    congr_arg11: Expr,
    // the cube-scale provider (carries ofNat_mul/mmmc smart-constructors).
    inv: CbrtInvConsts,
}

impl CbrtUpperConsts {
    pub(crate) fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_add: k("Nat.add"),
            nat_mul: k("Nat.mul"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_lt: k("Rat.lt"),
            rat_le: k("Rat.le"),
            rat_mul: k("Rat.mul"),
            rat_ofnat: k("Rat.ofNat"),
            rat_cbrt_num: k("Rat.cbrtDyadicNum"),
            rat_cbrt_pow8: k("Rat.cbrtDyadicPow8"),
            rat_ble: k("Rat.ble"),
            bool_ty: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            rat_mul_one: k("Rat.mul_one"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_lt_pos_left: k("Rat.mul_lt_mul_of_pos_left"),
            rat_lt_of_ble_eq_false: k("Rat.lt_of_ble_eq_false"),
            rat_zero_lt_eight: k("Rat.zero_lt_ofNat_eight"),
            nat_rec_prop: Expr::const_(Name::from_string("Nat.rec"), vec![l0.clone()]),
            bool_rec_nat: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            bool_rec_prop: Expr::const_(Name::from_string("Bool.rec"), vec![l0]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_subst_prop: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg11: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            inv: CbrtInvConsts::new(),
        }
    }

    // ── small constructors ──
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_add.clone(), [a, b])
    }
    fn nmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [a, b])
    }
    fn nat_lit(&self, n: u32) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = self.succ(e);
        }
        e
    }
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn rofnat(&self, n: Expr) -> Expr {
        Expr::app(self.rat_ofnat.clone(), n)
    }
    fn cnum(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_cbrt_num.clone(), [x.clone(), n])
    }
    fn pow8(&self, n: Expr) -> Expr {
        Expr::app(self.rat_cbrt_pow8.clone(), n)
    }
    /// `(ofNat m)³ := (ofNat m · ofNat m) · ofNat m`.
    fn cube_ofnat(&self, m: Expr) -> Expr {
        let r = self.rofnat(m);
        let sq = self.rmul(r.clone(), r.clone());
        self.rmul(sq, r)
    }
    fn eq_bool(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_ty.clone(), x, y])
    }
    fn refl_bool(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.bool_ty.clone(), x])
    }
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [self.rat.clone(), a, b, cc, hab, hbc],
        )
    }
    fn congr_rat(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg11.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    fn subst_rat_prop(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst_prop.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `Rat.mul_lt_mul_of_pos_left a b c (h:b<c)(h0:0<a) : a·b < a·c`.
    fn mul_lt_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_lt_pos_left.clone(), [a, b, cc, h, h0])
    }
    fn f_right(&self, parent: &EnvDeclBuilder, t: Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.rat.clone());
        let body = self.rmul(w, t);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
    }

    /// `cbrtDyadicNum x (succ n)`'s defining `Bool.rec` value at explicit `b`.
    fn bool_rec_num(&self, parent: &EnvDeclBuilder, kk: &Expr, b: Expr) -> Expr {
        let two_k = self.nmul(self.nat_lit(2), kk.clone());
        let two_k1 = self.nadd(two_k.clone(), self.nat_lit(1));
        let bmotive = {
            let mut bm = EnvDeclBuilder::child_of(parent);
            let (z_id, _z) = bm.fresh_local(self.bool_ty.clone());
            bm.finish_child(bm.mk_lam(
                z_id,
                BinderInfo::Default,
                self.bool_ty.clone(),
                self.nat.clone(),
            ))
        };
        Expr::apps(self.bool_rec_nat.clone(), [bmotive, two_k, two_k1, b])
    }

    /// The cube digit test `Rat.ble ((ofNat (2k+1))³) (x·8^{n+1})`.
    fn digit_test(&self, x: &Expr, kk: &Expr, n: &Expr) -> Expr {
        let two_k = self.nmul(self.nat_lit(2), kk.clone());
        let two_k1 = self.nadd(two_k, self.nat_lit(1));
        let lhs = self.cube_ofnat(two_k1);
        let rhs = self.rmul(x.clone(), self.pow8(self.succ(n.clone())));
        Expr::apps(self.rat_ble.clone(), [lhs, rhs])
    }
}

impl Environment {
    /// Register `Rat.cbrtDyadicNum_cube_lt_succ` (and the `0 < ofNat 8` helper).
    /// Idempotent; axiom-free.
    pub fn init_algebra_nnreal_cbrt_upper(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cbrt_invariant()?; // cbrtDyadicNum, pow8, ofNat_mul, mmmc, …
        self.init_algebra_nnreal_sqrt_strict()?; // Rat.lt_of_ble_eq_false
        self.init_boolean_analysis_order_toolkit_b1b()?; // Rat.mul_lt_mul_of_pos_left
        self.register_rat_mul_assoc_proof()?;
        self.register_rat_mul_comm_proof()?;
        self.register_rat_ofnat()?;
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;

        let c = CbrtUpperConsts::new();
        self.register_rat_zero_lt_ofnat_eight(&c)?;
        self.register_cbrt_dyadic_num_cube_lt_succ(&c)
    }

    /// `Rat.zero_lt_ofNat_eight : Rat.lt Rat.zero (Rat.ofNat 8)`.
    /// `Rat.lt 0 (ofNat 8)` δ+ι-reduces to `Int.NonNeg (Int.ofNat 7)`; the
    /// canonical witness `@Int.NonNeg.mk 7` closes it (the `zero_lt_one` idiom).
    fn register_rat_zero_lt_ofnat_eight(&mut self, c: &CbrtUpperConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.zero_lt_ofNat_eight");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = c.rlt(c.rat_zero.clone(), c.rofnat(c.nat_lit(8)));
        let value = Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            c.nat_lit(7),
        );
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    fn register_cbrt_dyadic_num_cube_lt_succ(
        &mut self,
        c: &CbrtUpperConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cbrtDyadicNum_cube_lt_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // motive_body x n := x·8^n < (ofNat (succ (cnum x n)))³.
        let motive_body = |x: &Expr, n: &Expr| -> Expr {
            c.rlt(
                c.rmul(x.clone(), c.pow8(n.clone())),
                c.cube_ofnat(c.succ(c.cnum(x, n.clone()))),
            )
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let le0_ty = Expr::apps(c.rat_le.clone(), [c.rat_zero.clone(), x.clone()]);
            let (h0_id, _h0) = b.fresh_local(le0_ty.clone());
            let h1_ty = c.rlt(x.clone(), c.rat_one.clone());
            let (h1_id, _h1) = b.fresh_local(h1_ty.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ib.fresh_local(c.nat.clone());
                let body = motive_body(&x, &n);
                ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let e = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, inner);
            let e = b.mk_pi(h0_id, BinderInfo::Default, le0_ty, e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = build_upper_value(c, &motive_body);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `fun x h0 h1 => Nat.rec motive base step`.
fn build_upper_value(c: &CbrtUpperConsts, motive_body: &dyn Fn(&Expr, &Expr) -> Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let le0_ty = Expr::apps(c.rat_le.clone(), [c.rat_zero.clone(), x.clone()]);
    let (h0_id, _h0) = b.fresh_local(le0_ty.clone());
    let h1_ty = c.rlt(x.clone(), c.rat_one.clone());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());

    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = m.fresh_local(c.nat.clone());
        let body = motive_body(&x, &n);
        m.finish_child(m.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
    };

    let base = build_base(c, &b, &x, &h1);
    let step = build_step(c, &b, &x);

    let rec = Expr::apps(c.nat_rec_prop.clone(), [motive, base, step]);
    let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, rec);
    let e = b.mk_lam(h0_id, BinderInfo::Default, le0_ty, e);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// BASE `n=0`: goal ≡ `x·1 < ((ofNat 1·ofNat 1)·ofNat 1)`.
/// `x·1 = x` (mul_one); `((1·1)·1) ≡ 1` via two `mul_one` (ofNat 1 ≡ Rat.one).
fn build_base(c: &CbrtUpperConsts, parent: &EnvDeclBuilder, x: &Expr, h1: &Expr) -> Expr {
    let b = EnvDeclBuilder::child_of(parent);
    let one = c.rat_one.clone();
    let of1 = c.rofnat(c.nat_lit(1)); // ofNat 1 (≡ Rat.one defeq)
    let lhs = c.rmul(x.clone(), one.clone()); // x · 1   (8^0 ≡ 1)
    let sq1 = c.rmul(of1.clone(), of1.clone()); // ofNat 1 · ofNat 1
    let rhs = c.rmul(sq1.clone(), of1.clone()); // (ofNat 1 · ofNat 1) · ofNat 1

    // e_lhs : (x·1) = x.
    let e_lhs = Expr::app(c.rat_mul_one.clone(), x.clone());
    // e_sq1 : (of1·of1) = of1   via mul_one of1.
    let e_sq1 = Expr::app(c.rat_mul_one.clone(), of1.clone());
    // congr (· · of1) e_sq1 : (of1·of1)·of1 = of1·of1.
    let f_r = c.f_right(&b, of1.clone());
    let s1 = c.congr_rat(sq1.clone(), of1.clone(), f_r, e_sq1);
    let of1_of1 = c.rmul(of1.clone(), of1.clone());
    // e_of1of1 : of1·of1 = of1   via mul_one of1.
    let e_of1of1 = Expr::app(c.rat_mul_one.clone(), of1.clone());
    // e_rhs : rhs = of1   (s1 ; e_of1of1).
    let e_rhs = c.trans_rat(rhs.clone(), of1_of1.clone(), of1.clone(), s1, e_of1of1);

    // Step 1: from h1 : x < 1, get `x·1 < 1` by subst along symm e_lhs (x → x·1).
    let motive_l = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (l_id, l) = d.fresh_local(c.rat.clone());
        let body = c.rlt(l, one.clone());
        d.finish_child(d.mk_lam(l_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let e_lhs_symm = c.symm_rat(lhs.clone(), x.clone(), e_lhs); // x = x·1
    let lhs_lt_one = c.subst_rat_prop(motive_l, x.clone(), lhs.clone(), e_lhs_symm, h1.clone());

    // Step 2: from `x·1 < 1`(≡ `< ofNat 1`), subst RHS along symm e_rhs (of1 → rhs).
    let motive_r = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (r_id, r) = d.fresh_local(c.rat.clone());
        let body = c.rlt(lhs.clone(), r);
        d.finish_child(d.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let e_rhs_symm = c.symm_rat(rhs.clone(), of1.clone(), e_rhs); // of1 = rhs
    let body = c.subst_rat_prop(motive_r, of1.clone(), rhs.clone(), e_rhs_symm, lhs_lt_one);
    b.finish_child(body)
}

/// STEP: `fun (n:Nat)(ih : P n) => P (n+1)`.
fn build_step(c: &CbrtUpperConsts, parent: &EnvDeclBuilder, x: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = b.fresh_local(c.nat.clone());

    // ih : x·8^n < (ofNat(succ k))³   where k := cnum x n.
    let kk = c.cnum(x, n.clone());
    let succ_k = c.succ(kk.clone());
    let ih_ty = c.rlt(
        c.rmul(x.clone(), c.pow8(n.clone())),
        c.cube_ofnat(succ_k.clone()),
    );
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let test = c.digit_test(x, &kk, &n);
    let rhs_lhs = c.rmul(x.clone(), c.pow8(c.succ(n.clone()))); // x·8^{n+1}

    // motive : fun (z:Bool) => Eq Bool test z →
    //            x·8^{n+1} < (ofNat(succ(Bool.rec _ (2k)(2k+1) z)))³.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = mb.fresh_local(c.bool_ty.clone());
        let heq_ty = c.eq_bool(test.clone(), z.clone());
        let (heq_id, _heq) = mb.fresh_local(heq_ty.clone());
        let num_z = c.bool_rec_num(&mb, &kk, z.clone());
        let concl = c.rlt(rhs_lhs.clone(), c.cube_ofnat(c.succ(num_z)));
        let body = mb.mk_pi(heq_id, BinderInfo::Default, heq_ty, concl);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.bool_ty.clone(), body))
    };

    // FALSE minor: succ(2k) = 2k+1, goal `x·8^{n+1} < (ofNat(2k+1))³`,
    //   = `Rat.lt_of_ble_eq_false ((ofNat(2k+1))³)(x·8^{n+1}) heq`.
    let false_minor = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let heq_ty = c.eq_bool(test.clone(), c.bool_false.clone());
        let (heq_id, heq) = fb.fresh_local(heq_ty.clone());
        let two_k = c.nmul(c.nat_lit(2), kk.clone());
        let two_k1 = c.nadd(two_k, c.nat_lit(1));
        let cube = c.cube_ofnat(two_k1);
        let body = Expr::apps(
            c.rat_lt_of_ble_eq_false.clone(),
            [cube, rhs_lhs.clone(), heq],
        );
        let lam = fb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
        fb.finish_child(lam)
    };

    // TRUE minor: succ(2k+1) = 2(k+1), goal `x·8^{n+1} < (ofNat(2(k+1)))³`.
    let true_minor = build_true_minor(c, &b, x, &n, &kk, &ih);

    let rec_app = Expr::apps(
        c.bool_rec_prop.clone(),
        [motive, false_minor, true_minor, test.clone()],
    );
    let applied = Expr::app(rec_app, c.refl_bool(test.clone()));

    let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, applied);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish_child(e)
}

/// TRUE minor: `fun (heq) => x·8^{n+1} < (ofNat(2(k+1)))³` by scaling IH by 8.
/// Goal RHS `(ofNat(succ(2k+1)))³` is defeq to `(ofNat(2·(k+1)))³`.
fn build_true_minor(
    c: &CbrtUpperConsts,
    parent: &EnvDeclBuilder,
    x: &Expr,
    n: &Expr,
    kk: &Expr,
    ih: &Expr,
) -> Expr {
    let mut tb = EnvDeclBuilder::child_of(parent);
    let test = c.digit_test(x, kk, n);
    let heq_ty = c.eq_bool(test, c.bool_true.clone());
    let (heq_id, _heq) = tb.fresh_local(heq_ty.clone());

    let of8 = c.rofnat(c.nat_lit(8));
    let succ_k = c.succ(kk.clone()); // k+1
    let ofk1 = c.rofnat(succ_k.clone()); // ofNat(k+1)
    let two_m = c.nmul(c.nat_lit(2), succ_k.clone()); // 2·(k+1) (Nat)
    let cube_k1 = {
        let sq = c.rmul(ofk1.clone(), ofk1.clone());
        c.rmul(sq, ofk1.clone())
    }; // (ofNat(k+1))³
    let pow8n = c.pow8(n.clone());
    let x_pow = c.rmul(x.clone(), pow8n.clone()); // x·8^n

    // pos8 : 0 < ofNat 8.
    let pos8 = c.rat_zero_lt_eight.clone();

    // scaled : ofNat8·(x·8^n) < ofNat8·(ofNat(k+1))³
    //   via mul_lt_mul_of_pos_left (ofNat8)(x·8^n)(cube_k1) ih pos8.
    let scaled = c.mul_lt_left(
        of8.clone(),
        x_pow.clone(),
        cube_k1.clone(),
        ih.clone(),
        pos8,
    );

    // ── LEFT (the strict goal LHS): x·8^{n+1} = ofNat8·(x·8^n) ──
    let pow8_succ_unfold = c.rmul(of8.clone(), pow8n.clone()); // o8·8^n ≡ 8^{n+1}
    let r0 = c.rmul(x.clone(), pow8_succ_unfold.clone()); // x·(o8·8^n) ≡ x·8^{n+1}
    let assoc1 = Expr::apps(
        c.rat_mul_assoc.clone(),
        [x.clone(), of8.clone(), pow8n.clone()],
    ); // (x·o8)·p = x·(o8·p)
    let xo8 = c.rmul(x.clone(), of8.clone());
    let r1 = c.rmul(xo8.clone(), pow8n.clone());
    let assoc1_symm = c.symm_rat(r1.clone(), r0.clone(), assoc1); // x·(o8·p) = (x·o8)·p
    let comm1 = Expr::apps(c.rat_mul_comm.clone(), [x.clone(), of8.clone()]); // x·o8 = o8·x
    let o8x = c.rmul(of8.clone(), x.clone());
    let f_pp = c.f_right(&tb, pow8n.clone());
    let s_r2 = c.congr_rat(xo8.clone(), o8x.clone(), f_pp, comm1);
    let r2 = c.rmul(o8x.clone(), pow8n.clone());
    let assoc2 = Expr::apps(
        c.rat_mul_assoc.clone(),
        [of8.clone(), x.clone(), pow8n.clone()],
    ); // (o8·x)·p = o8·(x·p)
    let r3 = c.rmul(of8.clone(), x_pow.clone()); // o8·(x·p)
    let r0_r2 = c.trans_rat(r0.clone(), r1.clone(), r2.clone(), assoc1_symm, s_r2);
    let left_eq = c.trans_rat(r0.clone(), r2.clone(), r3.clone(), r0_r2, assoc2); // r0 = r3

    // ── RIGHT (the strict goal RHS): ofNat8·(ofNat(k+1))³ = (ofNat(2(k+1)))³ ──
    //   This is SYMM of the cube scale identity at m := k+1
    //   (cube_scale_eq m : (ofNat 2m)³ = ofNat 8 · (ofNat m)³).
    let l0 = {
        let of_2m = c.rofnat(two_m.clone());
        let sq = c.rmul(of_2m.clone(), of_2m.clone());
        c.rmul(sq, of_2m.clone())
    }; // (ofNat(2m))³  ≡ goal RHS
    let r3_right = c.rmul(of8.clone(), cube_k1.clone()); // ofNat8·(ofNat(k+1))³
    let cube_scale = c.inv.cube_scale_eq(&tb, &succ_k); // (ofNat 2m)³ = ofNat8·(ofNat m)³
                                                        // right_eq : r3_right = l0  (SYMM of cube_scale).
    let right_eq = c.symm_rat(l0.clone(), r3_right.clone(), cube_scale);

    // Assemble: scaled : r3 < r3_right ; left_eq : r0 = r3 ; right_eq : r3_right = l0.
    // Goal: r0 < l0.
    // Step A: subst scaled's LHS r3 → r0 via symm left_eq.
    let motive_a = {
        let mut d = EnvDeclBuilder::child_of(&tb);
        let (u_id, u) = d.fresh_local(c.rat.clone());
        let body = c.rlt(u, r3_right.clone());
        d.finish_child(d.mk_lam(u_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let left_eq_symm = c.symm_rat(r0.clone(), r3.clone(), left_eq); // r3 = r0
    let r0_lt_r3right = c.subst_rat_prop(motive_a, r3.clone(), r0.clone(), left_eq_symm, scaled);
    // Step B: subst RHS r3_right → l0 via right_eq.
    let motive_b = {
        let mut d = EnvDeclBuilder::child_of(&tb);
        let (v_id, v) = d.fresh_local(c.rat.clone());
        let body = c.rlt(r0.clone(), v);
        d.finish_child(d.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let r0_lt_l0 = c.subst_rat_prop(
        motive_b,
        r3_right.clone(),
        l0.clone(),
        right_eq,
        r0_lt_r3right,
    );

    let lam = tb.mk_lam(heq_id, BinderInfo::Default, heq_ty, r0_lt_l0);
    tb.finish_child(lam)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cbrt_upper()
            .expect("init_algebra_nnreal_cbrt_upper");
        env.init_algebra_nnreal_cbrt_upper().expect("idempotent");
        env
    }

    const THMS: &[&str] = &["Rat.zero_lt_ofNat_eight", "Rat.cbrtDyadicNum_cube_lt_succ"];

    #[test]
    fn test_cbrt_upper_kernel_checks() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for nm in THMS {
            let name = Name::from_string(nm);
            let info = env.get_const(&name).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{nm} must be Theorem");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{nm} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_cbrt_upper_constructive_empty_closure() {
        let env = env();
        for nm in THMS {
            let name = Name::from_string(nm);
            assert_eq!(
                env.proof_quality(&name),
                Some(ProofQuality::Constructive),
                "{nm} must be Constructive"
            );
            assert!(
                env.axiom_deps(&name).expect("deps").is_empty(),
                "{nm} closure must be foundational-only: {:?}",
                env.axiom_deps(&name)
            );
        }
    }
}
