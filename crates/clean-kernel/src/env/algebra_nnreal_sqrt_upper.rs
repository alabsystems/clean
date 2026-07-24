// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage B3 (4/n): the dyadic-floor STRICT UPPER bound.
//!
//! # Why this module exists
//!
//! The keystone squeeze needs both halves around `k_n := Rat.dyadicNum x n`:
//!
//! ```text
//!   LOWER (done, algebra_nnreal_sqrt_invariant.rs):  (ofNat k_n)² ≤ x · 4^n
//!   UPPER (this module):                              x · 4^n < (ofNat (k_n+1))²
//! ```
//!
//! Together they pin `a_n = k_n/2^n` to within `(2k_n+1)/4^n → 0` of `√x`.
//!
//! # DOMAIN RESTRICTION (load-bearing, honest)
//!
//! The strict upper bound is FALSE for `x ≥ 1` with the as-built `dyadicNum`,
//! because the recursion HARDCODES `k_0 = 0` (it never seeds the integer part),
//! so `k_n ≤ 2^n − 1 < 2^n` for all `n` and the approximation saturates below 1.
//! Concretely at `x = 4`: `k_n = 2^n − 1`, and at `n = 3` the bound would read
//! `4·64 = 256 < 8² = 64`, which is false.
//!
//! The bound therefore carries the hypothesis `Rat.lt x Rat.one` (`x < 1`):
//!
//! ```text
//!   Rat.dyadicNum_sq_lt_succ :
//!     0 ≤ x → x < 1 → ∀ n, Rat.lt (x · dyadicPow4 n) ((ofNat (Nat.succ (dyadicNum x n)))²)
//! ```
//!
//! This restricts the SELF-CONTAINED dyadic keystone to `x ∈ [0,1)`. The
//! arbitrary-`x` √ then factors as `√x = 2^m · √(x/4^m)` (range reduction; a
//! separate, mechanical layer) — or the KKL charge consumes the in-range form
//! directly (the influences `Inf_i ∈ [0,1]`). The hypothesis is used in EXACTLY
//! the base case `n = 0`; the inductive step holds for every `x`.
//!
//! # Proof (Nat.rec over n, Prop motive; mirrors the lower-bound invariant)
//!
//! - BASE `n = 0`: `k_0 ≡ 0`, `4^0 ≡ 1`, so the goal is `x·1 < (ofNat 1)²`.
//!   `x·1 = x` (`Rat.mul_one`) and `(ofNat 1)² = ofNat 1 · ofNat 1` with
//!   `ofNat 1 ≡ Rat.one` defeq, so `(ofNat 1)² ≡ Rat.one` after `Rat.mul_one`.
//!   The hypothesis `x < 1` transports along both equalities.
//!
//! - STEP `P n → P (n+1)`: dependent `Bool.rec.{0}` on the digit `test`.
//!     * FALSE (`Bool.rec ≡ 2k`, `succ(2k) = 2k+1`): the test being `false` is
//!       `ble ((ofNat(2k+1))²) (x·4^{n+1}) = false`, so
//!       `Rat.lt_of_ble_eq_false` (Stage-B3 rung 1) gives the goal directly.
//!     * TRUE (`Bool.rec ≡ 2k+1`, `succ(2k+1) = 2(k+1)`): scale the IH by 4.
//!       `Rat.mul_lt_mul_of_pos_left (ofNat 4)` on `ih : x·4^n < (ofNat(k+1))²`
//!       gives `4·(x·4^n) < 4·(ofNat(k+1))²`; transport the LHS to `x·4^{n+1}`
//!       and the RHS to `(ofNat(2(k+1)))²` (defeq to `(ofNat(succ(2k+1)))²`)
//!       through the same `ofNat_mul`/`mul_mul_mul_comm`/assoc chains the
//!       lower-bound invariant uses, instantiated at `k+1`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the strict upper bound.
pub(crate) struct UpperConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_lt: Expr,
    rat_mul: Expr,
    rat_ofnat: Expr,
    rat_dyadic_num: Expr,
    rat_dyadic_pow4: Expr,
    rat_ble: Expr,
    bool_ty: Expr,
    bool_true: Expr,
    bool_false: Expr,
    rat_mul_one: Expr,
    rat_mul_assoc: Expr,
    rat_mul_comm: Expr,
    rat_mul_mul_mul_comm: Expr,
    rat_ofnat_mul: Expr,
    rat_mul_lt_pos_left: Expr,
    rat_lt_of_ble_eq_false: Expr,
    rat_zero_lt_four: Expr,
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
}

impl UpperConsts {
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
            rat_mul: k("Rat.mul"),
            rat_ofnat: k("Rat.ofNat"),
            rat_dyadic_num: k("Rat.dyadicNum"),
            rat_dyadic_pow4: k("Rat.dyadicPow4"),
            rat_ble: k("Rat.ble"),
            bool_ty: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            rat_mul_one: k("Rat.mul_one"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            rat_ofnat_mul: k("Rat.ofNat_mul"),
            rat_mul_lt_pos_left: k("Rat.mul_lt_mul_of_pos_left"),
            rat_lt_of_ble_eq_false: k("Rat.lt_of_ble_eq_false"),
            rat_zero_lt_four: k("Rat.zero_lt_ofNat_four"),
            nat_rec_prop: Expr::const_(Name::from_string("Nat.rec"), vec![l0.clone()]),
            bool_rec_nat: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            bool_rec_prop: Expr::const_(Name::from_string("Bool.rec"), vec![l0.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_subst_prop: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg11: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
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
    fn dnum(&self, x: &Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_dyadic_num.clone(), [x.clone(), n])
    }
    fn pow4(&self, n: Expr) -> Expr {
        Expr::app(self.rat_dyadic_pow4.clone(), n)
    }
    /// `(ofNat m)²`.
    fn sq_ofnat(&self, m: Expr) -> Expr {
        let r = self.rofnat(m);
        self.rmul(r.clone(), r)
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
    fn ofnat_mul(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_ofnat_mul.clone(), [m, n])
    }
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mul_mul_mul_comm.clone(), [a, b, cc, d])
    }
    /// `Rat.mul_lt_mul_of_pos_left a b c (h:b<c)(h0:0<a) : a·b < a·c`.
    fn mul_lt_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_lt_pos_left.clone(), [a, b, cc, h, h0])
    }

    /// `dyadicNum x (succ n)`'s defining `Bool.rec` value at an explicit `b`.
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

    /// The digit test `Rat.ble ((ofNat (2k+1))²) (x·4^{n+1})`.
    fn digit_test(&self, x: &Expr, kk: &Expr, n: &Expr) -> Expr {
        let two_k = self.nmul(self.nat_lit(2), kk.clone());
        let two_k1 = self.nadd(two_k, self.nat_lit(1));
        let lhs = self.sq_ofnat(two_k1);
        let rhs = self.rmul(x.clone(), self.pow4(self.succ(n.clone())));
        Expr::apps(self.rat_ble.clone(), [lhs, rhs])
    }
}

impl Environment {
    /// Register `Rat.dyadicNum_sq_lt_succ` (and the `0 < ofNat 4` helper).
    /// Idempotent; axiom-free.
    pub fn init_algebra_nnreal_sqrt_upper(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_sqrt_invariant()?; // dyadicNum, pow4, ofNat_mul, mmmc, …
        self.init_algebra_nnreal_sqrt_strict()?; // Rat.lt_of_ble_eq_false
        self.init_boolean_analysis_order_toolkit_b1b()?; // Rat.mul_lt_mul_of_pos_left
        self.register_rat_ofnat()?;
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;

        let c = UpperConsts::new();
        self.register_rat_zero_lt_ofnat_four(&c)?;
        self.register_dyadic_num_sq_lt_succ(&c)
    }

    /// `Rat.zero_lt_ofNat_four : Rat.lt Rat.zero (Rat.ofNat 4)`.
    ///
    /// `Rat.lt Rat.zero (ofNat 4)` δ+ι-reduces (closed Int arithmetic) to
    /// `Int.NonNeg (Int.ofNat 3)`; the canonical witness `@Int.NonNeg.mk 3`
    /// closes it by definitional reduction (the `Rat.zero_lt_one` idiom).
    fn register_rat_zero_lt_ofnat_four(&mut self, c: &UpperConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.zero_lt_ofNat_four");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = c.rlt(c.rat_zero.clone(), c.rofnat(c.nat_lit(4)));
        // @Int.NonNeg.mk (Nat.lit 3) : Int.NonNeg (Int.ofNat 3).
        let value = Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            c.nat_lit(3),
        );
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    fn register_dyadic_num_sq_lt_succ(&mut self, c: &UpperConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.dyadicNum_sq_lt_succ");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // motive_body x n := x·4^n < (ofNat (succ (dnum x n)))².
        let motive_body = |x: &Expr, n: &Expr| -> Expr {
            c.rlt(
                c.rmul(x.clone(), c.pow4(n.clone())),
                c.sq_ofnat(c.succ(c.dnum(x, n.clone()))),
            )
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h0_ty = c.rlt(c.rat_zero.clone(), x.clone());
            // h0 : 0 < x would be too strong (x can be 0); use 0 ≤ x via Rat.le.
            // We instead require `0 ≤ x` and `x < 1`. Build 0 ≤ x with Rat.le.
            let _ = h0_ty;
            let le0_ty = Expr::apps(
                Expr::const_(Name::from_string("Rat.le"), vec![]),
                [c.rat_zero.clone(), x.clone()],
            );
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
fn build_upper_value(c: &UpperConsts, motive_body: &dyn Fn(&Expr, &Expr) -> Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let le0_ty = Expr::apps(
        Expr::const_(Name::from_string("Rat.le"), vec![]),
        [c.rat_zero.clone(), x.clone()],
    );
    let (h0_id, _h0) = b.fresh_local(le0_ty.clone());
    let h1_ty = c.rlt(x.clone(), c.rat_one.clone());
    let (h1_id, h1) = b.fresh_local(h1_ty.clone());

    // motive : fun (n:Nat) => x·4^n < (ofNat(succ(dnum x n)))².
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

/// BASE `n=0`: goal ≡ `x·1 < (ofNat 1)·(ofNat 1)`.
/// `x·1 = x` (mul_one); `(ofNat 1)·(ofNat 1) = ofNat 1 · 1 = ofNat 1 ≡ 1` —
/// but to avoid the `ofNat 1 ≡ 1` route on the RHS, transport ONLY the LHS:
/// from `h1 : x < 1` and `(ofNat 1)·(ofNat 1) ≡ 1` (defeq: `ofNat 1 ≡ Rat.one`
/// and `Rat.one · Rat.one ≡ Rat.one` is NOT defeq, so use `Rat.mul_one`).
fn build_base(c: &UpperConsts, parent: &EnvDeclBuilder, x: &Expr, h1: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let one = c.rat_one.clone();
    let of1 = c.rofnat(c.nat_lit(1)); // ofNat 1  (≡ Rat.one defeq)
    let lhs = c.rmul(x.clone(), one.clone()); // x · 1   (4^0 ≡ 1)
    let rhs = c.rmul(of1.clone(), of1.clone()); // (ofNat 1)·(ofNat 1)

    // e_lhs : (x · 1) = x   via Rat.mul_one x.
    let e_lhs = Expr::app(c.rat_mul_one.clone(), x.clone());
    // e_rhs : (ofNat 1 · ofNat 1) = ofNat 1   via Rat.mul_one (ofNat 1).
    //   (ofNat 1 ≡ Rat.one, and `Rat.one` is the `< 1` bound, so the goal RHS
    //    rewrites to `ofNat 1` which is defeq to the `1` in `h1`.)
    let e_rhs = Expr::app(c.rat_mul_one.clone(), of1.clone());

    // Step 1: from h1 : x < 1, get `x·1 < 1` by subst along symm e_lhs
    //   (motive_l l := l < 1). e_lhs : x·1 = x, symm : x = x·1.
    let motive_l = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (l_id, l) = d.fresh_local(c.rat.clone());
        let body = c.rlt(l, one.clone());
        d.finish_child(d.mk_lam(l_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let e_lhs_symm = c.symm_rat(lhs.clone(), x.clone(), e_lhs); // x = x·1
    let lhs_lt_one = c.subst_rat_prop(motive_l, x.clone(), lhs.clone(), e_lhs_symm, h1.clone());

    // Step 2: from `x·1 < 1`, get `x·1 < rhs` by subst along symm e_rhs
    //   (motive_r r := lhs < r). e_rhs : rhs = ofNat 1; ofNat 1 ≡ 1 defeq, so
    //   `lhs < 1` ≡ `lhs < ofNat 1`; symm e_rhs : ofNat 1 = rhs.
    let motive_r = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (r_id, r) = d.fresh_local(c.rat.clone());
        let body = c.rlt(lhs.clone(), r);
        d.finish_child(d.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let e_rhs_symm = c.symm_rat(rhs.clone(), of1.clone(), e_rhs); // ofNat 1 = rhs
                                                                  // `lhs_lt_one : lhs < 1` ; `1 ≡ ofNat 1` defeq, so this also types as `lhs < ofNat 1`.
    let body = c.subst_rat_prop(motive_r, of1.clone(), rhs.clone(), e_rhs_symm, lhs_lt_one);
    b.finish_child(body)
}

/// STEP: `fun (n:Nat)(ih : P n) => P (n+1)`.
fn build_step(c: &UpperConsts, parent: &EnvDeclBuilder, x: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = b.fresh_local(c.nat.clone());

    // ih : x·4^n < (ofNat(succ k))²   where k := dnum x n.
    let kk = c.dnum(x, n.clone());
    let succ_k = c.succ(kk.clone());
    let ih_ty = c.rlt(
        c.rmul(x.clone(), c.pow4(n.clone())),
        c.sq_ofnat(succ_k.clone()),
    );
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let test = c.digit_test(x, &kk, &n);
    let rhs_lhs = c.rmul(x.clone(), c.pow4(c.succ(n.clone()))); // x·4^{n+1}

    // motive : fun (z:Bool) => Eq Bool test z →
    //            x·4^{n+1} < (ofNat(succ(Bool.rec _ (2k)(2k+1) z)))².
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = mb.fresh_local(c.bool_ty.clone());
        let heq_ty = c.eq_bool(test.clone(), z.clone());
        let (heq_id, _heq) = mb.fresh_local(heq_ty.clone());
        let num_z = c.bool_rec_num(&mb, &kk, z.clone());
        let concl = c.rlt(rhs_lhs.clone(), c.sq_ofnat(c.succ(num_z)));
        let body = mb.mk_pi(heq_id, BinderInfo::Default, heq_ty, concl);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.bool_ty.clone(), body))
    };

    // FALSE minor: succ(2k) = 2k+1, goal `x·4^{n+1} < (ofNat(2k+1))²`,
    //   = `Rat.lt_of_ble_eq_false ((ofNat(2k+1))²)(x·4^{n+1}) heq`.
    let false_minor = {
        let mut fb = EnvDeclBuilder::child_of(&b);
        let heq_ty = c.eq_bool(test.clone(), c.bool_false.clone());
        let (heq_id, heq) = fb.fresh_local(heq_ty.clone());
        let two_k = c.nmul(c.nat_lit(2), kk.clone());
        let two_k1 = c.nadd(two_k, c.nat_lit(1));
        let sq = c.sq_ofnat(two_k1);
        // lt_of_ble_eq_false sq (x·4^{n+1}) heq : x·4^{n+1} < sq.
        let body = Expr::apps(c.rat_lt_of_ble_eq_false.clone(), [sq, rhs_lhs.clone(), heq]);
        let lam = fb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
        fb.finish_child(lam)
    };

    // TRUE minor: succ(2k+1) = 2(k+1), goal `x·4^{n+1} < (ofNat(2(k+1)))²`.
    let true_minor = build_true_minor(c, &b, x, &n, &kk, &ih);

    // Bool.rec.{0} motive false_minor true_minor test (Eq.refl test).
    let rec_app = Expr::apps(
        c.bool_rec_prop.clone(),
        [motive, false_minor, true_minor, test.clone()],
    );
    let applied = Expr::app(rec_app, c.refl_bool(test.clone()));

    let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, applied);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish_child(e)
}

/// TRUE minor: `fun (heq) => x·4^{n+1} < (ofNat(2(k+1)))²` by scaling IH by 4.
///
/// Goal RHS `(ofNat(succ(2k+1)))²` is defeq to `(ofNat(2·(succ k)))²` (Nat
/// computation `succ(2k+1) = 2k+2 = 2·(k+1)`).
fn build_true_minor(
    c: &UpperConsts,
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

    let of2 = c.rofnat(c.nat_lit(2));
    let of4 = c.rofnat(c.nat_lit(4));
    let succ_k = c.succ(kk.clone()); // k+1
    let ofk1 = c.rofnat(succ_k.clone()); // ofNat(k+1)
    let two_k1n = c.nmul(c.nat_lit(2), succ_k.clone()); // 2·(k+1)  (Nat)
    let sq_k1 = c.rmul(ofk1.clone(), ofk1.clone()); // (ofNat(k+1))²
    let pow4n = c.pow4(n.clone());
    let x_pow = c.rmul(x.clone(), pow4n.clone()); // x·4^n

    // pos4 : 0 < ofNat 4.
    let pos4 = c.rat_zero_lt_four.clone();

    // scaled : ofNat4·(x·4^n) < ofNat4·(ofNat(k+1))²
    //   via mul_lt_mul_of_pos_left (ofNat4)(x·4^n)(sq_k1) ih pos4.
    let scaled = c.mul_lt_left(of4.clone(), x_pow.clone(), sq_k1.clone(), ih.clone(), pos4);

    // ── LEFT (the strict goal LHS): x·4^{n+1} = ofNat4·(x·4^n) ──
    // (same chain as the invariant's right_eq, at this n).
    let pow4_succ_unfold = c.rmul(of4.clone(), pow4n.clone()); // o4·4^n  (≡ 4^{n+1})
    let r0 = c.rmul(x.clone(), pow4_succ_unfold.clone()); // x·(o4·4^n) ≡ x·4^{n+1}
    let assoc1 = Expr::apps(
        c.rat_mul_assoc.clone(),
        [x.clone(), of4.clone(), pow4n.clone()],
    ); // (x·o4)·p = x·(o4·p)
    let xo4 = c.rmul(x.clone(), of4.clone());
    let r1 = c.rmul(xo4.clone(), pow4n.clone());
    let assoc1_symm = c.symm_rat(r1.clone(), r0.clone(), assoc1); // x·(o4·p) = (x·o4)·p
    let comm1 = Expr::apps(c.rat_mul_comm.clone(), [x.clone(), of4.clone()]); // x·o4 = o4·x
    let o4x = c.rmul(of4.clone(), x.clone());
    let f_pp = {
        let mut d = EnvDeclBuilder::child_of(&tb);
        let (w_id, w) = d.fresh_local(c.rat.clone());
        let body = c.rmul(w, pow4n.clone());
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s_r2 = c.congr_rat(xo4.clone(), o4x.clone(), f_pp, comm1);
    let r2 = c.rmul(o4x.clone(), pow4n.clone());
    let assoc2 = Expr::apps(
        c.rat_mul_assoc.clone(),
        [of4.clone(), x.clone(), pow4n.clone()],
    ); // (o4·x)·p = o4·(x·p)
    let r3 = c.rmul(of4.clone(), x_pow.clone()); // o4·(x·p)
    let r0_r2 = c.trans_rat(r0.clone(), r1.clone(), r2.clone(), assoc1_symm, s_r2);
    let left_eq = c.trans_rat(r0.clone(), r2.clone(), r3.clone(), r0_r2, assoc2); // r0 = r3

    // ── RIGHT (the strict goal RHS): ofNat4·(ofNat(k+1))² = (ofNat(2(k+1)))² ──
    // i.e. the SYMM of the invariant's left_eq, at m := k+1.
    //   (ofNat(2m))² = ofNat4·(ofNat m)²   [invariant's left_eq shape] ; we need
    //   the reverse, then it is defeq to the goal RHS (ofNat(succ(2k+1)))².
    let of_2m = c.rofnat(two_k1n.clone()); // ofNat(2·(k+1))
    let l0 = c.rmul(of_2m.clone(), of_2m.clone()); // (ofNat(2m))²
    let e_2m = c.ofnat_mul(c.nat_lit(2), succ_k.clone()); // ofNat(2·m) = ofNat2·ofNat m
    let prod_2m = c.rmul(of2.clone(), ofk1.clone());
    // s1 : of_2m·of_2m = prod_2m·of_2m
    let f_right = {
        let mut d = EnvDeclBuilder::child_of(&tb);
        let (w_id, w) = d.fresh_local(c.rat.clone());
        let body = c.rmul(w, of_2m.clone());
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s1 = c.congr_rat(of_2m.clone(), prod_2m.clone(), f_right, e_2m.clone());
    let l1 = c.rmul(prod_2m.clone(), of_2m.clone());
    // s2 : prod_2m·of_2m = prod_2m·prod_2m
    let f_left = {
        let mut d = EnvDeclBuilder::child_of(&tb);
        let (w_id, w) = d.fresh_local(c.rat.clone());
        let body = c.rmul(prod_2m.clone(), w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s2 = c.congr_rat(of_2m.clone(), prod_2m.clone(), f_left, e_2m.clone());
    let l2 = c.rmul(prod_2m.clone(), prod_2m.clone()); // (o2·om)·(o2·om)
    let l0_l2 = c.trans_rat(l0.clone(), l1.clone(), l2.clone(), s1, s2);
    // s3 : (o2·om)·(o2·om) = (o2·o2)·(om·om)  via mmmc.
    let s3 = c.mmmc(of2.clone(), ofk1.clone(), of2.clone(), ofk1.clone());
    let o2o2 = c.rmul(of2.clone(), of2.clone());
    let mid = c.rmul(o2o2.clone(), sq_k1.clone()); // (o2·o2)·(om·om)
                                                   // s5 : (o2·o2)·(om·om) = ofNat4·(om·om)  via congr (·sq_k1)(symm ofNat_mul 2 2).
    let e_22 = c.ofnat_mul(c.nat_lit(2), c.nat_lit(2)); // ofNat(2·2) = o2·o2 ; ofNat 4 = o2o2
    let e_22_symm = c.symm_rat(of4.clone(), o2o2.clone(), e_22); // o2o2 = ofNat 4
    let f_scale = {
        let mut d = EnvDeclBuilder::child_of(&tb);
        let (w_id, w) = d.fresh_local(c.rat.clone());
        let body = c.rmul(w, sq_k1.clone());
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s5 = c.congr_rat(o2o2.clone(), of4.clone(), f_scale, e_22_symm);
    let r3_right = c.rmul(of4.clone(), sq_k1.clone()); // ofNat4·(ofNat(k+1))²
    let l2_mid = c.trans_rat(l2.clone(), mid.clone(), r3_right.clone(), s3, s5);
    // forward_eq : l0 = ofNat4·(ofNat(k+1))²   i.e. (ofNat(2m))² = r3_right.
    let forward_eq = c.trans_rat(l0.clone(), l2.clone(), r3_right.clone(), l0_l2, l2_mid);
    // right_eq : r3_right = l0  (SYMM, so we can subst the RHS of `scaled`).
    let right_eq = c.symm_rat(l0.clone(), r3_right.clone(), forward_eq);

    // Assemble: scaled : r3_right(LHS=o4·(x·p)? NO).
    //   scaled : ofNat4·(x·4^n) < ofNat4·(ofNat(k+1))²
    //          = r3            < r3_right.
    //   left_eq  : r0 (=x·4^{n+1}) = r3.
    //   right_eq : r3_right = l0 (=(ofNat(2m))² ≡ goal RHS).
    // Goal: x·4^{n+1} < (ofNat(2m))²  i.e.  r0 < l0.
    // Step A: subst scaled's LHS r3 → r0 via symm left_eq (r3 = r0):
    //   motive_a u := u < r3_right.
    let motive_a = {
        let mut d = EnvDeclBuilder::child_of(&tb);
        let (u_id, u) = d.fresh_local(c.rat.clone());
        let body = c.rlt(u, r3_right.clone());
        d.finish_child(d.mk_lam(u_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let left_eq_symm = c.symm_rat(r0.clone(), r3.clone(), left_eq); // r3 = r0
    let r0_lt_r3right = c.subst_rat_prop(motive_a, r3.clone(), r0.clone(), left_eq_symm, scaled);
    // Step B: subst RHS r3_right → l0 via right_eq (r3_right = l0):
    //   motive_b v := r0 < v.
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
        env.init_algebra_nnreal_sqrt_upper()
            .expect("init_algebra_nnreal_sqrt_upper");
        env.init_algebra_nnreal_sqrt_upper().expect("idempotent");
        env
    }

    #[test]
    fn test_zero_lt_ofnat_four_kernel_checks() {
        let env = env();
        let nm = Name::from_string("Rat.zero_lt_ofNat_four");
        let info = env.get_const(&nm).expect("registered");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.zero_lt_ofNat_four must kernel-check");
    }

    #[test]
    fn test_dyadic_num_sq_lt_succ_kernel_checks() {
        let env = env();
        let nm = Name::from_string("Rat.dyadicNum_sq_lt_succ");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.dyadicNum_sq_lt_succ must kernel-check");
    }

    #[test]
    fn test_dyadic_num_sq_lt_succ_constructive_empty_closure() {
        let env = env();
        for nm in ["Rat.zero_lt_ofNat_four", "Rat.dyadicNum_sq_lt_succ"] {
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
