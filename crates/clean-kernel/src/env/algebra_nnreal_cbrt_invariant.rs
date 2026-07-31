// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — Stage B3 (2/n): the cube dyadic-floor LOWER invariant.
//!
//! # Why this module exists
//!
//! The cube-root keystone `NNReal.cbrt x · cbrt x · cbrt x = ofRat x` needs the
//! cube dyadic numerator `k_n := Rat.cbrtDyadicNum x n`
//! (`algebra_nnreal_cbrt_dyadic.rs`) to satisfy the LOWER bound
//!
//! ```text
//!   Rat.cbrtDyadicNum_cube_le :  0 ≤ x  ⟹  ∀ n, (ofNat k_n)³ ≤ x · 8^n
//! ```
//!
//! which (after dividing by `8^n`) is exactly `a_n³ ≤ x` for the scaled
//! approximation `a_n = k_n/2^n`. It is the "cube floor never overshoots" half
//! of the squeeze.
//!
//! # The CUBE vs SQUARE difference (load-bearing rework)
//!
//! The sqrt layer (`algebra_nnreal_sqrt_invariant.rs`) scales the IH by `4`:
//! `(ofNat 2k)² = ofNat 4 · (ofNat k)²`. The cube layer scales by `8`:
//!
//! ```text
//!   (ofNat 2k)³ = ofNat 8 · (ofNat k)³                       (cube_scale_eq)
//!   x · 8^{n+1} = ofNat 8 · (x · 8^n)                        (powNat_succ defeq + regroup)
//! ```
//!
//! The cube scaling identity is the genuinely-new arithmetic: from
//! `ofNat 2k = ofNat 2 · ofNat k` (`ofNat_mul`), the cube
//! `(of2·ofk)·(of2·ofk)·(of2·ofk)` regroups via TWO `mul_mul_mul_comm` steps
//! into `((of2·of2)·of2)·((ofk·ofk)·ofk)`, and `(of2·of2)·of2 = ofNat 8` via
//! two `ofNat_mul` (`2·2=4`, `4·2=8`).
//!
//! # Proof (Nat.rec over n with a Prop motive; mirrors the sqrt invariant)
//!
//! - BASE `n = 0`: `cbrtDyadicNum x 0 ≡ 0`, `cbrtDyadicPow8 0 ≡ Rat.one`, so the
//!   goal is `((ofNat 0·ofNat 0)·ofNat 0) ≤ x · 1`. `Rat.zero_mul`+`Rat.mul_one`
//!   collapse the LHS to `0` and the RHS to `x`; transport `0 ≤ x`.
//! - STEP `P n → P (n+1)`: dependent `Bool.rec.{0}` on the cube digit test.
//!     * TRUE minor: `Rat.le_of_ble_eq_true` directly.
//!     * FALSE minor (`Bool.rec ≡ 2k`): scale the IH by 8 via `cube_scale_eq` +
//!       the RHS regroup + `Rat.mul_le_mul_of_nonneg_left (ofNat 8)` with
//!       `0 ≤ ofNat 8` from `Rat.ofNat_le_ofNat_of_le 0 8 (Nat.zero_le 8)`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the cube lower invariant.
pub(crate) struct CbrtInvConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    nat_zero_le: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_ofnat: Expr,
    rat_cbrt_num: Expr,
    rat_cbrt_pow8: Expr,
    rat_ble: Expr,
    bool_ty: Expr,
    bool_true: Expr,
    bool_false: Expr,
    rat_zero_mul: Expr,
    rat_mul_one: Expr,
    rat_mul_assoc: Expr,
    rat_mul_comm: Expr,
    rat_mul_mul_mul_comm: Expr,
    rat_mul_le_left: Expr,
    rat_ofnat_mul: Expr,
    rat_ofnat_le_ofnat: Expr,
    rat_le_of_ble_eq_true: Expr,
    // Recursors / Eq toolkit (Rat is Sort 1).
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

impl CbrtInvConsts {
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
            nat_zero_le: k("Nat.zero_le"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            rat_ofnat: k("Rat.ofNat"),
            rat_cbrt_num: k("Rat.cbrtDyadicNum"),
            rat_cbrt_pow8: k("Rat.cbrtDyadicPow8"),
            rat_ble: k("Rat.ble"),
            bool_ty: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            rat_zero_mul: k("Rat.zero_mul"),
            rat_mul_one: k("Rat.mul_one"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            rat_mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            rat_ofnat_mul: k("Rat.ofNat_mul"),
            rat_ofnat_le_ofnat: k("Rat.ofNat_le_ofNat_of_le"),
            rat_le_of_ble_eq_true: k("Rat.le_of_ble_eq_true"),
            nat_rec_prop: Expr::const_(Name::from_string("Nat.rec"), vec![l0.clone()]),
            bool_rec_nat: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            bool_rec_prop: Expr::const_(Name::from_string("Bool.rec"), vec![l0]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            // `Eq.subst.{u}`; α = Rat : Sort 1.
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
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
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
    /// `(a · a) · a`.
    fn cube_expr(&self, a: Expr) -> Expr {
        let sq = self.rmul(a.clone(), a.clone());
        self.rmul(sq, a)
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
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `@congrArg Rat Rat a b f h : Eq Rat (f a)(f b)`.
    fn congr_rat(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg11.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b` (motive into Prop).
    fn subst_rat_prop(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst_prop.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `Rat.ofNat_mul m n : Eq Rat (ofNat (m·n)) (ofNat m · ofNat n)`.
    fn ofnat_mul(&self, m: Expr, n: Expr) -> Expr {
        Expr::apps(self.rat_ofnat_mul.clone(), [m, n])
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (h:b≤c)(h0:0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_left.clone(), [a, b, cc, h, h0])
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        Expr::apps(self.rat_mul_mul_mul_comm.clone(), [a, b, cc, d])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.rat_mul_assoc.clone(), [a, b, cc])
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    fn mul_comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a, b])
    }
    /// `f := fun w => w · t` (right-mul by `t`).
    fn f_right(&self, parent: &EnvDeclBuilder, t: Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.rat.clone());
        let body = self.rmul(w, t);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, self.rat.clone(), body))
    }
    /// `f := fun w => t · w` (left-mul by `t`).
    fn f_left(&self, parent: &EnvDeclBuilder, t: Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let (w_id, w) = d.fresh_local(self.rat.clone());
        let body = self.rmul(t, w);
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

mod cube_scale;

/// `pub(super)` re-exports of the smart-constructors the `cube_scale` submodule
/// needs (the underlying private helpers stay private to this file).
impl CbrtInvConsts {
    pub(super) fn s_rmul(&self, a: Expr, b: Expr) -> Expr {
        self.rmul(a, b)
    }
    pub(super) fn s_rofnat(&self, n: Expr) -> Expr {
        self.rofnat(n)
    }
    pub(super) fn s_nat_lit(&self, n: u32) -> Expr {
        self.nat_lit(n)
    }
    pub(super) fn s_nmul(&self, a: Expr, b: Expr) -> Expr {
        self.nmul(a, b)
    }
    pub(super) fn s_ofnat_mul(&self, m: Expr, n: Expr) -> Expr {
        self.ofnat_mul(m, n)
    }
    pub(super) fn s_congr(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        self.congr_rat(a, b, f, h)
    }
    pub(super) fn s_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        self.trans_rat(a, b, cc, h1, h2)
    }
    pub(super) fn s_symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.symm_rat(a, b, h)
    }
    pub(super) fn s_mmmc(&self, a: Expr, b: Expr, cc: Expr, d: Expr) -> Expr {
        self.mmmc(a, b, cc, d)
    }
    pub(super) fn s_f_right(&self, parent: &EnvDeclBuilder, t: Expr) -> Expr {
        self.f_right(parent, t)
    }
    pub(super) fn s_f_left(&self, parent: &EnvDeclBuilder, t: Expr) -> Expr {
        self.f_left(parent, t)
    }
}

impl Environment {
    /// Register `Rat.cbrtDyadicNum_cube_le`. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_cbrt_invariant(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_cbrt_dyadic()?; // cbrtDyadicNum, cbrtDyadicPow8, Rat.ble
        self.register_rat_ofnat_mul()?; // Rat.ofNat_mul
        self.register_rat_ofnat()?; // Rat.ofNat
        self.register_rat_ofnat_le_ofnat_of_le()?; // 0 ≤ ofNat 8 bridge
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.register_nat_ble_le_lemmas()?; // Nat.zero_le
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_left, etc.
        self.register_rat_mul_mul_mul_comm_theorem()?; // Rat.mul_mul_mul_comm
        self.register_rat_mul_assoc_proof()?; // Rat.mul_assoc
        self.register_rat_mul_comm_proof()?; // Rat.mul_comm
        self.rat_quotient_payoff_into_live()?; // Rat.mul_one, Rat.zero_mul, Rat.one_mul (live)
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true

        let c = CbrtInvConsts::new();
        self.register_cbrt_dyadic_num_cube_le(&c)
    }

    fn register_cbrt_dyadic_num_cube_le(&mut self, c: &CbrtInvConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cbrtDyadicNum_cube_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // motive_body x n := (ofNat (cnum x n))³ ≤ (x · 8^n).
        let motive_body = |x: &Expr, n: &Expr| -> Expr {
            c.rle(
                c.cube_ofnat(c.cnum(x, n.clone())),
                c.rmul(x.clone(), c.pow8(n.clone())),
            )
        };

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let h_ty = c.rle(c.rat_zero.clone(), x.clone());
            let (h_id, _h) = b.fresh_local(h_ty.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ib.fresh_local(c.nat.clone());
                let body = motive_body(&x, &n);
                ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, inner);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = build_invariant_value(c, &motive_body);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// The full proof term: `fun x h => Nat.rec motive base step`.
fn build_invariant_value(c: &CbrtInvConsts, motive_body: &dyn Fn(&Expr, &Expr) -> Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let h_ty = c.rle(c.rat_zero.clone(), x.clone());
    let (h_id, h) = b.fresh_local(h_ty.clone());

    // motive : fun (n:Nat) => (ofNat (cnum x n))³ ≤ x·8^n.
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = m.fresh_local(c.nat.clone());
        let body = motive_body(&x, &n);
        m.finish_child(m.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
    };

    let base = build_base(c, &b, &x, &h);
    let step = build_step(c, &b, &x);

    let rec = Expr::apps(c.nat_rec_prop.clone(), [motive, base, step]);
    let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, rec);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// BASE: `((ofNat 0·ofNat 0)·ofNat 0) ≤ x · 1`. (cnum x 0 ≡ 0, pow8 0 ≡ 1.)
fn build_base(c: &CbrtInvConsts, parent: &EnvDeclBuilder, x: &Expr, h: &Expr) -> Expr {
    let b = EnvDeclBuilder::child_of(parent);
    let of0 = c.rofnat(c.nat_zero.clone());
    let lhs = c.cube_expr(of0.clone()); // (of0·of0)·of0
    let rhs = c.rmul(x.clone(), c.rat_one.clone()); // x · 1

    // e_lhs : ((of0·of0)·of0) = Rat.zero.
    //   inner of0·of0 = 0 via Rat.zero_mul of0 (of0 ≡ Rat.zero defeq);
    //   then (0)·of0 = 0 via Rat.zero_mul of0; chain with congrArg.
    let zero = c.rat_zero.clone();
    let sq0 = c.rmul(of0.clone(), of0.clone());
    // e_inner : (of0·of0) = 0.
    let e_inner = Expr::app(c.rat_zero_mul.clone(), of0.clone());
    // congr (· · of0) e_inner : (of0·of0)·of0 = 0·of0.
    let f_r = c.f_right(&b, of0.clone());
    let s1 = c.congr_rat(sq0.clone(), zero.clone(), f_r, e_inner);
    let zero_of0 = c.rmul(zero.clone(), of0.clone());
    // e_zero_of0 : 0·of0 = 0.
    let e_zero_of0 = Expr::app(c.rat_zero_mul.clone(), of0.clone());
    // e_lhs : lhs = 0  (s1 ; e_zero_of0).
    let e_lhs = c.trans_rat(lhs.clone(), zero_of0.clone(), zero.clone(), s1, e_zero_of0);

    // e_rhs : (x · 1) = x   via Rat.mul_one x.
    let e_rhs = Expr::app(c.rat_mul_one.clone(), x.clone());

    // Step 1: from h : 0 ≤ x, get `lhs ≤ x` by subst along symm e_lhs (0 → lhs).
    let motive_l = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (l_id, l) = d.fresh_local(c.rat.clone());
        let body = c.rle(l, x.clone());
        d.finish_child(d.mk_lam(l_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let e_lhs_symm = c.symm_rat(lhs.clone(), zero.clone(), e_lhs); // 0 = lhs
    let lhs_le_x = c.subst_rat_prop(motive_l, zero.clone(), lhs.clone(), e_lhs_symm, h.clone());

    // Step 2: from `lhs ≤ x`, get `lhs ≤ rhs` by subst along symm e_rhs (x → rhs).
    let motive_r = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (r_id, r) = d.fresh_local(c.rat.clone());
        let body = c.rle(lhs.clone(), r);
        d.finish_child(d.mk_lam(r_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let e_rhs_symm = c.symm_rat(rhs.clone(), x.clone(), e_rhs); // x = rhs
    let body = c.subst_rat_prop(motive_r, x.clone(), rhs.clone(), e_rhs_symm, lhs_le_x);
    b.finish_child(body)
}

/// STEP: `fun (n:Nat) (ih : P n) => P (n+1)`.
fn build_step(c: &CbrtInvConsts, parent: &EnvDeclBuilder, x: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = b.fresh_local(c.nat.clone());

    // ih : (ofNat (cnum x n))³ ≤ x · 8^n.
    let kk = c.cnum(x, n.clone()); // k := cnum x n
    let ih_ty = c.rle(
        c.cube_ofnat(kk.clone()),
        c.rmul(x.clone(), c.pow8(n.clone())),
    );
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let test = c.digit_test(x, &kk, &n);
    let rhs_succ = c.rmul(x.clone(), c.pow8(c.succ(n.clone()))); // x·8^{n+1}

    // motive : fun (z:Bool) => Eq Bool test z → (ofNat (Bool.rec _ (2k)(2k+1) z))³ ≤ x·8^{n+1}.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = mb.fresh_local(c.bool_ty.clone());
        let heq_ty = c.eq_bool(test.clone(), z.clone());
        let (heq_id, _heq) = mb.fresh_local(heq_ty.clone());
        let num_z = c.bool_rec_num(&mb, &kk, z.clone());
        let concl = c.rle(c.cube_ofnat(num_z), rhs_succ.clone());
        let body = mb.mk_pi(heq_id, BinderInfo::Default, heq_ty, concl);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.bool_ty.clone(), body))
    };

    // FALSE minor: scale IH by 8.
    let false_minor = build_false_minor(c, &b, x, &n, &kk, &ih);
    // TRUE minor: le_of_ble_eq_true.
    let true_minor = {
        let mut tb = EnvDeclBuilder::child_of(&b);
        let heq_ty = c.eq_bool(test.clone(), c.bool_true.clone());
        let (heq_id, heq) = tb.fresh_local(heq_ty.clone());
        let two_k = c.nmul(c.nat_lit(2), kk.clone());
        let two_k1 = c.nadd(two_k, c.nat_lit(1));
        let cube = c.cube_ofnat(two_k1);
        let body = Expr::apps(
            c.rat_le_of_ble_eq_true.clone(),
            [cube, rhs_succ.clone(), heq],
        );
        let lam = tb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
        tb.finish_child(lam)
    };

    let rec_app = Expr::apps(
        c.bool_rec_prop.clone(),
        [motive, false_minor, true_minor, test.clone()],
    );
    let applied = Expr::app(rec_app, c.refl_bool(test.clone()));

    let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, applied);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish_child(e)
}

/// FALSE minor: `fun (heq) => (ofNat 2k)³ ≤ x·8^{n+1}` by scaling the IH by 8.
fn build_false_minor(
    c: &CbrtInvConsts,
    parent: &EnvDeclBuilder,
    x: &Expr,
    n: &Expr,
    kk: &Expr,
    ih: &Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let test = c.digit_test(x, kk, n);
    let heq_ty = c.eq_bool(test, c.bool_false.clone());
    let (heq_id, _heq) = fb.fresh_local(heq_ty.clone());

    let of8 = c.rofnat(c.nat_lit(8));
    let ofk = c.rofnat(kk.clone());
    let two_k = c.nmul(c.nat_lit(2), kk.clone());
    let of_2k = c.rofnat(two_k.clone());
    let cube_k = c.cube_expr(ofk.clone()); // (ofNat k)³
    let cube_2k = c.cube_expr(of_2k.clone()); // (ofNat 2k)³ (the goal LHS)
    let pow8n = c.pow8(n.clone());
    let x_pow = c.rmul(x.clone(), pow8n.clone()); // x·8^n

    // 0 ≤ ofNat 8.
    let zero_le_8 = Expr::apps(
        c.rat_ofnat_le_ofnat.clone(),
        [
            c.nat_zero.clone(),
            c.nat_lit(8),
            Expr::app(c.nat_zero_le.clone(), c.nat_lit(8)),
        ],
    );

    // scaled : ofNat 8 · (ofNat k)³ ≤ ofNat 8 · (x·8^n).
    let scaled = c.mul_le_left(
        of8.clone(),
        cube_k.clone(),
        x_pow.clone(),
        ih.clone(),
        zero_le_8,
    );

    // LEFT equality: (ofNat 2k)³ = ofNat 8 · (ofNat k)³   (the cube scale).
    let rhs_scaled_l = c.rmul(of8.clone(), cube_k.clone()); // ofNat 8 · (ofNat k)³
    let left_eq = c.cube_scale_eq(&fb, kk);

    // RIGHT equality: x·8^{n+1} = ofNat 8 · (x·8^n)   (powNat_succ defeq + regroup).
    //   8^{n+1} ≡ ofNat8·8^n defeq, so x·8^{n+1} ≡ x·(ofNat8·8^n) =: r0.
    let pow8_succ_unfold = c.rmul(of8.clone(), pow8n.clone()); // o8·8^n  (≡ 8^{n+1})
    let r0 = c.rmul(x.clone(), pow8_succ_unfold.clone()); // x·(o8·8^n)  ≡ x·8^{n+1}
                                                          // r0 = (x·o8)·p  via symm (mul_assoc x o8 p)
    let assoc1 = c.mul_assoc(x.clone(), of8.clone(), pow8n.clone());
    let xo8 = c.rmul(x.clone(), of8.clone());
    let r1 = c.rmul(xo8.clone(), pow8n.clone());
    let assoc1_symm = c.symm_rat(r1.clone(), r0.clone(), assoc1);
    // (x·o8) = (o8·x) via mul_comm.
    let comm1 = c.mul_comm(x.clone(), of8.clone()); // x·o8 = o8·x
    let o8x = c.rmul(of8.clone(), x.clone());
    let f_pp = c.f_right(&fb, pow8n.clone());
    let s_r2 = c.congr_rat(xo8.clone(), o8x.clone(), f_pp, comm1);
    let r2 = c.rmul(o8x.clone(), pow8n.clone());
    // r2 = o8·(x·p) via mul_assoc o8 x p.
    let assoc2 = c.mul_assoc(of8.clone(), x.clone(), pow8n.clone()); // (o8·x)·p = o8·(x·p)
    let r3 = c.rmul(of8.clone(), x_pow.clone()); // o8·(x·p)
    let r0_r2 = c.trans_rat(r0.clone(), r1.clone(), r2.clone(), assoc1_symm, s_r2);
    let right_eq = c.trans_rat(r0.clone(), r2.clone(), r3.clone(), r0_r2, assoc2);

    // scaled : rhs_scaled_l ≤ r3.  Goal: cube_2k ≤ r0 (defeq to x·8^{n+1}).
    // Step A: subst scaled LHS along symm left_eq (rhs_scaled_l → cube_2k).
    let motive_a = {
        let mut d = EnvDeclBuilder::child_of(&fb);
        let (u_id, u) = d.fresh_local(c.rat.clone());
        let body = c.rle(u, r3.clone());
        d.finish_child(d.mk_lam(u_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let left_eq_symm = c.symm_rat(cube_2k.clone(), rhs_scaled_l.clone(), left_eq); // rhs_scaled_l = cube_2k
    let l0_le_r3 = c.subst_rat_prop(
        motive_a,
        rhs_scaled_l.clone(),
        cube_2k.clone(),
        left_eq_symm,
        scaled,
    );
    // Step B: subst RHS along symm right_eq (r3 → r0).
    let motive_b = {
        let mut d = EnvDeclBuilder::child_of(&fb);
        let (v_id, v) = d.fresh_local(c.rat.clone());
        let body = c.rle(cube_2k.clone(), v);
        d.finish_child(d.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let right_eq_symm = c.symm_rat(r0.clone(), r3.clone(), right_eq); // r3 = r0
    let l0_le_r0 = c.subst_rat_prop(motive_b, r3.clone(), r0.clone(), right_eq_symm, l0_le_r3);

    let lam = fb.mk_lam(heq_id, BinderInfo::Default, heq_ty, l0_le_r0);
    fb.finish_child(lam)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_cbrt_invariant()
            .expect("init_algebra_nnreal_cbrt_invariant");
        env.init_algebra_nnreal_cbrt_invariant()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_cbrt_dyadic_num_cube_le_kernel_checks() {
        let env = env();
        let nm = Name::from_string("Rat.cbrtDyadicNum_cube_le");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.cbrtDyadicNum_cube_le must kernel-check");
    }

    #[test]
    fn test_cbrt_dyadic_num_cube_le_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("Rat.cbrtDyadicNum_cube_le");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }
}
