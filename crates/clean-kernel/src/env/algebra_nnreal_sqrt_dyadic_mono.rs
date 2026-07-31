// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage C (Component A, rung 1): dyadic-floor numerator
//! MONOTONICITY in the radicand.
//!
//! # Why this module exists
//!
//! `NNReal.sqrtRat` is monotone (`x ≤ y → sqrtRat x ≤ sqrtRat y`) — the bridge
//! that lets the half-power charge `x^{3/2} ≤ ε^{1/2}·x` close through the
//! cleaner sqrt-monotone route (designs §9.3/§9.4). Pointwise, the dyadic
//! approximation `a_n = k_n/2^n` is monotone in the radicand BECAUSE its
//! integer numerator is:
//!
//! ```text
//!   Rat.dyadicNum_mono :
//!     0 ≤ x → x ≤ y → ∀ n, Nat.le (Rat.dyadicNum x n) (Rat.dyadicNum y n)
//! ```
//!
//! # Proof (Nat.rec over n; the digit step splits on the IH trichotomy)
//!
//! Let `kx := dyadicNum x n`, `ky := dyadicNum y n`, IH : `kx ≤ ky`.
//!
//! - BASE `n = 0`: both numerators are `0`, so `@Nat.le.refl Nat.zero`.
//! - STEP: goal `Nat.le kx_{n+1} ky_{n+1}`. The landed digit bounds give
//!   `kx_{n+1} ≤ succ(2·kx)` (`dyadicNum_succ_le_two_mul_succ`) and
//!   `2·ky ≤ ky_{n+1}` (`dyadicNum_two_mul_le_succ`). Split the IH via
//!   `Nat.lt_or_eq_of_le kx ky IH`:
//!     * `kx < ky` (`Nat.le (succ kx) ky`): then `succ(2·kx) ≤ 2·ky`
//!       (`Nat.mul_le_mul_left (succ kx) ky 2` ⟹ `2·(succ kx) = succ(succ 2kx)
//!       ≤ 2·ky`, then `Nat.le.step` peels one `succ`), so the chain
//!       `kx_{n+1} ≤ succ(2kx) ≤ 2ky ≤ ky_{n+1}` closes. NO digit-test reasoning.
//!     * `kx = ky =: k`: the only failure mode is `kx_{n+1} = 2k+1`,
//!       `ky_{n+1} = 2k`. That needs x's digit TRUE while y's is FALSE, which is
//!       impossible: `x·4^{n+1} ≤ y·4^{n+1}` makes x's test `(2k+1)² ≤ x·4^{n+1}`
//!       imply y's `(2k+1)² ≤ y·4^{n+1}`. Realized by a NESTED dependent
//!       `Bool.rec.{0}` (outer on `bley`, inner on `blex`); the impossible
//!       `(blex=true, bley=false)` corner derives `False` via
//!       `Rat.le_of_ble_eq_true` → `Rat.le_trans` (scaling `x≤y` by `4^{n+1}≥0`)
//!       → `Eq.subst` along `heq` to y's LHS → `Rat.ble_eq_true_of_le` →
//!       `Bool.noConfusion` on `true = false`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for dyadic numerator monotonicity.
pub(crate) struct DyMonoConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    nat_le: Expr,
    nat_lt: Expr,
    nat_le_refl: Expr,
    nat_le_step: Expr,
    nat_le_trans: Expr,
    nat_succ_le_succ: Expr,
    nat_mul_le_mul_left: Expr,
    nat_lt_or_eq_of_le: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    rat_mul: Expr,
    rat_ofnat: Expr,
    rat_ble: Expr,
    rat_dyadic_num: Expr,
    rat_dyadic_pow4: Expr,
    dnum_succ_le: Expr,
    dnum_two_mul_le: Expr,
    rat_le_trans: Expr,
    rat_le_of_ble_eq_true: Expr,
    rat_ble_eq_true_of_le: Expr,
    rat_mul_le_right: Expr,
    rat_zero_lt_pow4: Expr,
    rat_lt_iff: Expr,
    bool_ty: Expr,
    bool_true: Expr,
    bool_false: Expr,
    false_ty: Expr,
    bool_rec_nat: Expr,
    bool_rec_prop: Expr,
    nat_rec_prop: Expr,
    or_c: Expr,
    or_rec: Expr,
    and_c: Expr,
    and_left: Expr,
    iff_mp: Expr,
    not_c: Expr,
    false_elim: Expr,
    bool_no_confusion: Expr,
    // Eq toolkit: Bool (universe 1), Nat (universe 1), Rat (universe 1).
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
    eq_trans1: Expr,
    #[cfg(test)]
    congr_arg11: Expr,
}

impl DyMonoConsts {
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
            nat_le: k("Nat.le"),
            nat_lt: k("Nat.lt"),
            nat_le_refl: k("Nat.le.refl"),
            nat_le_step: k("Nat.le.step"),
            nat_le_trans: k("Nat.le_trans"),
            nat_succ_le_succ: k("Nat.succ_le_succ"),
            nat_mul_le_mul_left: k("Nat.mul_le_mul_left"),
            nat_lt_or_eq_of_le: k("Nat.lt_or_eq_of_le"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            rat_mul: k("Rat.mul"),
            rat_ofnat: k("Rat.ofNat"),
            rat_ble: k("Rat.ble"),
            rat_dyadic_num: k("Rat.dyadicNum"),
            rat_dyadic_pow4: k("Rat.dyadicPow4"),
            dnum_succ_le: k("Rat.dyadicNum_succ_le_two_mul_succ"),
            dnum_two_mul_le: k("Rat.dyadicNum_two_mul_le_succ"),
            rat_le_trans: k("Rat.le_trans"),
            rat_le_of_ble_eq_true: k("Rat.le_of_ble_eq_true"),
            rat_ble_eq_true_of_le: k("Rat.ble_eq_true_of_le"),
            rat_mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            rat_zero_lt_pow4: k("Rat.zero_lt_dyadicPow4"),
            rat_lt_iff: k("Rat.lt_iff_le_not_le"),
            bool_ty: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            false_ty: k("False"),
            bool_rec_nat: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            bool_rec_prop: Expr::const_(Name::from_string("Bool.rec"), vec![l0.clone()]),
            nat_rec_prop: Expr::const_(Name::from_string("Nat.rec"), vec![l0.clone()]),
            or_c: k("Or"),
            or_rec: k("Or.rec"),
            and_c: k("And"),
            and_left: k("And.left"),
            iff_mp: k("Iff.mp"),
            not_c: k("Not"),
            false_elim: Expr::const_(Name::from_string("False.elim"), vec![l0.clone()]),
            bool_no_confusion: Expr::const_(Name::from_string("Bool.noConfusion"), vec![l0]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            #[cfg(test)]
            congr_arg11: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    // ── Nat constructors ──
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
    fn nle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    fn nlt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_lt.clone(), [a, b])
    }
    /// `Nat.le.refl n : Nat.le n n`.
    fn nle_refl(&self, n: Expr) -> Expr {
        Expr::app(self.nat_le_refl.clone(), n)
    }
    /// `Nat.le.step a b h : Nat.le a (succ b)` from `h : Nat.le a b`.
    fn nle_step(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.nat_le_step.clone(), [a, b, h])
    }
    /// `Nat.le_trans a b c hab hbc : Nat.le a c`.
    fn nle_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.nat_le_trans.clone(), [a, b, cc, hab, hbc])
    }
    /// `Nat.succ_le_succ n m h : Nat.le (succ n)(succ m)` from `h : Nat.le n m`.
    fn nsucc_le_succ(&self, n: Expr, m: Expr, h: Expr) -> Expr {
        Expr::apps(self.nat_succ_le_succ.clone(), [n, m, h])
    }
    /// `Nat.mul_le_mul_left a b c h : Nat.le (c·a)(c·b)` from `h : Nat.le a b`.
    fn nmul_le_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr) -> Expr {
        Expr::apps(self.nat_mul_le_mul_left.clone(), [a, b, cc, h])
    }

    // ── Rat / dyadic constructors ──
    fn rmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
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
    /// `(ofNat m)² := Rat.mul (ofNat m)(ofNat m)`.
    fn sq_ofnat(&self, m: Expr) -> Expr {
        let r = self.rofnat(m);
        self.rmul(r.clone(), r)
    }
    /// The digit test `Rat.ble ((ofNat (2k+1))²) (x·4^{n+1})`.
    fn digit_test(&self, x: &Expr, kk: &Expr, n: &Expr) -> Expr {
        let two_k = self.nmul(self.nat_lit(2), kk.clone());
        let two_k1 = self.nadd(two_k, self.nat_lit(1));
        let lhs = self.sq_ofnat(two_k1);
        let rhs = self.rmul(x.clone(), self.pow4(self.succ(n.clone())));
        Expr::apps(self.rat_ble.clone(), [lhs, rhs])
    }
    /// `dyadicNum x (succ n)`'s defining `Bool.rec` value at explicit `b`:
    ///   `@Bool.rec.{1} (fun _=>Nat) (2k) (2k+1) b`  where `k := dnum x n`.
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

    fn eq_bool(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.bool_ty.clone(), x, y])
    }
    fn eq_nat(&self, x: Expr, y: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nat.clone(), x, y])
    }
    fn refl_bool(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.bool_ty.clone(), x])
    }
    /// `Eq.symm.{1} Bool a b h : Eq Bool b a`.
    fn symm_bool(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.bool_ty.clone(), a, b, h])
    }
    /// `Eq.trans.{1} Bool a b c hab hbc : Eq Bool a c`.
    fn trans_bool(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [self.bool_ty.clone(), a, b, cc, hab, hbc],
        )
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h : motive b`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@congrArg Nat Rat a b f h : Eq Rat (f a)(f b)`.
    fn congr_nat_rat(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        let congr = Expr::const_(
            Name::from_string("congrArg"),
            vec![Level::succ(Level::zero()), Level::succ(Level::zero())],
        );
        Expr::apps(congr, [self.nat.clone(), self.rat.clone(), a, b, f, h])
    }
    /// `Rat.le_trans a b c hab hbc : Rat.le a c`.
    fn rle_trans(&self, a: Expr, b: Expr, cc: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(self.rat_le_trans.clone(), [a, b, cc, hab, hbc])
    }
    /// `Rat.le_of_ble_eq_true a b h : Rat.le a b` from `h : ble a b = true`.
    fn le_of_ble_true(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_le_of_ble_eq_true.clone(), [a, b, h])
    }
    /// `Rat.ble_eq_true_of_le a b h : Eq Bool (ble a b) true` from `h : a ≤ b`.
    fn ble_true_of_le(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_ble_eq_true_of_le.clone(), [a, b, h])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c hbc h0 : Rat.le (b·a)(c·a)`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, hbc: Expr, h0: Expr) -> Expr {
        Expr::apps(self.rat_mul_le_right.clone(), [a, b, cc, hbc, h0])
    }
    /// `0 ≤ dyadicPow4 n` from `Rat.zero_lt_dyadicPow4 n` via the lt→le idiom
    /// `And.left (Iff.mp (Rat.lt_iff_le_not_le 0 (pow4 n)) hlt)`.
    fn zero_le_pow4(&self, n: Expr) -> Expr {
        let pow4 = self.pow4(n.clone());
        let hlt = Expr::app(self.rat_zero_lt_pow4.clone(), n);
        let le_0_p = self.rle(self.rat_zero.clone(), pow4.clone());
        let not_le_p_0 = Expr::app(
            self.not_c.clone(),
            self.rle(pow4.clone(), self.rat_zero.clone()),
        );
        let iff_e = Expr::apps(
            self.rat_lt_iff.clone(),
            [self.rat_zero.clone(), pow4.clone()],
        );
        let lt_0_p = Expr::apps(self.rat_lt.clone(), [self.rat_zero.clone(), pow4]);
        let and_e = Expr::apps(self.and_c.clone(), [le_0_p.clone(), not_le_p_0.clone()]);
        // Iff.mp (lt 0 p)(And (le 0 p)(¬le p 0)) iff_e hlt : And ...
        let mp = Expr::apps(self.iff_mp.clone(), [lt_0_p, and_e, iff_e, hlt]);
        // And.left (le 0 p)(¬le p 0) mp : le 0 p.
        Expr::apps(self.and_left.clone(), [le_0_p, not_le_p_0, mp])
    }
}

impl Environment {
    /// Register `Rat.dyadicNum_mono`. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_sqrt_dyadic_mono(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_sqrt_mono()?; // dyadicNum, pow4, both digit bounds
        self.init_algebra_nnreal_sqrt_squeeze()?; // Rat.zero_lt_dyadicPow4
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?; // Bool, Bool.rec, Bool.noConfusion
        self.init_le()?; // Nat.le, Nat.le.refl, Nat.le.step
        self.init_or()?; // Or, Or.rec
        self.init_and()?; // And, And.left
        self.init_iff()?; // Iff, Iff.mp
        self.init_true_false()?; // False, False.elim
        self.init_nat_lt_or_eq_of_le()?; // Nat.lt_or_eq_of_le (constructive)
        self.register_nat_arith_order_proofs()?; // Nat.mul_le_mul_left
        self.init_nat_top_level_ordering()?; // Nat.succ_le_succ
        self.register_nat_le_trans_proof()?; // Nat.le_trans
        self.register_rat_minmax_proofs()?; // Rat.ble, Rat.le_of_ble_eq_true, Rat.ble_eq_true_of_le
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_right
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.init_rat_linear_order()?; // Rat.lt_iff_le_not_le

        let c = DyMonoConsts::new();
        self.register_dyadic_num_mono(&c)
    }

    fn register_dyadic_num_mono(&mut self, c: &DyMonoConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.dyadicNum_mono");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // type: ∀ x y, 0≤x → x≤y → ∀ n, Nat.le (dyadicNum x n)(dyadicNum y n).
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, x) = b.fresh_local(c.rat.clone());
            let (y_id, y) = b.fresh_local(c.rat.clone());
            let h0_ty = c.rle(c.rat_zero.clone(), x.clone());
            let (h0_id, _h0) = b.fresh_local(h0_ty.clone());
            let hxy_ty = c.rle(x.clone(), y.clone());
            let (hxy_id, _hxy) = b.fresh_local(hxy_ty.clone());
            let inner = {
                let mut ib = EnvDeclBuilder::child_of(&b);
                let (n_id, n) = ib.fresh_local(c.nat.clone());
                let body = c.nle(c.dnum(&x, n.clone()), c.dnum(&y, n.clone()));
                ib.finish_child(ib.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body))
            };
            let e = b.mk_pi(hxy_id, BinderInfo::Default, hxy_ty, inner);
            let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, c.rat.clone(), e);
            b.finish(e)
        };

        let value = build_mono_value(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// `fun x y h0 hxy => Nat.rec motive base step`.
fn build_mono_value(c: &DyMonoConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let (y_id, y) = b.fresh_local(c.rat.clone());
    let h0_ty = c.rle(c.rat_zero.clone(), x.clone());
    let (h0_id, _h0) = b.fresh_local(h0_ty.clone());
    let hxy_ty = c.rle(x.clone(), y.clone());
    let (hxy_id, hxy) = b.fresh_local(hxy_ty.clone());

    // motive : fun (n:Nat) => Nat.le (dnum x n)(dnum y n).
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (n_id, n) = m.fresh_local(c.nat.clone());
        let body = c.nle(c.dnum(&x, n.clone()), c.dnum(&y, n.clone()));
        m.finish_child(m.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), body))
    };

    // BASE n=0: dnum _ 0 ≡ 0, so goal ≡ Nat.le 0 0 := Nat.le.refl 0.
    let base = c.nle_refl(c.nat_zero.clone());

    let step = build_step(c, &b, &x, &y, &hxy);

    let rec = Expr::apps(c.nat_rec_prop.clone(), [motive, base, step]);
    let e = b.mk_lam(hxy_id, BinderInfo::Default, hxy_ty, rec);
    let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
    let e = b.mk_lam(y_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(x_id, BinderInfo::Default, c.rat.clone(), e);
    b.finish(e)
}

/// STEP: `fun (n:Nat)(ih : kx ≤ ky) => Nat.le kx_{n+1} ky_{n+1}`.
fn build_step(c: &DyMonoConsts, parent: &EnvDeclBuilder, x: &Expr, y: &Expr, hxy: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let kx = c.dnum(x, n.clone());
    let ky = c.dnum(y, n.clone());
    let ih_ty = c.nle(kx.clone(), ky.clone());
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    // kx_{n+1}, ky_{n+1} as surface dyadicNum applications.
    let kx_s = c.dnum(x, c.succ(n.clone()));
    let ky_s = c.dnum(y, c.succ(n.clone()));
    let goal = c.nle(kx_s.clone(), ky_s.clone());

    let two_kx = c.nmul(c.nat_lit(2), kx.clone());
    let two_ky = c.nmul(c.nat_lit(2), ky.clone());
    let succ_two_kx = c.succ(two_kx.clone());
    let succ_two_ky = c.succ(two_ky.clone());

    // Landed digit bounds.
    //   b1 : Nat.le kx_{n+1} (succ 2kx).
    let b1 = Expr::apps(c.dnum_succ_le.clone(), [x.clone(), n.clone()]);
    //   b2y : Nat.le (2ky) ky_{n+1}.
    let b2y = Expr::apps(c.dnum_two_mul_le.clone(), [y.clone(), n.clone()]);

    // disj : Or (Nat.lt kx ky)(Eq kx ky)  := Nat.lt_or_eq_of_le kx ky ih.
    let lt_kx_ky = c.nlt(kx.clone(), ky.clone());
    let eq_kx_ky = c.eq_nat(kx.clone(), ky.clone());
    let disj = Expr::apps(
        c.nat_lt_or_eq_of_le.clone(),
        [kx.clone(), ky.clone(), ih.clone()],
    );

    // ── LEFT minor: kx < ky (≡ Nat.le (succ kx) ky). ──
    let left = {
        let mut l = EnvDeclBuilder::child_of(&b);
        let (hlt_id, hlt) = l.fresh_local(lt_kx_ky.clone());
        // mid_raw : Nat.le (Nat.mul 2 (succ kx))(Nat.mul 2 ky)
        //   ≡ Nat.le (succ(succ 2kx))(2ky) by Nat.mul reduction on (succ kx).
        let mid_raw = c.nmul_le_left(c.succ(kx.clone()), ky.clone(), c.nat_lit(2), hlt);
        // step_up : Nat.le (succ 2kx)(succ(succ 2kx)).
        let succ2_two_kx = c.succ(succ_two_kx.clone());
        let step_up = c.nle_step(
            succ_two_kx.clone(),
            succ_two_kx.clone(),
            c.nle_refl(succ_two_kx.clone()),
        );
        // mid : Nat.le (succ 2kx)(2ky) := le_trans (succ 2kx)(succ(succ 2kx))(2ky) step_up mid_raw.
        let mid = c.nle_trans(
            succ_two_kx.clone(),
            succ2_two_kx,
            two_ky.clone(),
            step_up,
            mid_raw,
        );
        // chain1 : Nat.le kx_{n+1} (2ky) := le_trans kx_{n+1} (succ 2kx)(2ky) b1 mid.
        let chain1 = c.nle_trans(
            kx_s.clone(),
            succ_two_kx.clone(),
            two_ky.clone(),
            b1.clone(),
            mid,
        );
        // proof : Nat.le kx_{n+1} ky_{n+1} := le_trans kx_{n+1} (2ky) ky_{n+1} chain1 b2y.
        let proof = c.nle_trans(
            kx_s.clone(),
            two_ky.clone(),
            ky_s.clone(),
            chain1,
            b2y.clone(),
        );
        l.finish_child(l.mk_lam(hlt_id, BinderInfo::Default, lt_kx_ky.clone(), proof))
    };

    // ── RIGHT minor: kx = ky. ──
    let right = build_eq_minor(
        c,
        &b,
        x,
        y,
        hxy,
        &n,
        &kx,
        &ky,
        &eq_kx_ky,
        &kx_s,
        &b1,
        &b2y,
        &two_kx,
        &two_ky,
        &succ_two_kx,
        &succ_two_ky,
        &ih,
    );

    // @Or.rec (lt)(eq) or_motive left right disj.
    let or_motive = {
        let mut ob = EnvDeclBuilder::child_of(&b);
        let or_ty = Expr::apps(c.or_c.clone(), [lt_kx_ky.clone(), eq_kx_ky.clone()]);
        let (d_id, _d) = ob.fresh_local(or_ty.clone());
        ob.finish_child(ob.mk_lam(d_id, BinderInfo::Default, or_ty, goal.clone()))
    };
    let applied = Expr::apps(
        c.or_rec.clone(),
        [lt_kx_ky, eq_kx_ky, or_motive, left, right, disj],
    );

    let e = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, applied);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish_child(e)
}

/// RIGHT minor of the IH trichotomy: `fun (heq : Eq kx ky) => Nat.le kx_{n+1} ky_{n+1}`.
///
/// Nested dependent `Bool.rec.{0}`: outer reflects `bley` (exposing `ky_{n+1}`),
/// inner reflects `blex` (exposing `kx_{n+1}`).
#[allow(clippy::too_many_arguments)]
fn build_eq_minor(
    c: &DyMonoConsts,
    parent: &EnvDeclBuilder,
    x: &Expr,
    y: &Expr,
    hxy: &Expr,
    n: &Expr,
    kx: &Expr,
    ky: &Expr,
    eq_kx_ky: &Expr,
    kx_s: &Expr,
    b1: &Expr,
    _b2y: &Expr,
    two_kx: &Expr,
    two_ky: &Expr,
    succ_two_kx: &Expr,
    succ_two_ky: &Expr,
    ih: &Expr,
) -> Expr {
    let mut rb = EnvDeclBuilder::child_of(parent);
    let (heq_id, heq) = rb.fresh_local(eq_kx_ky.clone());

    let _blex = c.digit_test(x, kx, n);
    let bley = c.digit_test(y, ky, n);

    // OUTER motive on bley:
    //   fun z => Eq Bool bley z → Nat.le kx_{n+1} (Bool.rec _ (2ky)(2ky+1) z).
    let outer_motive = {
        let mut mb = EnvDeclBuilder::child_of(&rb);
        let (z_id, z) = mb.fresh_local(c.bool_ty.clone());
        let heqz_ty = c.eq_bool(bley.clone(), z.clone());
        let (heqz_id, _heqz) = mb.fresh_local(heqz_ty.clone());
        let kyz = c.bool_rec_num(&mb, ky, z.clone());
        let concl = c.nle(kx_s.clone(), kyz);
        let body = mb.mk_pi(heqz_id, BinderInfo::Default, heqz_ty, concl);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.bool_ty.clone(), body))
    };

    // OUTER false minor: bley ≡ false ⟹ ky_{n+1} = 2ky.
    //   fun (hbley_false : Eq Bool bley false) => [inner Bool.rec on blex].
    let outer_false = build_outer_false(
        c,
        &rb,
        x,
        y,
        hxy,
        n,
        kx,
        ky,
        &heq,
        kx_s,
        b1,
        two_kx,
        two_ky,
        succ_two_kx,
        ih,
    );

    // OUTER true minor: bley ≡ true ⟹ ky_{n+1} = succ 2ky.
    //   goal Nat.le kx_{n+1} (succ 2ky): kx_{n+1} ≤ succ 2kx ≤ succ 2ky.
    let outer_true = {
        let mut tb = EnvDeclBuilder::child_of(&rb);
        let hbley_true_ty = c.eq_bool(bley.clone(), c.bool_true.clone());
        let (ht_id, _ht) = tb.fresh_local(hbley_true_ty.clone());
        // 2kx ≤ 2ky := mul_le_mul_left kx ky 2 ih.
        let two_kx_le_two_ky = c.nmul_le_left(kx.clone(), ky.clone(), c.nat_lit(2), ih.clone());
        // succ 2kx ≤ succ 2ky := succ_le_succ (2kx)(2ky) (that).
        let succ_le = c.nsucc_le_succ(two_kx.clone(), two_ky.clone(), two_kx_le_two_ky);
        // kx_{n+1} ≤ succ 2ky := le_trans kx_{n+1} (succ 2kx)(succ 2ky) b1 succ_le.
        let proof = c.nle_trans(
            kx_s.clone(),
            succ_two_kx.clone(),
            succ_two_ky.clone(),
            b1.clone(),
            succ_le,
        );
        tb.finish_child(tb.mk_lam(ht_id, BinderInfo::Default, hbley_true_ty, proof))
    };

    // @Bool.rec.{0} outer_motive outer_false outer_true bley (Eq.refl bley).
    let rec_app = Expr::apps(
        c.bool_rec_prop.clone(),
        [outer_motive, outer_false, outer_true, bley.clone()],
    );
    let applied = Expr::app(rec_app, c.refl_bool(bley.clone()));

    rb.finish_child(rb.mk_lam(heq_id, BinderInfo::Default, eq_kx_ky.clone(), applied))
}

/// OUTER-false branch (`bley ≡ false`, `ky_{n+1} = 2ky`): inner `Bool.rec` on
/// `blex`. Goal `Nat.le kx_{n+1} (2ky)`.
#[allow(clippy::too_many_arguments)]
fn build_outer_false(
    c: &DyMonoConsts,
    parent: &EnvDeclBuilder,
    x: &Expr,
    y: &Expr,
    hxy: &Expr,
    n: &Expr,
    kx: &Expr,
    ky: &Expr,
    heq: &Expr,
    kx_s: &Expr,
    b1: &Expr,
    two_kx: &Expr,
    two_ky: &Expr,
    succ_two_kx: &Expr,
    ih: &Expr,
) -> Expr {
    let mut fb = EnvDeclBuilder::child_of(parent);
    let bley = c.digit_test(y, ky, n);
    let hbley_false_ty = c.eq_bool(bley.clone(), c.bool_false.clone());
    let (hbf_id, hbf) = fb.fresh_local(hbley_false_ty.clone());

    let blex = c.digit_test(x, kx, n);

    // INNER motive on blex:
    //   fun w => Eq Bool blex w → Nat.le (Bool.rec _ (2kx)(2kx+1) w) (2ky).
    let inner_motive = {
        let mut mb = EnvDeclBuilder::child_of(&fb);
        let (w_id, w) = mb.fresh_local(c.bool_ty.clone());
        let heqw_ty = c.eq_bool(blex.clone(), w.clone());
        let (heqw_id, _heqw) = mb.fresh_local(heqw_ty.clone());
        let kxw = c.bool_rec_num(&mb, kx, w.clone());
        let concl = c.nle(kxw, two_ky.clone());
        let body = mb.mk_pi(heqw_id, BinderInfo::Default, heqw_ty, concl);
        mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, c.bool_ty.clone(), body))
    };

    // INNER false minor: blex ≡ false ⟹ kx_{n+1} = 2kx.
    //   goal Nat.le (2kx)(2ky) := mul_le_mul_left kx ky 2 ih.
    let inner_false = {
        let mut ib = EnvDeclBuilder::child_of(&fb);
        let hblex_false_ty = c.eq_bool(blex.clone(), c.bool_false.clone());
        let (h_id, _h) = ib.fresh_local(hblex_false_ty.clone());
        let proof = c.nmul_le_left(kx.clone(), ky.clone(), c.nat_lit(2), ih.clone());
        ib.finish_child(ib.mk_lam(h_id, BinderInfo::Default, hblex_false_ty, proof))
    };

    // INNER true minor: blex ≡ true ⟹ kx_{n+1} = succ 2kx. Derive False.
    let inner_true = build_inner_true(c, &fb, x, y, hxy, n, kx, ky, heq, &hbf, two_ky, succ_two_kx);

    // @Bool.rec.{0} inner_motive inner_false inner_true blex (Eq.refl blex).
    let rec_app = Expr::apps(
        c.bool_rec_prop.clone(),
        [inner_motive, inner_false, inner_true, blex.clone()],
    );
    let applied = Expr::app(rec_app, c.refl_bool(blex.clone()));

    let _ = (kx_s, b1, two_kx);
    fb.finish_child(fb.mk_lam(hbf_id, BinderInfo::Default, hbley_false_ty, applied))
}

/// INNER-true branch (`blex ≡ true`, `bley ≡ false`, `kx = ky`): the impossible
/// corner. Goal `Nat.le (succ 2kx)(2ky)` discharged by `False.elim`.
#[allow(clippy::too_many_arguments)]
fn build_inner_true(
    c: &DyMonoConsts,
    parent: &EnvDeclBuilder,
    x: &Expr,
    y: &Expr,
    hxy: &Expr,
    n: &Expr,
    kx: &Expr,
    ky: &Expr,
    heq: &Expr,
    hbley_false: &Expr,
    two_ky: &Expr,
    succ_two_kx: &Expr,
) -> Expr {
    let mut ib = EnvDeclBuilder::child_of(parent);
    let blex = c.digit_test(x, kx, n);
    let bley = c.digit_test(y, ky, n);
    let hblex_true_ty = c.eq_bool(blex.clone(), c.bool_true.clone());
    let (ht_id, ht) = ib.fresh_local(hblex_true_ty.clone());

    // LHS squares and the scaled RHS.
    let two_kx_1 = c.nadd(c.nmul(c.nat_lit(2), kx.clone()), c.nat_lit(1));
    let two_ky_1 = c.nadd(c.nmul(c.nat_lit(2), ky.clone()), c.nat_lit(1));
    let sq_x = c.sq_ofnat(two_kx_1.clone()); // (ofNat(2kx+1))²
    let sq_y = c.sq_ofnat(two_ky_1.clone()); // (ofNat(2ky+1))²
    let pow4_succ = c.pow4(c.succ(n.clone()));
    let x_scale = c.rmul(x.clone(), pow4_succ.clone()); // x·4^{n+1}
    let y_scale = c.rmul(y.clone(), pow4_succ.clone()); // y·4^{n+1}

    // h_lhs_le_x : (ofNat(2kx+1))² ≤ x·4^{n+1}  := le_of_ble_eq_true … ht.
    let h_lhs_le_x = c.le_of_ble_true(sq_x.clone(), x_scale.clone(), ht.clone());
    // h_scale : x·4^{n+1} ≤ y·4^{n+1}  := mul_le_mul_of_nonneg_right (4^{n+1}) x y hxy (0≤4^{n+1}).
    let zero_le_pow4 = c.zero_le_pow4(c.succ(n.clone()));
    let h_scale = c.mul_le_right(
        pow4_succ.clone(),
        x.clone(),
        y.clone(),
        hxy.clone(),
        zero_le_pow4,
    );
    // h_lhs_le_y : (ofNat(2kx+1))² ≤ y·4^{n+1}  := le_trans … h_lhs_le_x h_scale.
    let h_lhs_le_y = c.rle_trans(
        sq_x.clone(),
        x_scale.clone(),
        y_scale.clone(),
        h_lhs_le_x,
        h_scale,
    );

    // Rewrite (ofNat(2kx+1))² → (ofNat(2ky+1))² along heq : kx = ky.
    //   sq_fn := fun (k:Nat) => (ofNat (2k+1))².
    let sq_fn = {
        let mut d = EnvDeclBuilder::child_of(&ib);
        let (k_id, k) = d.fresh_local(c.nat.clone());
        let two_k_1 = c.nadd(c.nmul(c.nat_lit(2), k.clone()), c.nat_lit(1));
        let body = c.sq_ofnat(two_k_1);
        d.finish_child(d.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
    };
    // congr : Eq Rat (sq_fn kx)(sq_fn ky) := congrArg sq_fn heq.  (sq_fn kx ≡ sq_x.)
    let h_sq_eq = c.congr_nat_rat(kx.clone(), ky.clone(), sq_fn, heq.clone());
    // Transport h_lhs_le_y : sq_x ≤ y_scale  to  sq_y ≤ y_scale.
    //   motive t := Rat.le t y_scale.
    let motive_le = {
        let mut d = EnvDeclBuilder::child_of(&ib);
        let (t_id, t) = d.fresh_local(c.rat.clone());
        let body = c.rle(t, y_scale.clone());
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let h_sqy_le_y = c.subst_rat(motive_le, sq_x.clone(), sq_y.clone(), h_sq_eq, h_lhs_le_y);

    // bley_true : Eq Bool bley true  := ble_eq_true_of_le sq_y y_scale h_sqy_le_y.
    let bley_true = c.ble_true_of_le(sq_y.clone(), y_scale.clone(), h_sqy_le_y);
    // true = bley (symm), then true = false (trans with hbley_false : bley = false).
    let true_eq_bley = c.symm_bool(bley.clone(), c.bool_true.clone(), bley_true);
    let true_eq_false = c.trans_bool(
        c.bool_true.clone(),
        bley.clone(),
        c.bool_false.clone(),
        true_eq_bley,
        hbley_false.clone(),
    );
    // @Bool.noConfusion.{0} False true false (true=false) : False.
    let false_proof = Expr::apps(
        c.bool_no_confusion.clone(),
        [
            c.false_ty.clone(),
            c.bool_true.clone(),
            c.bool_false.clone(),
            true_eq_false,
        ],
    );
    // goal Nat.le (succ 2kx)(2ky) := @False.elim.{0} goal false_proof.
    let goal = c.nle(succ_two_kx.clone(), two_ky.clone());
    let body = Expr::apps(c.false_elim.clone(), [goal, false_proof]);

    ib.finish_child(ib.mk_lam(ht_id, BinderInfo::Default, hblex_true_ty, body))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_nnreal_sqrt_dyadic_mono()
            .expect("init_algebra_nnreal_sqrt_dyadic_mono");
        env.init_algebra_nnreal_sqrt_dyadic_mono()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_dyadic_num_mono_kernel_checks() {
        let env = env();
        let nm = Name::from_string("Rat.dyadicNum_mono");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("Rat.dyadicNum_mono must kernel-check: {e:?}"));
    }

    #[test]
    fn test_dyadic_num_mono_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("Rat.dyadicNum_mono");
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
