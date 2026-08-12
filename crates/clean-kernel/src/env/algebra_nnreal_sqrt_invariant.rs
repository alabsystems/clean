// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/sqrt layer — Stage B3 (2/n): the dyadic-floor LOWER-bound invariant.
//!
//! # Why this module exists
//!
//! The keystone `NNReal.sqrt x · NNReal.sqrt x = x` needs the dyadic-floor
//! numerator `k_n := Rat.dyadicNum x n` (`algebra_nnreal_sqrt_dyadic.rs`) to
//! satisfy the LOWER bound
//!
//! ```text
//!   Rat.dyadicNum_sq_le :  0 ≤ x  ⟹  ∀ n, (ofNat k_n)² ≤ x · 4^n
//! ```
//!
//! which (after dividing by `4^n`) is exactly `a_n² ≤ x` for the scaled
//! approximation `a_n = k_n / 2^n`. It is the "floor never overshoots" half of
//! the squeeze.
//!
//! # Proof (Nat.rec over n with a Prop motive)
//!
//! - BASE `n = 0`: `dyadicNum x 0 ≡ 0`, `dyadicPow4 0 ≡ Rat.one` (single ι), so
//!   the goal is `(ofNat 0 · ofNat 0) ≤ x · 1`. `Rat.zero_mul (ofNat 0)` collapses
//!   the LHS to `0` (`ofNat 0 ≡ Rat.zero` defeq) and `Rat.mul_one x` the RHS to
//!   `x`; transport the hypothesis `0 ≤ x` along both equalities.
//!
//! - STEP `P n → P (n+1)`: `dyadicNum x (n+1) ≡ Bool.rec (fun _=>Nat) (2k) (2k+1)
//!   (Rat.ble ((ofNat (2k+1))²) (x·4^{n+1}))` for `k := dyadicNum x n`. Dependent
//!   `Bool.rec.{0}` on that test with reflection (the `Rat.max` lattice idiom):
//!   motive `fun b => Eq Bool test b → (ofNat (Bool.rec _ (2k)(2k+1) b))² ≤ x·4^{n+1}`.
//!     * TRUE minor (`b ≡ true`, `Bool.rec ≡ 2k+1`): the goal is exactly
//!       `Rat.le_of_ble_eq_true ((ofNat (2k+1))²) (x·4^{n+1}) h_eq`.
//!     * FALSE minor (`b ≡ false`, `Bool.rec ≡ 2k`): scale the IH by 4. With
//!       `ofNat (2k) = ofNat 2 · ofNat k` and `ofNat 2 · ofNat 2 = ofNat 4`
//!       (both `Rat.ofNat_mul`), `(ofNat 2k)² = ofNat 4 · (ofNat k)²`
//!       (`Rat.mul_mul_mul_comm`); and `x·4^{n+1} = ofNat 4 · (x·4^n)`
//!       (`powNat_succ` defeq + `mul_mul_mul_comm` with the trivial `x = 1·x`
//!       regroup via `Rat.one_mul`/assoc — done with explicit `Eq.subst`s);
//!       `Rat.mul_le_mul_of_nonneg_left (ofNat 4)` applied to the IH closes it,
//!       with `0 ≤ ofNat 4` from `Rat.ofNat_le_ofNat_of_le 0 4 (Nat.zero_le 4)`.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure. NO `sorry` / `add_decl_unchecked` / `add_decl_structural`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the lower-bound invariant.
pub(crate) struct InvConsts {
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_add: Expr,
    nat_mul: Expr,
    nat_zero_le: Expr,
    rat: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_le: Expr,
    rat_ofnat: Expr,
    rat_dyadic_num: Expr,
    rat_dyadic_pow4: Expr,
    rat_ble: Expr,
    bool_ty: Expr,
    bool_true: Expr,
    bool_false: Expr,
    rat_zero_mul: Expr,
    rat_mul_one: Expr,
    rat_mul_mul_mul_comm: Expr,
    rat_mul_le_left: Expr,
    rat_ofnat_mul: Expr,
    rat_ofnat_le_ofnat: Expr,
    rat_le_of_ble_eq_true: Expr,
    // Recursors / Eq toolkit.
    nat_rec_prop: Expr,
    bool_rec_nat: Expr,
    bool_rec_prop: Expr,
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_subst_prop: Expr,
    congr_arg11: Expr,
}

impl InvConsts {
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
            rat_mul: k("Rat.mul"),
            rat_le: k("Rat.le"),
            rat_ofnat: k("Rat.ofNat"),
            rat_dyadic_num: k("Rat.dyadicNum"),
            rat_dyadic_pow4: k("Rat.dyadicPow4"),
            rat_ble: k("Rat.ble"),
            bool_ty: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            rat_zero_mul: k("Rat.zero_mul"),
            rat_mul_one: k("Rat.mul_one"),
            rat_mul_mul_mul_comm: k("Rat.mul_mul_mul_comm"),
            rat_mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            rat_ofnat_mul: k("Rat.ofNat_mul"),
            rat_ofnat_le_ofnat: k("Rat.ofNat_le_ofNat_of_le"),
            rat_le_of_ble_eq_true: k("Rat.le_of_ble_eq_true"),
            nat_rec_prop: Expr::const_(Name::from_string("Nat.rec"), vec![l0.clone()]),
            bool_rec_nat: Expr::const_(Name::from_string("Bool.rec"), vec![l1.clone()]),
            bool_rec_prop: Expr::const_(Name::from_string("Bool.rec"), vec![l0.clone()]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl1: Expr::const_(Name::from_string("Eq.refl"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            // `Eq.subst.{u}` quantifies `{α : Sort u}`; here `α = Rat : Sort 1`,
            // so the universe is 1 (the `motive : α → Prop` is independent).
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
        // `Bool : Sort 1`, so element equality over it is `Eq.{1} Bool`.
        Expr::apps(self.eq1.clone(), [self.bool_ty.clone(), x, y])
    }
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn refl_rat(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), x])
    }
    fn refl_bool(&self, x: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.bool_ty.clone(), x])
    }
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    /// `@congrArg Rat Rat a b f h : Eq Rat (f a)(f b)`.
    fn congr_rat(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg11.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `@Eq.subst.{0} Rat motive a b h_eq h : motive b` (motive into Prop).
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

    /// `dyadicNum x (succ n)`'s defining `Bool.rec` value at an explicit `b`:
    ///   `@Bool.rec.{1} (fun _=>Nat) (2k) (2k+1) b`  where `k := dnum x n`.
    /// Reduces to `dnum x (succ n)` when `b ≡ test`.
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
    /// Register `Rat.dyadicNum_sq_le`. Idempotent; axiom-free.
    pub fn init_algebra_nnreal_sqrt_invariant(&mut self) -> Result<(), EnvError> {
        self.init_algebra_nnreal_sqrt_dyadic()?; // dyadicNum, dyadicPow4, Rat.ble
        self.register_rat_ofnat_mul()?; // Rat.ofNat_mul
        self.register_rat_ofnat()?; // Rat.ofNat
        self.register_rat_ofnat_le_ofnat_of_le()?; // 0 ≤ ofNat 4 bridge
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.register_nat_ble_le_lemmas()?; // Nat.zero_le
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_left, mul_one, etc.
        self.register_rat_mul_mul_mul_comm_theorem()?; // Rat.mul_mul_mul_comm
        self.rat_quotient_payoff_into_live()?; // Rat.mul_one, Rat.zero_mul, Rat.one_mul (live)
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true

        let c = InvConsts::new();
        self.register_dyadic_num_sq_le(&c)
    }

    fn register_dyadic_num_sq_le(&mut self, c: &InvConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.dyadicNum_sq_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        // motive_body x n := (ofNat (dnum x n))² ≤ (x · dyadicPow4 n).
        let motive_body = |x: &Expr, n: &Expr| -> Expr {
            c.rle(
                c.sq_ofnat(c.dnum(x, n.clone())),
                c.rmul(x.clone(), c.pow4(n.clone())),
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
fn build_invariant_value(c: &InvConsts, motive_body: &dyn Fn(&Expr, &Expr) -> Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(c.rat.clone());
    let h_ty = c.rle(c.rat_zero.clone(), x.clone());
    let (h_id, h) = b.fresh_local(h_ty.clone());

    // motive : fun (n:Nat) => (ofNat (dnum x n))² ≤ x·4^n.
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

/// BASE: `(ofNat 0 · ofNat 0) ≤ x · 1`. (dnum x 0 ≡ 0, dyadicPow4 0 ≡ 1.)
fn build_base(c: &InvConsts, parent: &EnvDeclBuilder, x: &Expr, h: &Expr) -> Expr {
    let b = EnvDeclBuilder::child_of(parent);
    let of0 = c.rofnat(c.nat_zero.clone());
    let lhs = c.rmul(of0.clone(), of0.clone()); // ofNat 0 · ofNat 0
    let one = Expr::const_(Name::from_string("Rat.one"), vec![]);
    let rhs = c.rmul(x.clone(), one.clone()); // x · 1

    // e_lhs : (ofNat 0 · ofNat 0) = Rat.zero    via Rat.zero_mul (ofNat 0)
    //   (ofNat 0 ≡ Rat.zero defeq, so zero_mul applies to the leading factor).
    let e_lhs = Expr::app(c.rat_zero_mul.clone(), of0.clone());
    // e_rhs : (x · 1) = x   via Rat.mul_one x.
    let e_rhs = Expr::app(c.rat_mul_one.clone(), x.clone());

    // Goal: lhs ≤ rhs. We have h : 0 ≤ x.
    // subst RHS: motive_r r := lhs ≤ r ; want lhs ≤ rhs from lhs ≤ x via symm e_rhs.
    // Better: build `lhs ≤ x` then transport to `lhs ≤ rhs`.
    // Step 1: from h : Rat.zero ≤ x, get `lhs ≤ x` by subst along symm e_lhs
    //   (motive_l l := l ≤ x).
    let motive_l = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (l_id, l) = d.fresh_local(c.rat.clone());
        let body = c.rle(l, x.clone());
        d.finish_child(d.mk_lam(l_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let e_lhs_symm = c.symm_rat(lhs.clone(), c.rat_zero.clone(), e_lhs); // zero = lhs
    let lhs_le_x = c.subst_rat_prop(
        motive_l,
        c.rat_zero.clone(),
        lhs.clone(),
        e_lhs_symm,
        h.clone(),
    );

    // Step 2: from `lhs ≤ x`, get `lhs ≤ rhs` by subst along symm e_rhs
    //   (motive_r r := lhs ≤ r). e_rhs : rhs = x, symm : x = rhs.
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
fn build_step(c: &InvConsts, parent: &EnvDeclBuilder, x: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let (n_id, n) = b.fresh_local(c.nat.clone());

    // ih : (ofNat (dnum x n))² ≤ x · 4^n.
    let kk = c.dnum(x, n.clone()); // k := dnum x n
    let ih_ty = c.rle(c.sq_ofnat(kk.clone()), c.rmul(x.clone(), c.pow4(n.clone())));
    let (ih_id, ih) = b.fresh_local(ih_ty.clone());

    let test = c.digit_test(x, &kk, &n);
    let rhs_succ = c.rmul(x.clone(), c.pow4(c.succ(n.clone()))); // x·4^{n+1}

    // motive : fun (z:Bool) => Eq Bool test z → (ofNat (Bool.rec _ (2k)(2k+1) z))² ≤ x·4^{n+1}.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = mb.fresh_local(c.bool_ty.clone());
        let heq_ty = c.eq_bool(test.clone(), z.clone());
        let (heq_id, _heq) = mb.fresh_local(heq_ty.clone());
        let num_z = c.bool_rec_num(&mb, &kk, z.clone());
        let concl = c.rle(c.sq_ofnat(num_z), rhs_succ.clone());
        let body = mb.mk_pi(heq_id, BinderInfo::Default, heq_ty, concl);
        mb.finish_child(mb.mk_lam(z_id, BinderInfo::Default, c.bool_ty.clone(), body))
    };

    // FALSE minor: fun (heq : Eq Bool test false) => proof of (ofNat 2k)² ≤ x·4^{n+1}.
    let false_minor = build_false_minor(c, &b, x, &n, &kk, &ih);
    // TRUE minor: fun (heq : Eq Bool test true) => le_of_ble_eq_true.
    let true_minor = {
        let mut tb = EnvDeclBuilder::child_of(&b);
        let heq_ty = c.eq_bool(test.clone(), c.bool_true.clone());
        let (heq_id, heq) = tb.fresh_local(heq_ty.clone());
        let two_k = c.nmul(c.nat_lit(2), kk.clone());
        let two_k1 = c.nadd(two_k, c.nat_lit(1));
        let sq = c.sq_ofnat(two_k1);
        // Rat.le_of_ble_eq_true sq (x·4^{n+1}) heq : sq ≤ x·4^{n+1}.
        let body = Expr::apps(c.rat_le_of_ble_eq_true.clone(), [sq, rhs_succ.clone(), heq]);
        let lam = tb.mk_lam(heq_id, BinderInfo::Default, heq_ty, body);
        tb.finish_child(lam)
    };

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

/// FALSE minor: `fun (heq) => (ofNat 2k)² ≤ x·4^{n+1}` by scaling the IH by 4.
fn build_false_minor(
    c: &InvConsts,
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

    let of2 = c.rofnat(c.nat_lit(2));
    let of4 = c.rofnat(c.nat_lit(4));
    let ofk = c.rofnat(kk.clone());
    let two_k = c.nmul(c.nat_lit(2), kk.clone());
    let sq_k = c.rmul(ofk.clone(), ofk.clone()); // (ofNat k)²
    let pow4n = c.pow4(n.clone());
    let x_pow = c.rmul(x.clone(), pow4n.clone()); // x·4^n

    // 0 ≤ ofNat 4 : Rat.ofNat_le_ofNat_of_le 0 4 (Nat.zero_le 4) : ofNat 0 ≤ ofNat 4
    //   (ofNat 0 ≡ Rat.zero defeq).
    let zero_le_4 = Expr::apps(
        c.rat_ofnat_le_ofnat.clone(),
        [
            c.nat_zero.clone(),
            c.nat_lit(4),
            Expr::app(c.nat_zero_le.clone(), c.nat_lit(4)),
        ],
    );

    // scaled : ofNat 4 · (ofNat k · ofNat k) ≤ ofNat 4 · (x·4^n)
    //   via mul_le_mul_of_nonneg_left (ofNat 4) sq_k x_pow ih zero_le_4.
    let scaled = c.mul_le_left(
        of4.clone(),
        sq_k.clone(),
        x_pow.clone(),
        ih.clone(),
        zero_le_4,
    );

    // ── LEFT equality: (ofNat 2k)² = ofNat 4 · (ofNat k · ofNat k) ──
    // (a) ofNat (2k) = ofNat 2 · ofNat k    (ofNat_mul 2 k ; 2k ≡ Nat.mul 2 k)
    let e_2k = c.ofnat_mul(c.nat_lit(2), kk.clone()); // ofNat(2·k) = ofNat 2 · ofNat k
    let of_2k = c.rofnat(two_k.clone());
    let prod_2k = c.rmul(of2.clone(), ofk.clone());
    let eq_trans1 = Expr::const_(
        Name::from_string("Eq.trans"),
        vec![Level::succ(Level::zero())],
    );

    // (ofNat 2k)² = (ofNat 2k)·(ofNat 2k); rewrite both factors to (ofNat 2·ofNat k).
    // L0 := of_2k · of_2k.
    let l0 = c.rmul(of_2k.clone(), of_2k.clone());
    // s1 : of_2k·of_2k = prod_2k·of_2k   via congrArg (· · of_2k) e_2k.
    let f_right = {
        let mut d = EnvDeclBuilder::child_of(&fb);
        let (w_id, w) = d.fresh_local(c.rat.clone());
        let body = c.rmul(w, of_2k.clone());
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s1 = c.congr_rat(of_2k.clone(), prod_2k.clone(), f_right, e_2k.clone());
    let l1 = c.rmul(prod_2k.clone(), of_2k.clone());
    // s2 : prod_2k·of_2k = prod_2k·prod_2k   via congrArg (prod_2k · ·) e_2k.
    let f_left = {
        let mut d = EnvDeclBuilder::child_of(&fb);
        let (w_id, w) = d.fresh_local(c.rat.clone());
        let body = c.rmul(prod_2k.clone(), w);
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s2 = c.congr_rat(of_2k.clone(), prod_2k.clone(), f_left, e_2k.clone());
    let l2 = c.rmul(prod_2k.clone(), prod_2k.clone()); // (ofNat2·ofNatk)·(ofNat2·ofNatk)
                                                       // l0_l2 : l0 = l2  (s1 ; s2).
    let l0_l2 = Expr::apps(
        eq_trans1.clone(),
        [c.rat.clone(), l0.clone(), l1.clone(), l2.clone(), s1, s2],
    );

    // s3 : (ofNat2·ofNatk)·(ofNat2·ofNatk) = (ofNat2·ofNat2)·(ofNatk·ofNatk)
    //      via mul_mul_mul_comm (ofNat2)(ofNatk)(ofNat2)(ofNatk).
    let s3 = c.mmmc(of2.clone(), ofk.clone(), of2.clone(), ofk.clone());
    let o2o2 = c.rmul(of2.clone(), of2.clone());
    let mid_l = c.rmul(o2o2.clone(), sq_k.clone()); // (o2·o2)·(ok·ok)
                                                    // s5 : (o2·o2)·(ok·ok) = ofNat4·(ok·ok).
                                                    //   e_22 : ofNat(2·2) = ofNat2·ofNat2, i.e. ofNat 4 = o2o2 (2·2 ≡ 4). symm → o2o2 = ofNat4.
    let e_22 = c.ofnat_mul(c.nat_lit(2), c.nat_lit(2));
    let e_22_symm = c.symm_rat(of4.clone(), o2o2.clone(), e_22); // o2o2 = ofNat 4
    let f_scale = {
        let mut d = EnvDeclBuilder::child_of(&fb);
        let (w_id, w) = d.fresh_local(c.rat.clone());
        let body = c.rmul(w, sq_k.clone());
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s5 = c.congr_rat(o2o2.clone(), of4.clone(), f_scale, e_22_symm);
    let rhs_scaled_l = c.rmul(of4.clone(), sq_k.clone()); // ofNat 4 · (ofNat k · ofNat k)

    // l2_mid : l2 = rhs_scaled_l  (s3 ; s5).
    let l2_mid = Expr::apps(
        eq_trans1.clone(),
        [
            c.rat.clone(),
            l2.clone(),
            mid_l.clone(),
            rhs_scaled_l.clone(),
            s3,
            s5,
        ],
    );
    // left_eq : l0 = rhs_scaled_l  (l0_l2 ; l2_mid).
    let left_eq = Expr::apps(
        eq_trans1.clone(),
        [
            c.rat.clone(),
            l0.clone(),
            l2.clone(),
            rhs_scaled_l.clone(),
            l0_l2,
            l2_mid,
        ],
    );

    // ── RIGHT equality: x·4^{n+1} = ofNat 4 · (x·4^n) ──
    // 4^{n+1} ≡ Rat.mul (ofNat 4)(4^n) defeq (powNat_succ single ι), so
    //   x·4^{n+1} ≡ x·(ofNat4·4^n). We need = ofNat4·(x·4^n).
    //   x·(o4·p) = (x·o4)·p (assoc)... simplest: use mul_mul_mul_comm with 1's? Use:
    //   x·(o4·p) and o4·(x·p). Route via mmmc on (1·x)·(o4·p) is messy.
    //   Cleaner: regroup with Rat.mul_comm/assoc.
    //   We build: r0 := x·(o4·p) (defeq to x·4^{n+1}); target r3 := o4·(x·p).
    let pow4_succ_unfold = c.rmul(of4.clone(), pow4n.clone()); // o4·4^n  (≡ 4^{n+1})
    let r0 = c.rmul(x.clone(), pow4_succ_unfold.clone()); // x·(o4·4^n)  ≡ x·4^{n+1}
                                                          // r0 = (x·o4)·p  via symm (mul_assoc x o4 p)
    let rat_mul_assoc = Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]);
    let assoc1 = Expr::apps(
        rat_mul_assoc.clone(),
        [x.clone(), of4.clone(), pow4n.clone()],
    );
    // assoc1 : (x·o4)·p = x·(o4·p). symm → x·(o4·p) = (x·o4)·p
    let xo4 = c.rmul(x.clone(), of4.clone());
    let r1 = c.rmul(xo4.clone(), pow4n.clone());
    let assoc1_symm = c.symm_rat(r1.clone(), r0.clone(), assoc1);
    // (x·o4) = (o4·x) via mul_comm
    let rat_mul_comm = Expr::const_(Name::from_string("Rat.mul_comm"), vec![]);
    let comm1 = Expr::apps(rat_mul_comm.clone(), [x.clone(), of4.clone()]); // x·o4 = o4·x
    let o4x = c.rmul(of4.clone(), x.clone());
    // r1 = (o4·x)·p via congrArg (· · p) comm1
    let f_pp = {
        let mut d = EnvDeclBuilder::child_of(&fb);
        let (w_id, w) = d.fresh_local(c.rat.clone());
        let body = c.rmul(w, pow4n.clone());
        d.finish_child(d.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let s_r2 = c.congr_rat(xo4.clone(), o4x.clone(), f_pp, comm1);
    let r2 = c.rmul(o4x.clone(), pow4n.clone());
    // r2 = o4·(x·p) via mul_assoc o4 x p
    let assoc2 = Expr::apps(
        rat_mul_assoc.clone(),
        [of4.clone(), x.clone(), pow4n.clone()],
    ); // (o4·x)·p = o4·(x·p)
    let r3 = c.rmul(of4.clone(), x_pow.clone()); // o4·(x·p)
                                                 // chain r0=r1 (assoc1_symm), r1=r2 (s_r2), r2=r3 (assoc2)
    let r0_r1 = assoc1_symm;
    let r0_r2 = Expr::apps(
        eq_trans1.clone(),
        [
            c.rat.clone(),
            r0.clone(),
            r1.clone(),
            r2.clone(),
            r0_r1,
            s_r2,
        ],
    );
    let right_eq = Expr::apps(
        eq_trans1.clone(),
        [
            c.rat.clone(),
            r0.clone(),
            r2.clone(),
            r3.clone(),
            r0_r2,
            assoc2,
        ],
    );

    // scaled : r3 ≤ r3'? scaled : o4·(ok·ok) ≤ o4·(x·p) = r3.
    //   so scaled : rhs_scaled_l ≤ r3.
    // Goal: l0 ≤ x·4^{n+1}  where x·4^{n+1} ≡ r0 (defeq).
    // We have left_eq : l0 = rhs_scaled_l ; scaled : rhs_scaled_l ≤ r3 ; right_eq : r0 = r3.
    // ⟹ l0 ≤ r0 by: subst scaled's LHS along symm left_eq → l0 ≤ r3, then RHS along symm right_eq → l0 ≤ r0.
    // Step A: motive_a u := u ≤ r3 ; from scaled : rhs_scaled_l ≤ r3, subst along symm left_eq (rhs_scaled_l → l0).
    let motive_a = {
        let mut d = EnvDeclBuilder::child_of(&fb);
        let (u_id, u) = d.fresh_local(c.rat.clone());
        let body = c.rle(u, r3.clone());
        d.finish_child(d.mk_lam(u_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let left_eq_symm = c.symm_rat(l0.clone(), rhs_scaled_l.clone(), left_eq); // rhs_scaled_l = l0
    let l0_le_r3 = c.subst_rat_prop(
        motive_a,
        rhs_scaled_l.clone(),
        l0.clone(),
        left_eq_symm,
        scaled,
    );
    // Step B: motive_b v := l0 ≤ v ; from l0 ≤ r3, subst along symm right_eq (r3 → r0).
    let motive_b = {
        let mut d = EnvDeclBuilder::child_of(&fb);
        let (v_id, v) = d.fresh_local(c.rat.clone());
        let body = c.rle(l0.clone(), v);
        d.finish_child(d.mk_lam(v_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // right_eq : r0 = r3 ; symm (endpoints r0,r3) → r3 = r0.
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
        env.init_algebra_nnreal_sqrt_invariant()
            .expect("init_algebra_nnreal_sqrt_invariant");
        env.init_algebra_nnreal_sqrt_invariant()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_dyadic_num_sq_le_kernel_checks() {
        let env = env();
        let nm = Name::from_string("Rat.dyadicNum_sq_le");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be Theorem");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let value = info.value.clone().expect("value present");
        tc.check_type(&value, &info.type_)
            .expect("Rat.dyadicNum_sq_le must kernel-check");
    }

    #[test]
    fn test_dyadic_num_sq_le_constructive_empty_closure() {
        let env = env();
        let nm = Name::from_string("Rat.dyadicNum_sq_le");
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
