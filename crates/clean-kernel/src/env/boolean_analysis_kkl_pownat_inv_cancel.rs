// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL normalization reconciliation — the `powNat`-inv CANCELLATION
//! `2^n·4^n·inv(8^n) = 1` (pure `Rat`, axiom-free).
//!
//! The un-normalized RUNG-1 identity carries a `cube = 2^n` footprint
//! (`noise_two_norm_spectral_third`); the NORMALIZED `W_norm = W·inv(8^n)` form
//! divides by `8^n`. Substituting the normalized Fourier coefficient
//! `Ahat = A·inv(2^n)` (so `A·A = 4^n·(Ahat·Ahat)`) into the rung-1 RHS turns the
//! scalar prefactor into `2^n·4^n·inv(8^n)`, which this module proves is exactly
//! `1`:
//!
//! ```text
//! BoolAnalysis.powNat_two_four_inv_eight_cancel :
//!   ∀ n : Nat,
//!     Rat.mul (Rat.mul (Rat.powNat 2 n) (Rat.powNat 4 n)) (Rat.inv (Rat.powNat 8 n))
//!       = Rat.one
//! ```
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! 1. `2^n·4^n = 8^n` (`eq_24_8`):
//!    - `(2·4)^n = 2^n·4^n` — `Rat.powNat_mul_base 2 4 n`; symm gives
//!      `2^n·4^n = (2·4)^n`.
//!    - `2·4 = 8` — `Rat.mul_natCast 2 4 : mk(ofNat 2)1·mk(ofNat 4)1 =
//!      mk(ofNat(Nat.mul 2 4))1`, and `Nat.mul 2 4 ≡ 8` def-eq, so this is
//!      `2·4 = 8`. `congrArg (powNat · n)` lifts it to `(2·4)^n = 8^n`.
//!    - chain: `2^n·4^n = (2·4)^n = 8^n`.
//! 2. `8^n·inv(8^n) = 1` (`cancel8`): `Rat.mul_inv_cancel (8^n)
//!    (Rat.ne_zero_of_pos (8^n) (Rat.powNat_pos 8 n (0<8)))`.
//! 3. Goal `(2^n·4^n)·inv(8^n) = 1`: `Eq.subst` the LHS factor `2^n·4^n → 8^n`
//!    (motive `t ↦ t·inv(8^n) = 1`) into `cancel8`, using `eq_24_8` symm.
//!
//! Every leaf (`Rat.powNat_mul_base`, `Rat.mul_natCast`, `Rat.mul_inv_cancel`,
//! `Rat.ne_zero_of_pos`, `Rat.powNat_pos`, `congrArg`, `Eq.*`, `Int.NonNeg.mk`)
//! is `Constructive` with empty admitted-axiom closure (only foundational
//! `Quot.sound` under `mul_natCast`/`mul_inv_cancel`), so this lemma is too. No
//! axiom is added or removed. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the `powNat`-inv cancellation.
struct CancelConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_one: Expr,
    #[cfg(test)]
    rat_zero: Expr,
    rat_mul: Expr,
    rat_inv: Expr,
    #[cfg(test)]
    rat_lt: Expr,
    pow_nat: Expr,
    pow_mul_base: Expr,
    pow_pos: Expr,
    mul_natcast: Expr,
    mul_inv_cancel: Expr,
    ne_zero_of_pos: Expr,
    int_nonneg_mk: Expr,
    #[cfg(test)]
    mul_comm: Expr,
    #[cfg(test)]
    mul_assoc: Expr,
    mul_one: Expr,
    mmmc: Expr,
    eq1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
    congr_arg1: Expr,
}

impl CancelConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_one: k("Rat.one"),
            #[cfg(test)]
            rat_zero: k("Rat.zero"),
            rat_mul: k("Rat.mul"),
            rat_inv: k("Rat.inv"),
            #[cfg(test)]
            rat_lt: k("Rat.lt"),
            pow_nat: k("Rat.powNat"),
            pow_mul_base: k("Rat.powNat_mul_base"),
            pow_pos: k("Rat.powNat_pos"),
            mul_natcast: k("Rat.mul_natCast"),
            mul_inv_cancel: k("Rat.mul_inv_cancel"),
            ne_zero_of_pos: k("Rat.ne_zero_of_pos"),
            int_nonneg_mk: k("Int.NonNeg.mk"),
            #[cfg(test)]
            mul_comm: k("Rat.mul_comm"),
            #[cfg(test)]
            mul_assoc: k("Rat.mul_assoc"),
            mul_one: k("Rat.mul_one"),
            mmmc: k("Rat.mul_mul_mul_comm"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg1: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn nat_lit(&self, k: usize) -> Expr {
        let mut nat = self.nat_zero.clone();
        for _ in 0..k {
            nat = Expr::app(self.nat_succ.clone(), nat);
        }
        nat
    }
    /// `Rat.mk (Int.ofNat k) 1`.
    fn lit(&self, k: usize) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), self.nat_lit(k)), one],
        )
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    #[cfg(test)]
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    /// `Rat.powNat (lit k) n`.
    fn pow(&self, k: usize, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.lit(k), n.clone()])
    }
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `congrArg (fun z => f z) h`.
    fn congr_arg(&self, from: Expr, to: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg1.clone(),
            [self.rat.clone(), self.rat.clone(), from, to, f, h],
        )
    }
    /// `0 < lit k` via `@Int.NonNeg.mk (k-1)` (`Rat.lt 0 (mk(ofNat k)1)` reduces
    /// to `Int.NonNeg (ofNat (k-1))`).
    fn lit_pos(&self, k: usize) -> Expr {
        Expr::app(self.int_nonneg_mk.clone(), self.nat_lit(k - 1))
    }
    /// `Rat.mul_comm a b : a·b = b·a`.
    #[cfg(test)]
    fn comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    #[cfg(test)]
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    /// `congrArg (fun z => left·z) h : left·a = left·b`.
    fn congr_l(&self, parent: &EnvDeclBuilder, left: &Expr, a: Expr, bb: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr_arg(a, bb, f, h)
    }
    /// `congrArg (fun z => z·right) h : a·right = b·right`.
    fn congr_r(&self, parent: &EnvDeclBuilder, right: &Expr, a: Expr, bb: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(z, right.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr_arg(a, bb, f, h)
    }
    /// `Rat.mul_one a : a·1 = a`.
    fn mul_one_at(&self, a: Expr) -> Expr {
        Expr::app(self.mul_one.clone(), a)
    }
    /// `Rat.mul_mul_mul_comm a b c d : (a·b)·(c·d) = (a·c)·(b·d)`.
    fn mmmc_at(&self, a: Expr, bb: Expr, cc: Expr, dd: Expr) -> Expr {
        Expr::apps(self.mmmc.clone(), [a, bb, cc, dd])
    }
}

/// Type: `∀ n : Nat, (2^n·4^n)·inv(8^n) = 1`.
fn cancel_type(c: &CancelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let p2 = c.pow(2, &n);
    let p4 = c.pow(4, &n);
    let p8 = c.pow(8, &n);
    let lhs = c.mul(c.mul(p2, p4), c.inv(p8));
    let concl = c.eq_rat(lhs, c.rat_one.clone());
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
    b.finish(e)
}

/// Value: `fun n => <subst eq_24_8 into cancel8>`.
fn cancel_value(c: &CancelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());

    let p2 = c.pow(2, &n);
    let p4 = c.pow(4, &n);
    let p8 = c.pow(8, &n);
    let p2p4 = c.mul(p2.clone(), p4.clone()); // 2^n·4^n

    // ── eq_24_8 : 2^n·4^n = 8^n ──
    // pmb : (2·4)^n = 2^n·4^n   (Rat.powNat_mul_base 2 4 n).
    let two = c.lit(2);
    let four = c.lit(4);
    let two_four = c.mul(two.clone(), four.clone()); // 2·4
    let pow_24 = Expr::apps(c.pow_nat.clone(), [two_four.clone(), n.clone()]); // (2·4)^n
    let pmb = Expr::apps(
        c.pow_mul_base.clone(),
        [two.clone(), four.clone(), n.clone()],
    );
    // symm pmb : 2^n·4^n = (2·4)^n.
    let pmb_symm = c.symm(pow_24.clone(), p2p4.clone(), pmb);
    // mnc : (2·4) = 8   (Rat.mul_natCast 2 4 : mk2·mk4 = mk(2·4); 2·4 ≡ 8 def-eq).
    let eight = c.lit(8);
    let mnc = Expr::apps(c.mul_natcast.clone(), [c.nat_lit(2), c.nat_lit(4)]);
    // congr (powNat · n) mnc : (2·4)^n = 8^n.
    let pow_lam = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = Expr::apps(c.pow_nat.clone(), [z, n.clone()]);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let cong_pow = c.congr_arg(two_four.clone(), eight.clone(), pow_lam, mnc);
    // chain: 2^n·4^n = (2·4)^n = 8^n.
    let eq_24_8 = c.trans(p2p4.clone(), pow_24.clone(), p8.clone(), pmb_symm, cong_pow);

    // ── cancel8 : 8^n·inv(8^n) = 1 ──
    // 0 < 8^n := powNat_pos 8 n (0<8).
    let pos8 = Expr::apps(c.pow_nat.clone(), [eight.clone(), n.clone()]); // == p8
    let _ = &pos8;
    let pow8_pos = Expr::apps(c.pow_pos.clone(), [eight.clone(), n.clone(), c.lit_pos(8)]);
    // 8^n ≠ 0 := ne_zero_of_pos (8^n) (0<8^n).
    let ne8 = Expr::apps(c.ne_zero_of_pos.clone(), [p8.clone(), pow8_pos]);
    // cancel8 : 8^n·inv(8^n) = 1.
    let cancel8 = Expr::apps(c.mul_inv_cancel.clone(), [p8.clone(), ne8]);

    // ── goal : (2^n·4^n)·inv(8^n) = 1 ──
    // motive t ↦ t·inv(8^n) = 1.
    let motive = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = d.fresh_local(c.rat.clone());
        let body = c.eq_rat(c.mul(t, c.inv(p8.clone())), c.rat_one.clone());
        d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    // eq_24_8 : 2^n·4^n = 8^n ; symm : 8^n = 2^n·4^n. subst (from 8^n to 2^n·4^n).
    let eq_8_24 = c.symm(p2p4.clone(), p8.clone(), eq_24_8);
    // @Eq.subst Rat motive 8^n (2^n·4^n) eq_8_24 cancel8 : motive (2^n·4^n).
    let proof = c.subst(motive, p8.clone(), p2p4.clone(), eq_8_24, cancel8);

    let body = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), proof);
    b.finish(body)
}

/// Type: `∀ n : Nat, 4^n·(inv(2^n)·inv(2^n)) = 1`.
fn four_inv_sq_type(c: &CancelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let p4 = c.pow(4, &n);
    let inv2 = c.inv(c.pow(2, &n));
    let lhs = c.mul(p4, c.mul(inv2.clone(), inv2));
    let concl = c.eq_rat(lhs, c.rat_one.clone());
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), concl);
    b.finish(e)
}

/// Value: `fun n => <p4 = p2·p2, then (p2·p2)·(inv2·inv2) = (p2·inv2)·(p2·inv2) =
/// 1·1 = 1>`.
fn four_inv_sq_value(c: &CancelConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());

    let two = c.lit(2);
    let p2 = c.pow(2, &n);
    let p4 = c.pow(4, &n);
    let inv2 = c.inv(p2.clone());
    let inv2_inv2 = c.mul(inv2.clone(), inv2.clone()); // inv2·inv2
    let p2_p2 = c.mul(p2.clone(), p2.clone()); // p2·p2

    // ── e_p4_p2p2 : 4^n = p2·p2 ──
    // pmb : (2·2)^n = p2·p2  (powNat_mul_base 2 2 n).
    let two_two = c.mul(two.clone(), two.clone()); // 2·2
    let pow_22 = Expr::apps(c.pow_nat.clone(), [two_two.clone(), n.clone()]); // (2·2)^n
    let pmb = Expr::apps(
        c.pow_mul_base.clone(),
        [two.clone(), two.clone(), n.clone()],
    );
    // mnc : 2·2 = 4  (mul_natCast 2 2 : mk2·mk2 = mk(Nat.mul 2 2); ≡ 4 def-eq).
    let four = c.lit(4);
    let mnc = Expr::apps(c.mul_natcast.clone(), [c.nat_lit(2), c.nat_lit(2)]);
    // congr (powNat · n) mnc : (2·2)^n = 4^n.
    let pow_lam = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let (z_id, z) = d.fresh_local(c.rat.clone());
        let body = Expr::apps(c.pow_nat.clone(), [z, n.clone()]);
        d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let cong_pow = c.congr_arg(two_two.clone(), four.clone(), pow_lam, mnc);
    // symm cong_pow : 4^n = (2·2)^n.
    let cong_pow_symm = c.symm(pow_22.clone(), p4.clone(), cong_pow);
    // chain : 4^n = (2·2)^n = p2·p2.
    let e_p4_p2p2 = c.trans(
        p4.clone(),
        pow_22.clone(),
        p2_p2.clone(),
        cong_pow_symm,
        pmb,
    );

    // ── e_rewrite : p4·(inv2·inv2) = (p2·p2)·(inv2·inv2)  (congr (_·(inv2·inv2))) ──
    let p4_inner = c.mul(p4.clone(), inv2_inv2.clone());
    let p2p2_inner = c.mul(p2_p2.clone(), inv2_inv2.clone());
    let e_rewrite = c.congr_r(&b, &inv2_inv2, p4.clone(), p2_p2.clone(), e_p4_p2p2);

    // ── e_shuffle : (p2·p2)·(inv2·inv2) = (p2·inv2)·(p2·inv2)  (mul_mul_mul_comm) ──
    let p2_inv2 = c.mul(p2.clone(), inv2.clone()); // p2·inv2
    let prod_cancel = c.mul(p2_inv2.clone(), p2_inv2.clone()); // (p2·inv2)·(p2·inv2)
    let e_shuffle = c.mmmc_at(p2.clone(), p2.clone(), inv2.clone(), inv2.clone());

    // ── cancel : p2·inv2 = 1  (mul_inv_cancel p2 (p2≠0)) ──
    let p2_pos = Expr::apps(c.pow_pos.clone(), [two.clone(), n.clone(), c.lit_pos(2)]);
    let ne2 = Expr::apps(c.ne_zero_of_pos.clone(), [p2.clone(), p2_pos]);
    let cancel2 = Expr::apps(c.mul_inv_cancel.clone(), [p2.clone(), ne2]); // p2·inv2 = 1

    // ── e_to_one : (p2·inv2)·(p2·inv2) = 1·1  then 1·1 = 1 (mul_one) ──
    // congr (_·(p2·inv2)) cancel2 : (p2·inv2)·(p2·inv2) = 1·(p2·inv2).
    let one = c.rat_one.clone();
    let one_p2inv2 = c.mul(one.clone(), p2_inv2.clone());
    let e_a = c.congr_r(&b, &p2_inv2, p2_inv2.clone(), one.clone(), cancel2.clone());
    // congr (1·_) cancel2 : 1·(p2·inv2) = 1·1.
    let one_one = c.mul(one.clone(), one.clone());
    let e_b = c.congr_l(&b, &one, p2_inv2.clone(), one.clone(), cancel2);
    // mul_one 1 : 1·1 = 1.
    let e_c = c.mul_one_at(one.clone());
    // chain : (p2·inv2)·(p2·inv2) = 1·(p2·inv2) = 1·1 = 1.
    let e_ab = c.trans(
        prod_cancel.clone(),
        one_p2inv2.clone(),
        one_one.clone(),
        e_a,
        e_b,
    );
    let e_to_one = c.trans(prod_cancel.clone(), one_one.clone(), one.clone(), e_ab, e_c);

    // ── assemble : p4·(inv2·inv2) = (p2·p2)·(inv2·inv2) = (p2·inv2)·(p2·inv2) = 1 ──
    let t1 = c.trans(
        p4_inner.clone(),
        p2p2_inner.clone(),
        prod_cancel.clone(),
        e_rewrite,
        e_shuffle,
    );
    let proof = c.trans(p4_inner, prod_cancel, one, t1, e_to_one);

    let body = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), proof);
    b.finish(body)
}

impl Environment {
    /// Register `BoolAnalysis.four_inv_two_sq_cancel` —
    /// `∀ n, 4^n·(inv(2^n)·inv(2^n)) = 1`. The companion cancellation that turns the
    /// un-normalized squared Fourier coefficient `A·A` into `4^n·(Ahat·Ahat)` (with
    /// `Ahat = A·inv(2^n)`): `A·A = 4^n·((A·inv2)·(A·inv2)) = (A·A)·(4^n·(inv2·inv2))
    /// = (A·A)·1`. Idempotent; kernel-checked, `Constructive`, EMPTY admitted-axiom
    /// closure. No axiom added or removed.
    pub fn register_four_inv_two_sq_cancel(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.four_inv_two_sq_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_pow_nat()?; // Rat.powNat
        self.register_rat_pow_nat_mul_base()?; // powNat_mul_base, powNat_pos
        self.register_rat_mul_natcast()?; // mk·mk = mk(Nat.mul) literal bridge
        self.init_algebra_rat_inv_dyadic()?; // mul_inv_cancel, ne_zero_of_pos
        self.register_rat_mul_mul_mul_comm_theorem()?; // mul_mul_mul_comm
        {
            // Rat.mul_one / Rat.mul_comm / Rat.mul_assoc quotient structural lemmas.
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?;
        }
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = CancelConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: four_inv_sq_type(&c),
            value: four_inv_sq_value(&c),
        })
    }

    /// Register `BoolAnalysis.powNat_two_four_inv_eight_cancel` —
    /// `∀ n, (2^n·4^n)·inv(8^n) = 1`. Pure `Rat`/`powNat` bookkeeping that clears
    /// the un-normalized `cube = 2^n` footprint when the NORMALIZED Fourier
    /// coefficient `Ahat = A·inv(2^n)` is substituted (`A·A = 4^n·Ahat²`) and the
    /// whole is divided by `8^n`. Idempotent; kernel-checked, `Constructive`,
    /// EMPTY admitted-axiom closure. No axiom added or removed.
    pub fn register_pownat_two_four_inv_eight_cancel(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.powNat_two_four_inv_eight_cancel");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_rat_pow_nat()?; // Rat.powNat
        self.register_rat_pow_nat_mul_base()?; // powNat_mul_base, powNat_pos
        self.register_rat_mul_natcast()?; // mk·mk = mk(Nat.mul) literal bridge
        self.init_algebra_rat_inv_dyadic()?; // mul_inv_cancel, ne_zero_of_pos
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = CancelConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: cancel_type(&c),
            value: cancel_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_pownat_two_four_inv_eight_cancel_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_pownat_two_four_inv_eight_cancel()
            .expect("register_pownat_two_four_inv_eight_cancel");
        let nm = Name::from_string("BoolAnalysis.powNat_two_four_inv_eight_cancel");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("cancel proof must check against its type: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_pownat_two_four_inv_eight_cancel_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_pownat_two_four_inv_eight_cancel()
            .expect("first");
        env.register_pownat_two_four_inv_eight_cancel()
            .expect("idempotent");
    }

    #[test]
    fn test_four_inv_two_sq_cancel_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_four_inv_two_sq_cancel()
            .expect("register_four_inv_two_sq_cancel");
        let nm = Name::from_string("BoolAnalysis.four_inv_two_sq_cancel");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("four_inv_sq proof must check against its type: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_four_inv_two_sq_cancel_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_four_inv_two_sq_cancel().expect("first");
        env.register_four_inv_two_sq_cancel().expect("idempotent");
    }
}
