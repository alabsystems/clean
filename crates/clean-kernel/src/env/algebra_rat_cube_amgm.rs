// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL real/cbrt layer — the **cubed 3-term AM-GM** `27·P²·Q ≤ (2P+Q)³`, proved
//! GENUINELY at the `Rat` level via the landed `RatPolyProver`'s SOS identity.
//!
//! # Why this module exists (CH3 §11 rung 3 — the ONE hard analytic rung)
//!
//! The sqrt-free dual `(4/3,4)` tensorization (design
//! `2026-06-20-hc43-dual-tensorization-cross-term.md`, §11) closes its CH3
//! cross-term split `3U₁²U₂ ≤ 2P+Q` ROOT-FREELY via `NNReal.le_of_cube_le_cube`,
//! reducing to the CUBED chain
//! ```text
//!   (3U₁²U₂)³ = 27·U₁⁶·U₂³  ≤  27·P²·Q  ≤  (2P+Q)³.
//! ```
//! The FIRST `≤` is the landed monotone core `NNReal.holder3_cross_mono`. The
//! SECOND `≤` — the rational cubed AM-GM `27·P²·Q ≤ (2P+Q)³` — is the design's
//! pinned "ONE hard rung" (§11 rung 3). Its certificate is the perfect-square
//! sum-of-squares factorisation
//! ```text
//!   (2P+Q)³ − 27·P²·Q  =  (P−Q)²·(8P+Q)  ≥ 0.
//! ```
//!
//! # What this module registers (axiom-free, kernel-checked, GENUINE)
//!
//! ```text
//!   Rat.cube_amgm_two_one : ∀ p q : Rat,
//!     Rat.le Rat.zero p → Rat.le Rat.zero q →
//!     Rat.le (27·(p·p·q)) (((2p+q)·(2p+q))·(2p+q))
//! ```
//!
//! where `27 := ((1+…+1) 27×)`, `2p := (1+1)·p`, `8P := (1+…+1)·p` (the numerals
//! exactly as the `RatPolyProver`'s `RatPoly.test_ch3_sos` writes them).
//!
//! # Proof (the prover does the real work; SOS nonnegativity does the rest)
//!
//! 1. `E : (2P+Q)³ = 27·P²·Q + (P−Q)²·(8P+Q)` — the degree-3 two-var `Rat` ring
//!    identity, proved by `RatPolyProver::prove_poly_eq` (this is the SAME identity
//!    the landed `RatPoly.test_ch3_sos` validates — the prover normalises both
//!    sides to the identical canonical polynomial and emits the `Eq` proof).
//! 2. `0 ≤ (P−Q)²` via `Rat.sq_nonneg (P−Q)` (note `(P−Q)² = (P−Q)·(P−Q)`).
//! 3. `0 ≤ 8P+Q` via the numeral chain `0 ≤ 8` (`Rat.zero_le_one` +
//!    `Rat.le_add_of_nonneg_right`/`Rat.le_trans`, 7 rungs), then
//!    `0 ≤ 8P` (`Rat.mul_nonneg`), then `8P ≤ 8P+Q` + `Rat.le_trans`.
//! 4. `0 ≤ (P−Q)²·(8P+Q)` via `Rat.mul_nonneg`.
//! 5. `27·P²·Q ≤ 27·P²·Q + (P−Q)²·(8P+Q)` via `Rat.le_add_of_nonneg_right`.
//! 6. transport the RHS back to `(2P+Q)³` along `symm E` (`Eq.subst`).
//!
//! Every leaf (`RatPolyProver`'s ring lemmas, `Rat.sq_nonneg`, `Rat.mul_nonneg`,
//! `Rat.le_add_of_nonneg_right`, `Rat.le_trans`, `Rat.zero_le_one`, the `Eq`
//! built-ins) is `Constructive` with an empty domain-axiom closure, so this lemma
//! is too.
//!
//! `Declaration::Theorem`, `ProofQuality::Constructive`, empty admitted-axiom
//! closure (foundational only). NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural`. NO new axiom: the SOS is the prover's genuine identity,
//! the nonnegativity is genuine `Rat.sq_nonneg`. FORBIDDEN here: `Rat.dist`,
//! `Real`, `Real.sqrt`, `NNReal.sqrt`.

use super::algebra_rat_poly_prover::RatPolyProver;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Pre-resolved handles + smart-constructors for the cubed AM-GM (`Rat` level).
struct CubeAmGmConsts {
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    rat_le: Expr,
    sq_nonneg: Expr,
    mul_nonneg: Expr,
    le_add_of_nonneg_right: Expr,
    le_trans: Expr,
    zero_le_one: Expr,
    eq_symm1: Expr,
    eq_subst1: Expr,
}

impl CubeAmGmConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_sub: k("Rat.sub"),
            rat_le: k("Rat.le"),
            sq_nonneg: k("Rat.sq_nonneg"),
            mul_nonneg: k("Rat.mul_nonneg"),
            le_add_of_nonneg_right: k("Rat.le_add_of_nonneg_right"),
            le_trans: k("Rat.le_trans"),
            zero_le_one: k("Rat.zero_le_one"),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1]),
        }
    }

    fn add(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a.clone(), b.clone()])
    }
    fn mul(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a.clone(), b.clone()])
    }
    /// `Rat.sub a b` (the prover parses this as `a + (−b)`).
    fn sub(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a.clone(), b.clone()])
    }
    fn le(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a.clone(), b.clone()])
    }
    fn nonneg(&self, a: &Expr) -> Expr {
        self.le(&self.rat_zero, a)
    }
    /// `Rat.sq_nonneg a : Rat.le 0 (a·a)`.
    fn sq_nonneg(&self, a: &Expr) -> Expr {
        Expr::app(self.sq_nonneg.clone(), a.clone())
    }
    /// `Rat.mul_nonneg a b (0≤a)(0≤b) : Rat.le 0 (a·b)`.
    fn mul_nonneg(&self, a: &Expr, b: &Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a.clone(), b.clone(), ha, hb])
    }
    /// `Rat.le_add_of_nonneg_right a b (0≤b) : Rat.le a (a+b)`.
    fn le_add_of_nonneg_right(&self, a: &Expr, b: &Expr, hb: Expr) -> Expr {
        Expr::apps(
            self.le_add_of_nonneg_right.clone(),
            [a.clone(), b.clone(), hb],
        )
    }
    /// `Rat.le_trans a b c (a≤b)(b≤c) : Rat.le a c`.
    fn le_trans(&self, a: &Expr, b: &Expr, cc: &Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::apps(
            self.le_trans.clone(),
            [a.clone(), b.clone(), cc.clone(), hab, hbc],
        )
    }
    /// `@Eq.symm Rat a b h : Eq Rat b a`.
    fn symm(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_symm1.clone(),
            [self.rat.clone(), a.clone(), b.clone(), h],
        )
    }
    /// `@Eq.subst Rat motive a b h_eq h : motive b`.
    fn subst(&self, motive: Expr, a: &Expr, b: &Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a.clone(), b.clone(), h_eq, h],
        )
    }
}

impl Environment {
    /// Register `Rat.cube_amgm_two_one`. Idempotent; foundational-only closure.
    pub fn init_algebra_rat_cube_amgm(&mut self) -> Result<(), EnvError> {
        // The prover surface (Rat ring + Eq toolkit) and the order bricks it and
        // this assembly cite.
        self.init_algebra_rat_poly_prover()?; // RatPolyProver ring surface + Eq
        self.init_boolean_analysis_order_toolkit()?; // Rat.sq_nonneg, Rat.mul_nonneg
        self.init_algebra_nnreal_nnrat()?; // Rat.zero_le_one
                                           // Rat.le_add_of_nonneg_right + Rat.le_trans (the quotient order layer).
        self.init_rat_quotient_poc()?;

        let c = CubeAmGmConsts::new();
        self.register_cube_amgm_two_one(&c)?;
        Ok(())
    }

    fn register_cube_amgm_two_one(&mut self, c: &CubeAmGmConsts) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.cube_amgm_two_one");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let (ty, value) = build_cube_amgm_two_one(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the `Rat.cube_amgm_two_one` type and value.
fn build_cube_amgm_two_one(c: &CubeAmGmConsts) -> (Expr, Expr) {
    // The conclusion `Rat.le (27·(p·p·q)) (((2p+q)·(2p+q))·(2p+q))`, as a closure
    // over the two locals — used by both the type (Pi) and value (Lam). The terms
    // are built with the SAME `Rat.add`/`Rat.mul`/`Rat.one` heads the
    // `RatPolyProver` parses (so `prove_poly_eq` recognises them).
    let concl_of = |p: &Expr, q: &Expr| -> (Expr, Expr) {
        // numerals (exactly as RatPoly.test_ch3_sos writes them).
        let two = c.add(&c.rat_one, &c.rat_one);
        let two_p = c.mul(&two, p);
        let two_p_q = c.add(&two_p, q);
        let cube = c.mul(&c.mul(&two_p_q, &two_p_q), &two_p_q); // (2P+Q)³
        let p2q = c.mul(&c.mul(p, p), q); // P²Q
        let twenty_seven = numeral(c, 27);
        let term1 = c.mul(&twenty_seven, &p2q); // 27·P²Q
        (term1, cube)
    };

    let ty = {
        let mut tb = EnvDeclBuilder::new();
        let (p_id, p) = tb.fresh_local(c.rat.clone());
        let (q_id, q) = tb.fresh_local(c.rat.clone());
        let (term1, cube) = concl_of(&p, &q);
        let concl = c.le(&term1, &cube);
        let hb_ty = c.nonneg(&q);
        let (hb_id, _) = tb.fresh_local(hb_ty.clone());
        let ha_ty = c.nonneg(&p);
        let (ha_id, _) = tb.fresh_local(ha_ty.clone());
        let e = tb.mk_pi(hb_id, BinderInfo::Default, hb_ty, concl);
        let e = tb.mk_pi(ha_id, BinderInfo::Default, ha_ty, e);
        let e = tb.mk_pi(q_id, BinderInfo::Default, c.rat.clone(), e);
        let e = tb.mk_pi(p_id, BinderInfo::Default, c.rat.clone(), e);
        tb.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (p_id, p) = b.fresh_local(c.rat.clone());
        let (q_id, q) = b.fresh_local(c.rat.clone());
        let ha_ty = c.nonneg(&p);
        let (ha_id, ha) = b.fresh_local(ha_ty.clone());
        let hb_ty = c.nonneg(&q);
        let (hb_id, hb) = b.fresh_local(hb_ty.clone());

        let proof = build_cube_amgm_value(c, &b, &p, &q, ha, hb);

        let e = b.mk_lam(hb_id, BinderInfo::Default, hb_ty, proof);
        let e = b.mk_lam(ha_id, BinderInfo::Default, ha_ty, e);
        let e = b.mk_lam(q_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_lam(p_id, BinderInfo::Default, c.rat.clone(), e);
        b.finish(e)
    };

    (ty, value)
}

/// The cubed-AM-GM proof body (SOS identity + nonnegativity).
fn build_cube_amgm_value(
    c: &CubeAmGmConsts,
    b: &EnvDeclBuilder,
    p: &Expr,
    q: &Expr,
    ha: Expr,
    hb: Expr,
) -> Expr {
    // The prover instance over the two atoms; used ONLY to emit the SOS identity
    // proof (the terms themselves are built with the shared `Rat.*` heads so they
    // round-trip through `prove_poly_eq`'s `parse`).
    let pr = RatPolyProver::new(vec![p.clone(), q.clone()]);

    // ── the canonical reified terms (identical to RatPoly.test_ch3_sos) ──
    let two = c.add(&c.rat_one, &c.rat_one);
    let two_p = c.mul(&two, p);
    let two_p_q = c.add(&two_p, q);
    let cube = c.mul(&c.mul(&two_p_q, &two_p_q), &two_p_q); // (2P+Q)³

    let p2q = c.mul(&c.mul(p, p), q); // P²Q
    let twenty_seven = numeral(c, 27);
    let term1 = c.mul(&twenty_seven, &p2q); // 27·P²Q

    let p_minus_q = c.sub(p, q); // P−Q
    let pmq_sq = c.mul(&p_minus_q, &p_minus_q); // (P−Q)²
    let eight = numeral(c, 8);
    let eight_p = c.mul(&eight, p); // 8P
    let eight_p_q = c.add(&eight_p, q); // 8P+Q
    let term2 = c.mul(&pmq_sq, &eight_p_q); // (P−Q)²·(8P+Q)
    let rhs = c.add(&term1, &term2); // 27·P²Q + (P−Q)²·(8P+Q)

    // ── E : (2P+Q)³ = 27·P²Q + (P−Q)²·(8P+Q)  (the prover's SOS identity) ──
    let e_eq = pr
        .prove_poly_eq(b, &cube, &rhs)
        .expect("CH3 SOS is a polynomial identity (RatPoly.test_ch3_sos)");

    // ── 0 ≤ (P−Q)²  via Rat.sq_nonneg (P−Q) ──
    let h_pmq_sq = c.sq_nonneg(&p_minus_q);

    // ── 0 ≤ 8P+Q ──
    // 0 ≤ 8 (numeral chain) → 0 ≤ 8P (mul_nonneg) → 8P ≤ 8P+Q → 0 ≤ 8P+Q (trans).
    let h_eight = build_numeral_nonneg(c, 8);
    let h_eight_p = c.mul_nonneg(&eight, p, h_eight, ha.clone());
    let h_8p_le_sum = c.le_add_of_nonneg_right(&eight_p, q, hb.clone());
    let h_eight_p_q = c.le_trans(&c.rat_zero, &eight_p, &eight_p_q, h_eight_p, h_8p_le_sum);

    // ── 0 ≤ (P−Q)²·(8P+Q)  via Rat.mul_nonneg ──
    let h_term2 = c.mul_nonneg(&pmq_sq, &eight_p_q, h_pmq_sq, h_eight_p_q);

    // ── 27·P²Q ≤ 27·P²Q + (P−Q)²·(8P+Q)  via Rat.le_add_of_nonneg_right ──
    let h_le_rhs = c.le_add_of_nonneg_right(&term1, &term2, h_term2);

    // ── transport RHS back to (2P+Q)³ along symm E ──
    // goal : Rat.le term1 cube.  motive : fun w => Rat.le term1 w.
    let motive = {
        let mut mb = EnvDeclBuilder::child_of(b);
        let (w_id, w) = mb.fresh_local(c.rat.clone());
        let body = c.le(&term1, &w);
        mb.finish_child(mb.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), body))
    };
    c.subst(motive, &rhs, &cube, c.symm(&cube, &rhs, e_eq), h_le_rhs)
}

/// The numeral `n` (`n ≥ 1`) as a left-nested sum of `Rat.one` (matches the
/// `RatPolyProver`'s numeral form and `RatPoly.test_ch3_sos`).
fn numeral(c: &CubeAmGmConsts, n: u32) -> Expr {
    debug_assert!(n >= 1);
    let mut acc = c.rat_one.clone();
    for _ in 1..n {
        acc = c.add(&acc, &c.rat_one);
    }
    acc
}

/// `0 ≤ n` for the left-nested numeral `n` (`n ≥ 1`): base `Rat.zero_le_one`,
/// step `0 ≤ acc → acc ≤ acc+1 (le_add_of_nonneg_right) → 0 ≤ acc+1 (le_trans)`.
fn build_numeral_nonneg(c: &CubeAmGmConsts, n: u32) -> Expr {
    debug_assert!(n >= 1);
    let one = c.rat_one.clone();
    // base : 0 ≤ 1.
    let mut acc_expr = one.clone();
    let mut acc_proof = c.zero_le_one.clone(); // 0 ≤ 1
    for _ in 1..n {
        // acc ≤ acc+1 via le_add_of_nonneg_right acc 1 (0≤1).
        let next = c.add(&acc_expr, &one);
        let h_step = c.le_add_of_nonneg_right(&acc_expr, &one, c.zero_le_one.clone());
        // 0 ≤ acc+1 via le_trans 0 acc (acc+1).
        acc_proof = c.le_trans(&c.rat_zero, &acc_expr, &next, acc_proof, h_step);
        acc_expr = next;
    }
    acc_proof
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &["Rat.cube_amgm_two_one"];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_algebra_rat_cube_amgm()
            .expect("init_algebra_rat_cube_amgm");
        env.init_algebra_rat_cube_amgm().expect("idempotent");
        env
    }

    #[test]
    fn test_cube_amgm_two_one_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_cube_amgm_two_one_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be foundational-only: {:?}",
                env.axiom_deps(&nm)
            );
        }
    }
}
