// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami dual `(4/3, 4)` two-point base — leg (B) + the (A)-conditional
//! assembly that pins the whole two-point inequality to the single hard
//! lemma (A).
//!
//! # Where this sits (the M2 two-point base)
//!
//! The `n = 1` dual hypercontractivity inequality (the two-point base) is, at
//! `a = 1` (the homogeneity base case the parallel crux (A) lives at), the
//! `NNReal` inequality
//!
//! ```text
//!   ofRat (1 + (2/3)·b² + (1/81)·b⁴)  ≤  (½·(α + β))³,
//! ```
//!
//! where `α = |1+b|^{4/3}`, `β = |1−b|^{4/3}` (abstract nonneg carriers in the
//! PIN), and `H := ½·(α + β)` is the `pow43`-mean. With the rational pivot
//! `S := 1 + (2/9)·b²` the inequality splits into three independent rungs:
//!
//! - **(B)** `S³ ≥ LHS`  — PURE RATIONAL (this module). Verified:
//!   `S³ − LHS = (11/81)·b⁴ + (8/729)·b⁶ ≥ 0` (each summand a nonneg rational
//!   times an even power of `b`). Cleared-integer form with `w = b²`:
//!   `729·(S³ − LHS) = 99·w² + 8·w³ = w²·(99 + 8·w) ≥ 0`.
//! - **(C)** `H ≥ S ⟹ H³ ≥ S³`  — the landed `NNReal.cube_le_cube_of_le`.
//! - **(A)** `H ≥ S`  — the hard analytic crux (a PARALLEL agent attacks it; we
//!   take it as an EXPLICIT HYPOTHESIS, never as an axiom).
//!
//! # What this module registers (axiom-free, kernel-checked)
//!
//! - **(B)** `BoolAnalysis.two_point_S_cube_ge_moment : ∀ b : Rat,
//!     Rat.le (1 + (2/3)·(b·b) + (1/81)·((b·b)·(b·b)))
//!            (((S·S)·S))`   where `S := 1 + (2/9)·(b·b)`.
//!   Proved with `Rat.add_cube` (the `(1+c)³` expansion), the
//!   `Rat.mk`-coefficient `Quot.sound` bridges (lowest-terms collapses), and the
//!   nonneg toolkit (`Rat.le_add_of_nonneg_right`, `Rat.mul_nonneg`,
//!   `Rat.sq_nonneg`, `Rat.le_of_sub_nonneg`). No AM-GM, no analysis.
//!
//! - **assembly** `BoolAnalysis.two_point_base_43_of_A`: the conditional
//!   reduction
//!   ```text
//!     ∀ (b : Rat)(α β : NNReal)(hm : 0 ≤ LHS)(hS : 0 ≤ S)
//!       (hA : NNReal.le (NNReal.ofRat S hS) (½·(α+β))),
//!         NNReal.le (NNReal.ofRat LHS hm) (((H·H)·H))
//!   ```
//!   chaining (B) → `ofRat`-monotone → the `ofRat`-cube homomorphism
//!   (`ofRat (S³) = (ofRat S)³`) → (C). This DISCHARGES the a=1 instance of the
//!   landed `two_point_base_43` PIN MODULO `hA = (A)`. (A) is an explicit
//!   hypothesis (like `two_norm_sq_le_of_holder_chain`'s Hölder premise), NOT an
//!   axiom and NOT a refl-over-circular-def.
//!
//! Each theorem is `Declaration::Theorem`, `ProofQuality::Constructive`, empty
//! admitted-axiom closure (foundational only). NO `sorry` / `add_decl_unchecked`
//! / `add_decl_structural` / `native_decide` / `unsafe` / Axiom. FORBIDDEN:
//! `Rat.dist`, `Real`/`Real.sqrt`.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached carrier atoms + smart-constructors for leg (B) and the assembly.
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
struct TwoPointLegConsts {
    // Nat / Int (literal `Rat.mk` fractions).
    nat_zero: Expr,
    nat_succ: Expr,
    int: Expr,
    int_of_nat: Expr,
    // Rat carrier + ring/order surface.
    rat: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mk: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    #[cfg(test)]
    rat_sub: Expr,
    rat_le: Expr,
    rat_add_cube: Expr,
    #[cfg(test)]
    rat_left_distrib: Expr,
    rat_right_distrib: Expr,
    #[cfg(test)]
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    rat_add_assoc: Expr,
    rat_one_mul: Expr,
    rat_mul_one: Expr,
    #[cfg(test)]
    rat_le_of_sub_nonneg: Expr,
    rat_le_add_of_nonneg_right: Expr,
    rat_le_trans: Expr,
    rat_mul_nonneg: Expr,
    rat_sq_nonneg: Expr,
    rat_le_of_ble_eq_true: Expr,
    bool_c: Expr,
    bool_true: Expr,
    // Rat.Raw quotient bridge.
    raw: Expr,
    raw_mk: Expr,
    raw_equiv: Expr,
    quot_mk1: Expr,
    quot_sound1: Expr,
    // Eq.{1}.
    eq1: Expr,
    eq_refl1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
    congr_arg11: Expr,
    // NNReal carrier.
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_add: Expr,
    nnreal_le: Expr,
    nnreal_of_rat: Expr,
    nnreal_ofrat_le_ofrat: Expr,
    nnreal_ofrat_mul: Expr,
    nnreal_cube_le_cube_of_le: Expr,
    nnreal_le_trans: Expr,
}

#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
impl TwoPointLegConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let kl = |s: &str| Expr::const_(Name::from_string(s), vec![l1.clone()]);
        Self {
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int: k("Int"),
            int_of_nat: k("Int.ofNat"),
            rat: k("Rat"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mk: k("Rat.mk"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            #[cfg(test)]
            rat_sub: k("Rat.sub"),
            rat_le: k("Rat.le"),
            rat_add_cube: k("Rat.add_cube"),
            #[cfg(test)]
            rat_left_distrib: k("Rat.left_distrib"),
            rat_right_distrib: k("Rat.right_distrib"),
            #[cfg(test)]
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_add_assoc: k("Rat.add_assoc"),
            rat_one_mul: k("Rat.one_mul"),
            rat_mul_one: k("Rat.mul_one"),
            #[cfg(test)]
            rat_le_of_sub_nonneg: k("Rat.le_of_sub_nonneg"),
            rat_le_add_of_nonneg_right: k("Rat.le_add_of_nonneg_right"),
            rat_le_trans: k("Rat.le_trans"),
            rat_mul_nonneg: k("Rat.mul_nonneg"),
            rat_sq_nonneg: k("Rat.sq_nonneg"),
            rat_le_of_ble_eq_true: k("Rat.le_of_ble_eq_true"),
            bool_c: k("Bool"),
            bool_true: k("Bool.true"),
            raw: k("Rat.Raw"),
            raw_mk: k("Rat.Raw.mk"),
            raw_equiv: k("Rat.Raw.Equiv"),
            quot_mk1: kl("Quot.mk"),
            quot_sound1: kl("Quot.sound"),
            eq1: kl("Eq"),
            eq_refl1: kl("Eq.refl"),
            eq_symm1: kl("Eq.symm"),
            eq_trans1: kl("Eq.trans"),
            eq_subst1: kl("Eq.subst"),
            congr_arg11: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_add: k("NNReal.add"),
            nnreal_le: k("NNReal.le"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_ofrat_le_ofrat: k("NNReal.ofRat_le_ofRat"),
            nnreal_ofrat_mul: k("NNReal.ofRat_mul"),
            nnreal_cube_le_cube_of_le: k("NNReal.cube_le_cube_of_le"),
            nnreal_le_trans: k("NNReal.le.trans"),
        }
    }

    // ── Rat term constructors ────────────────────────────────────────────────
    fn nat_lit(&self, n: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..n {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    /// `Rat.mk (Int.ofNat num) den`.
    fn frac(&self, num: u64, den: u64) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(num)),
                self.nat_lit(den),
            ],
        )
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    #[cfg(test)]
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn nonneg(&self, a: Expr) -> Expr {
        self.le(self.rat_zero.clone(), a)
    }
    /// `(a·a)·a`.
    fn cube(&self, a: &Expr) -> Expr {
        let sq = self.mul(a.clone(), a.clone());
        self.mul(sq, a.clone())
    }

    // ── Eq.{1} over Rat ──────────────────────────────────────────────────────
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    fn refl_rat(&self, a: Expr) -> Expr {
        Expr::apps(self.eq_refl1.clone(), [self.rat.clone(), a])
    }
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    #[cfg(test)]
    fn congr_rat(&self, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg11.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// Congruence via `Eq.subst` with motive `fun t => Eq ctx[a] ctx[t]`, where
    /// `ctx[·]` is a one-hole context. The result type is the BETA-NORMAL
    /// `Eq ctx[a] ctx[b]` (the `subst`'s `refl ctx[a]` seeds the LHS and the
    /// motive's `b`-instance the RHS), avoiding the residual `congrArg` redex.
    fn congr_ctx(
        &self,
        parent: &EnvDeclBuilder,
        ctx: impl Fn(&Self, &Expr) -> Expr,
        a: Expr,
        b: Expr,
        h: Expr,
    ) -> Expr {
        let ctx_a = ctx(self, &a);
        let motive = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (t_id, t) = d.fresh_local(self.rat.clone());
            let body = self.eq_rat(ctx_a.clone(), ctx(self, &t));
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.subst_rat(motive, a, b, h, self.refl_rat(ctx_a))
    }
    /// `ctx[t] = l + t` (rewrites the RIGHT summand): result `(l+a) = (l+b)`.
    fn congr_add_right(
        &self,
        parent: &EnvDeclBuilder,
        l: &Expr,
        a: Expr,
        b: Expr,
        h: Expr,
    ) -> Expr {
        let l = l.clone();
        self.congr_ctx(parent, move |s, t| s.add(l.clone(), t.clone()), a, b, h)
    }
    /// `ctx[t] = t + r` (rewrites the LEFT summand): result `(a+r) = (b+r)`.
    fn congr_add_left(&self, parent: &EnvDeclBuilder, r: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let r = r.clone();
        self.congr_ctx(parent, move |s, t| s.add(t.clone(), r.clone()), a, b, h)
    }
    /// `ctx[t] = l · t` (rewrites the RIGHT factor): result `(l·a) = (l·b)`.
    fn congr_mul_right(
        &self,
        parent: &EnvDeclBuilder,
        l: &Expr,
        a: Expr,
        b: Expr,
        h: Expr,
    ) -> Expr {
        let l = l.clone();
        self.congr_ctx(parent, move |s, t| s.mul(l.clone(), t.clone()), a, b, h)
    }
    /// `ctx[t] = t · r` (rewrites the LEFT factor): result `(a·r) = (b·r)`.
    fn congr_mul_left(&self, parent: &EnvDeclBuilder, r: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let r = r.clone();
        self.congr_ctx(parent, move |s, t| s.mul(t.clone(), r.clone()), a, b, h)
    }

    // ── ring/order bricks ────────────────────────────────────────────────────
    fn add_cube(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_add_cube.clone(), [a.clone(), b.clone()])
    }
    fn mul_assoc(&self, a: &Expr, b: &Expr, cc: &Expr) -> Expr {
        Expr::apps(
            self.rat_mul_assoc.clone(),
            [a.clone(), b.clone(), cc.clone()],
        )
    }
    #[cfg(test)]
    fn mul_comm(&self, a: &Expr, b: &Expr) -> Expr {
        Expr::apps(self.rat_mul_comm.clone(), [a.clone(), b.clone()])
    }
    fn one_mul(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_one_mul.clone(), a.clone())
    }
    fn mul_one(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_mul_one.clone(), a.clone())
    }
    /// `Rat.mul_nonneg a b (0≤a)(0≤b) : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: &Expr, b: &Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.rat_mul_nonneg.clone(), [a.clone(), b.clone(), ha, hb])
    }
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    fn sq_nonneg(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_sq_nonneg.clone(), a.clone())
    }
    /// `Rat.le_add_of_nonneg_right a b (0≤b) : a ≤ a + b`.
    fn le_add_of_nonneg_right(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(
            self.rat_le_add_of_nonneg_right.clone(),
            [a.clone(), b.clone(), h],
        )
    }
    /// `Rat.le_of_sub_nonneg a b (0 ≤ b−a) : a ≤ b`.
    #[cfg(test)]
    fn le_of_sub_nonneg(&self, a: &Expr, b: &Expr, h: Expr) -> Expr {
        Expr::apps(self.rat_le_of_sub_nonneg.clone(), [a.clone(), b.clone(), h])
    }
    /// `Rat.le_trans a b c (a≤b)(b≤c) : a ≤ c`.
    fn le_trans(&self, a: &Expr, b: &Expr, cc: &Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.rat_le_trans.clone(),
            [a.clone(), b.clone(), cc.clone(), h1, h2],
        )
    }
    /// `0 ≤ Rat.mk (Int.ofNat num) den` for a positive literal fraction, via
    /// `Rat.le_of_ble_eq_true Rat.zero (num/den) (Eq.refl Bool Bool.true)`.
    /// `Rat.ble Rat.zero (mk num den)` ground-reduces to `Bool.true`, so the
    /// `Eq.refl` witnesses `Rat.ble … = Bool.true` definitionally.
    fn lit_nonneg(&self, num: u64, den: u64) -> Expr {
        let frac = self.frac(num, den);
        let refl_true = Expr::apps(
            self.eq_refl1.clone(),
            [self.bool_c.clone(), self.bool_true.clone()],
        );
        Expr::apps(
            self.rat_le_of_ble_eq_true.clone(),
            [self.rat_zero.clone(), frac, refl_true],
        )
    }

    /// A `Quot.sound`-bridge `mk pn pd = mk qn qd` for equal fractions
    /// (`pn·qd = qn·pd` as `Int.ofNat`, witnessed by `Eq.refl (Int.ofNat prod)`).
    fn frac_bridge(&self, pn: u64, pd: u64, qn: u64, qd: u64, prod: u64) -> Expr {
        let raw_l = Expr::apps(
            self.raw_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(pn)),
                self.nat_lit(pd),
            ],
        );
        let raw_r = Expr::apps(
            self.raw_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(qn)),
                self.nat_lit(qd),
            ],
        );
        let equiv_proof = Expr::apps(
            self.eq_refl1.clone(),
            [
                self.int.clone(),
                Expr::app(self.int_of_nat.clone(), self.nat_lit(prod)),
            ],
        );
        let sound = Expr::apps(
            self.quot_sound1.clone(),
            [
                self.raw.clone(),
                self.raw_equiv.clone(),
                raw_l.clone(),
                raw_r.clone(),
                equiv_proof,
            ],
        );
        let mk_l = Expr::apps(
            self.quot_mk1.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), raw_l],
        );
        let mk_r = Expr::apps(
            self.quot_mk1.clone(),
            [self.raw.clone(), self.raw_equiv.clone(), raw_r],
        );
        let lhs = self.frac(pn, pd);
        let rhs = self.frac(qn, qd);
        let to_l = self.refl_rat(lhs.clone());
        let from_r = self.refl_rat(rhs.clone());
        let s1 = self.trans_rat(lhs.clone(), mk_l, mk_r.clone(), to_l, sound);
        self.trans_rat(lhs, mk_r, rhs, s1, from_r)
    }

    // ── NNReal constructors ──────────────────────────────────────────────────
    fn nnmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_mul.clone(), [a, b])
    }
    fn nnadd(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_add.clone(), [a, b])
    }
    fn nnle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nnreal_le.clone(), [a, b])
    }
    fn nncube(&self, a: &Expr) -> Expr {
        self.nnmul(self.nnmul(a.clone(), a.clone()), a.clone())
    }
    fn ofrat(&self, x: &Expr, h: &Expr) -> Expr {
        Expr::apps(self.nnreal_of_rat.clone(), [x.clone(), h.clone()])
    }
    #[cfg(test)]
    fn eq_nn(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.nnreal.clone(), a, b])
    }
    fn subst_nn(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.nnreal.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `@Eq.trans.{1} NNReal a b c h1 h2 : a = c`.
    fn trans_rat_nn(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            self.eq_trans1.clone(),
            [self.nnreal.clone(), a, b, cc, h1, h2],
        )
    }
    /// `@Eq.symm.{1} NNReal a b h : b = a`.
    fn symm_nn(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.nnreal.clone(), a, b, h])
    }
}

include!("boolean_analysis_two_point_base_legs_b.rs");
include!("boolean_analysis_two_point_base_legs_assembly.rs");

impl Environment {
    /// Initialize leg (B) + the (A)-conditional assembly of the two-point base.
    ///
    /// Registers `BoolAnalysis.two_point_S_cube_ge_moment` (leg B, pure rational)
    /// and `BoolAnalysis.two_point_base_43_of_A` (the conditional reduction to
    /// the single hard lemma (A)). Idempotent. No axiom added or removed.
    pub fn init_boolean_analysis_two_point_base_legs(&mut self) -> Result<(), EnvError> {
        // (B) deps: add_cube + the full Rat ring/order surface, plus the nonneg
        // and sub bricks.
        self.init_algebra_rat_cube_identity()?; // Rat.add_cube, ring + order surface
        self.init_rat_quotient_poc()?; // Rat.le_add_of_nonneg_right, distrib, le_trans
        self.init_boolean_analysis_order_toolkit()?; // Rat.sq_nonneg, Rat.mul_nonneg
        self.init_nn_verify_rat_ordering()?; // Rat.le_of_sub_nonneg
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true (literal nonneg)
        self.register_rat_mul_mul_mul_comm_theorem()?; // Rat.mul_mul_mul_comm (c² regroup)
                                                       // assembly deps: the ofRat order/homomorphism + the cube monotone.
        self.init_algebra_nnreal_add()?; // NNReal.add (the ½·(α+β) mean)
        self.init_algebra_nnreal_le()?; // NNReal.le, NNReal.ofRat, ofRat_le_ofRat, le.refl
        self.init_algebra_nnreal_reverse_square_algebra()?; // NNReal.ofRat_mul
        self.init_algebra_nnreal_cube_mono()?; // NNReal.cube_le_cube_of_le, le.trans
        self.init_eq()?;

        let c = TwoPointLegConsts::new();
        self.register_two_point_s_cube_ge_moment(&c)?;
        self.register_two_point_base_43_of_a(&c)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const THEOREMS: &[&str] = &[
        "BoolAnalysis.two_point_S_cube_ge_moment",
        "BoolAnalysis.two_point_base_43_of_A",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_two_point_base_legs()
            .expect("init_boolean_analysis_two_point_base_legs");
        env.init_boolean_analysis_two_point_base_legs()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_two_point_base_legs_kernel_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
            let value = info.value.clone().expect("value present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        }
    }

    #[test]
    fn test_two_point_base_legs_constructive_empty_closure() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
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

    /// Fence: each registered decl checks via `self.add_decl` (done in `env()`),
    /// and the proof value contains no closure/free-variable leak (an empty
    /// admitted-axiom closure is asserted above).
    #[test]
    fn test_two_point_base_legs_empty_closure_fence() {
        let env = env();
        for name in THEOREMS {
            let nm = Name::from_string(name);
            let info = env.get_const(&nm).expect("registered");
            assert!(info.value.is_some(), "{name} must carry a proof term");
        }
    }
}
