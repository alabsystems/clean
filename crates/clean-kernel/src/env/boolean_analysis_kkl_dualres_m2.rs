// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` bound — Stage C-3 RESIDUAL component **M2**, the dual
//! hypercontractive bound `f4 = Σ_x pow4(T_{1/9}g x) ≤ 16·count³`, reduced to its
//! genuine remaining ingredients along the *contraction* route (NOT the forward
//! `hc24_at_third` route — see the `8^n` verdict below).
//!
//! # Where this sits
//!
//! `BoolAnalysis.two_norm_sq_le_of_holder_chain`
//! (`boolean_analysis_kkl_dualbound_assemble.rs`) is the §9.6 conditional
//! reduction of the dual `(4/3→2)` bound to three hypotheses; its **`h_m2`** is
//! the dual `(4/3→4)` hypercontractivity `f4 ≤ b43` (`= ‖T_{1/9}g‖₄⁴ ≤
//! ‖g‖_{4/3}⁴ = 16·count³`). This module discharges `h_m2`'s arithmetic spine
//! down to the SINGLE genuinely-missing analytic fact — the spectral 2-norm
//! contraction `Σ_x sq(T_{1/9}g) ≤ Σ_x sq(g) = 4·count` — by the elementary
//! `‖·‖₄ ≤ ‖·‖₂` sequence chain, which avoids hypercontractivity (and its `8^n`)
//! entirely:
//!
//! ```text
//!   f4 = Σ_x z⁴        ≤  (Σ_x z²)²            [s4 ≤ s2², the ‖·‖₄≤‖·‖₂ shadow]
//!                      ≤  (4·count)²  = 16·count²  [2-norm contraction, z := T_{1/9}g]
//!                      ≤  16·count³            [count ≥ 1 monotone charge]
//! ```
//!
//! # The `8^n` verdict (design `2026-06-18-kkl-real-sqrt-layer-plan.md` §10.6)
//!
//! Route A (`hc24_at_third` at `F := T_{1/3}g`) is the FORWARD `(2→4)` bound
//! `Σ_jx pow4(noiseFn (1/3) n F jx) ≤ 8^n · (Σ_jx sq(F))²`. Because
//! `noiseFn (1/3) n F = 2^n · T_{1/3}F` and `pow4` carries `(2^n)⁴ = 16^n`, the
//! carrier LHS is `16^n · Σ_x (T_{1/9}g x)⁴ = 16^n · f4`. Dividing the carrier's
//! `16^n` against the RHS `8^n` leaves a `8^n/16^n = 1/2^n` factor, so the
//! NORMALIZED operator bound is `f4 ≤ (1/2^n)·(Σ_jx sq(T_{1/3}g))²` — i.e. the
//! `8^n` does NOT diverge; it cancels to a *strengthening* `1/2^n`. **So the
//! `8^n` is NOT fatal arithmetically.** Route A is nonetheless not directly
//! buildable axiom-free: it requires materialising `T_{1/3}g` as an `HCPoint n →
//! Rat` carrier (`applyT (1/3) g`, absent from the overlay) plus the Fubini /
//! semigroup bridge `noiseFn (1/3) (applyT (1/3) g) = 2^n·T_{1/9}g` (the §10.6
//! "secondary, shape mismatch" residual). The genuine dual `(4/3→4)`
//! hypercontractivity (Route B) is a SEPARATE theorem at the dual endpoint
//! `q = 4/3` — `hc24_core` is the `(2,4)`-endpoint two-point induction and is NOT
//! a re-instantiation of it. The CONTRACTION route this module pins reaches the
//! same `f4 ≤ 16·count³` with NO hypercontractivity at all (the only `(2→4)`
//! content, `s4 ≤ s2²`, is the trivial `‖·‖₄ ≤ ‖·‖₂`), so the residual is just
//! the 2-norm contraction `Σ sq(T_{1/9}g) ≤ Σ sq(g)`.
//!
//! # What this module proves (axiom-free, kernel-checked)
//!
//! ```text
//! BoolAnalysis.m2_from_contraction :
//!   ∀ (f4 s2 count : Rat),
//!     Rat.le Rat.zero count →                 -- 0 ≤ count
//!     Rat.le Rat.one  count →                 -- 1 ≤ count (nonzero disagree-set)
//!     Rat.le f4 s2 →                          -- (H1) Σz⁴ ≤ s2 := (Σz²)²
//!     Rat.le s2 (Rat.mul (Rat.mul 16 count) count) →  -- (H2) (Σ sq T_{1/9}g)² ≤ 16·count²
//!     Rat.le f4 (Rat.mul (Rat.mul 16 count) (Rat.mul count count))  -- ⟹ f4 ≤ 16·count³
//! ```
//!
//! The conclusion `16·count³ := (16·count)·(count·count)` is built byte-for-byte
//! from the consumer `cube16(count)` in `boolean_analysis_kkl_dualbound_assemble.rs`,
//! so this lemma's output is def-eq to the `h_m2`/`h_m1` shape there.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! With `c16 := 16`, `S16 := c16·count` (`= 16·count`), `sq := count·count`,
//! `cube := S16·sq` (the consumer cube), and `m2 := S16·count` (`= 16·count²`):
//!
//! 1. `step_f4 : f4 ≤ m2` — `Rat.le_trans f4 s2 m2 H1 H2` (`H2 : s2 ≤ m2`).
//! 2. `0 ≤ 16` via the boolean order reflection `Rat.le_of_ble_eq_true 0 16 rfl`.
//! 3. `0 ≤ S16 := Rat.mul_nonneg 16 count h16 h_count0`.
//! 4. `count ≤ sq` — from `1 ≤ count` (`h_count1`): `Rat.mul_le_mul_of_nonneg_right
//!    count Rat.one count h_count1 h_count0 : 1·count ≤ count·count`, transported
//!    along `Rat.one_mul count : 1·count = count` by `Eq.subst` (motive
//!    `z ↦ z ≤ count·count`).
//! 5. `m2 ≤ cube` — `Rat.mul_le_mul_of_nonneg_left S16 count sq h_count_le_sq h_S16
//!    : S16·count ≤ S16·sq`.
//! 6. `f4 ≤ cube := Rat.le_trans f4 m2 cube step_f4 charge`.
//!
//! Every leaf (`Rat.le_trans`, `Rat.mul_nonneg`, `Rat.mul_le_mul_of_nonneg_left`,
//! `Rat.mul_le_mul_of_nonneg_right`, `Rat.one_mul`, `Rat.le_of_ble_eq_true`,
//! `Eq.subst`, `Eq.refl`) is `Constructive` with empty admitted-axiom closure, so
//! this reduction is too.
//!
//! # The residual (the ONE genuinely-missing analytic fact)
//!
//! - **H1** `f4 ≤ (Σz²)²` is the elementary `Σ z⁴ ≤ (Σ z²)²` (`‖·‖₄ ≤ ‖·‖₂`):
//!   `(Σz²)² = Σ_x Σ_y z(x)²z(y)² ≥ Σ_x z(x)⁴` by dropping the nonneg
//!   off-diagonal — axiom-free but a `subsetSum` self-product + diagonal-extract
//!   sub-build (UNBUILT).
//! - **H2** `(Σ sq(T_{1/9}g))² ≤ 16·count²` ⟸ the 2-norm contraction
//!   `Σ_x sq(T_{1/9}g) ≤ Σ_x sq(g) = 4·count` (spectral term-wise `(1/9)^{2|S|} ≤
//!   1` domination + `deriv_sq_sum_eq_four_disagree`) squared — the GENUINE
//!   remaining analytic residual of M2 (no irrationals, no hypercontractivity;
//!   UNBUILT).

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached atoms for the M2 contraction-route reduction.
struct M2Consts {
    o: OrderConsts,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    one_mul: Expr,
    mul_nonneg: Expr,
    mul_le_left: Expr,
    mul_le_right: Expr,
    le_trans: Expr,
}

impl M2Consts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            o: OrderConsts::new(),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            one_mul: k("Rat.one_mul"),
            mul_nonneg: k("Rat.mul_nonneg"),
            mul_le_left: k("Rat.mul_le_mul_of_nonneg_left"),
            mul_le_right: k("Rat.mul_le_mul_of_nonneg_right"),
            le_trans: k("Rat.le_trans"),
        }
    }

    fn rat(&self) -> Expr {
        self.o.rat.clone()
    }
    fn zero(&self) -> Expr {
        self.o.rat_zero.clone()
    }
    fn one(&self) -> Expr {
        self.o.rat_one.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.o.mul(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.o.rat_le(a, b)
    }
    /// The literal `16 : Rat` as `Rat.mk (Int.ofNat 16) 1` (byte-for-byte the
    /// consumer `AssembleConsts::lit16`, so the cube outputs are def-eq).
    fn lit16(&self) -> Expr {
        let mut nat16 = self.nat_zero.clone();
        for _ in 0..16 {
            nat16 = Expr::app(self.nat_succ.clone(), nat16);
        }
        let one_nat = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), nat16), one_nat],
        )
    }
    /// `Rat.one_mul a : Rat.one · a = a`.
    fn one_mul(&self, a: Expr) -> Expr {
        Expr::app(self.one_mul.clone(), a)
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(self.mul_nonneg.clone(), [a, b, ha, hb])
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c (h:b≤c)(h0:0≤a) : a·b ≤ a·c`.
    fn mul_le_left(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.mul_le_left.clone(), [a, b, cc, h, h0])
    }
    /// `Rat.mul_le_mul_of_nonneg_right a b c (h:b≤c)(h0:0≤a) : b·a ≤ c·a`.
    fn mul_le_right(&self, a: Expr, b: Expr, cc: Expr, h: Expr, h0: Expr) -> Expr {
        Expr::apps(self.mul_le_right.clone(), [a, b, cc, h, h0])
    }
    /// `Rat.le_trans a b c (h1:a≤b)(h2:b≤c) : a ≤ c`.
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.le_trans.clone(), [a, b, cc, h1, h2])
    }
}

impl Environment {
    /// Register `BoolAnalysis.m2_from_contraction` — the M2 hypercontractive
    /// bound `f4 ≤ 16·count³` reduced (axiom-free, via the `‖·‖₄ ≤ ‖·‖₂`
    /// contraction route, NO hypercontractivity / NO `8^n`) to its two genuine
    /// remaining facts: `f4 ≤ (Σz²)²` (H1) and the 2-norm contraction shadow
    /// `(Σz²)² ≤ 16·count²` (H2), under `0 ≤ count` and `1 ≤ count`.
    /// Kernel-checked, `ProofQuality::Constructive`, empty admitted-axiom closure.
    /// Idempotent.
    pub fn register_m2_from_contraction(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.m2_from_contraction");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_{left,right}
        self.register_rat_order_proofs()?; // le_trans, mul_nonneg
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true (0 ≤ 16)
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // Rat.one_mul
        }

        let c = M2Consts::new();
        let (ty, value) = build_m2(&c);
        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Build the type + proof of `BoolAnalysis.m2_from_contraction`.
fn build_m2(c: &M2Consts) -> (Expr, Expr) {
    // `16·count²` (the M2 intermediate) and `16·count³` (the consumer cube).
    let m2_of = |count: &Expr| -> Expr {
        let s16 = c.mul(c.lit16(), count.clone());
        c.mul(s16, count.clone())
    };
    let cube_of = |count: &Expr| -> Expr {
        let s16 = c.mul(c.lit16(), count.clone());
        c.mul(s16, c.mul(count.clone(), count.clone()))
    };

    let ty = {
        let mut b = EnvDeclBuilder::new();
        let (f4_id, f4) = b.fresh_local(c.rat());
        let (s2_id, s2) = b.fresh_local(c.rat());
        let (cnt_id, cnt) = b.fresh_local(c.rat());

        let h0_ty = c.le(c.zero(), cnt.clone()); // 0 ≤ count
        let h1c_ty = c.le(c.one(), cnt.clone()); // 1 ≤ count
        let hf1_ty = c.le(f4.clone(), s2.clone()); // f4 ≤ s2
        let hf2_ty = c.le(s2.clone(), m2_of(&cnt)); // s2 ≤ 16·count²
        let concl = c.le(f4.clone(), cube_of(&cnt)); // f4 ≤ 16·count³

        let (hf2_id, _) = b.fresh_local(hf2_ty.clone());
        let e = b.mk_pi(hf2_id, BinderInfo::Default, hf2_ty, concl);
        let (hf1_id, _) = b.fresh_local(hf1_ty.clone());
        let e = b.mk_pi(hf1_id, BinderInfo::Default, hf1_ty, e);
        let (h1c_id, _) = b.fresh_local(h1c_ty.clone());
        let e = b.mk_pi(h1c_id, BinderInfo::Default, h1c_ty, e);
        let (h0_id, _) = b.fresh_local(h0_ty.clone());
        let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
        let e = b.mk_pi(cnt_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(s2_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(f4_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (f4_id, f4) = b.fresh_local(c.rat());
        let (s2_id, s2) = b.fresh_local(c.rat());
        let (cnt_id, cnt) = b.fresh_local(c.rat());

        let h0_ty = c.le(c.zero(), cnt.clone());
        let h1c_ty = c.le(c.one(), cnt.clone());
        let hf1_ty = c.le(f4.clone(), s2.clone());
        let hf2_ty = c.le(s2.clone(), m2_of(&cnt));

        let (h0_id, h_count0) = b.fresh_local(h0_ty.clone());
        let (h1c_id, h_count1) = b.fresh_local(h1c_ty.clone());
        let (hf1_id, h_f1) = b.fresh_local(hf1_ty.clone());
        let (hf2_id, h_f2) = b.fresh_local(hf2_ty.clone());

        let s16 = c.mul(c.lit16(), cnt.clone()); // 16·count
        let cnt_sq = c.mul(cnt.clone(), cnt.clone()); // count·count
        let m2 = m2_of(&cnt); // 16·count²
        let cube = cube_of(&cnt); // 16·count³

        // step_f4 : f4 ≤ 16·count²  (le_trans f4 s2 m2 H1 H2)
        let step_f4 = c.le_trans(f4.clone(), s2.clone(), m2.clone(), h_f1, h_f2);

        // 0 ≤ 16, then 0 ≤ 16·count.
        let h16 = h16_nonneg(c);
        let h_s16 = c.mul_nonneg(c.lit16(), cnt.clone(), h16, h_count0.clone());

        // count ≤ count·count from 1 ≤ count:
        //   one_mul_le : 1·count ≤ count·count  (mul_le_right count 1 count h_count1 h_count0)
        //   subst along Rat.one_mul count : 1·count = count  (motive z ↦ z ≤ count·count)
        let one_count = c.mul(c.one(), cnt.clone()); // 1·count
        let one_mul_le = c.mul_le_right(
            cnt.clone(),
            c.one(),
            cnt.clone(),
            h_count1,
            h_count0.clone(),
        );
        let h_count_le_sq = {
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (z_id, z) = d.fresh_local(c.rat());
                let body = c.le(z, cnt_sq.clone());
                d.finish_child(d.mk_lam(z_id, BinderInfo::Default, c.rat(), body))
            };
            // Rat.one_mul count : 1·count = count
            let h_one_mul = c.one_mul(cnt.clone());
            c.o.subst(motive, one_count, cnt.clone(), h_one_mul, one_mul_le)
        };

        // charge : 16·count² ≤ 16·count³  (mul_le_left S16 count (count·count) h_count_le_sq h_S16)
        let charge = c.mul_le_left(
            s16.clone(),
            cnt.clone(),
            cnt_sq.clone(),
            h_count_le_sq,
            h_s16,
        );
        // proof : f4 ≤ 16·count³  (le_trans f4 m2 cube step_f4 charge)
        let proof = c.le_trans(f4.clone(), m2, cube, step_f4, charge);

        let e = b.mk_lam(hf2_id, BinderInfo::Default, hf2_ty, proof);
        let e = b.mk_lam(hf1_id, BinderInfo::Default, hf1_ty, e);
        let e = b.mk_lam(h1c_id, BinderInfo::Default, h1c_ty, e);
        let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
        let e = b.mk_lam(cnt_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_lam(s2_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_lam(f4_id, BinderInfo::Default, c.rat(), e);
        b.finish(e)
    };

    (ty, value)
}

/// `0 ≤ (16 : Rat)` via the boolean order reflection `Rat.le_of_ble_eq_true 0 16
/// (Eq.refl Bool.true)` — `Rat.ble 0 16` native-reduces to `true` on the concrete
/// `Rat.mk` reps, so `Eq.refl Bool.true` checks (the idiom of `hc24_at_third` /
/// the dual-bound assembler).
fn h16_nonneg(c: &M2Consts) -> Expr {
    let le_of_ble = Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]);
    let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let refl = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![crate::level::Level::succ(crate::level::Level::zero())],
        ),
        [bool_ty, bool_true],
    );
    Expr::apps(le_of_ble, [c.zero(), c.lit16(), refl])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::carrier_refutation::refute_conjecture;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.register_m2_from_contraction()
            .expect("register_m2_from_contraction");
        env
    }

    #[test]
    fn test_m2_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.m2_from_contraction");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "must be a CHECKED Theorem, not an axiom"
        );
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("proof must check against its type: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be empty (foundational-only), got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_m2_from_contraction().expect("first");
        env.register_m2_from_contraction().expect("idempotent");
    }

    /// THE TARGET-REFUTATION GATE. The M2 contraction reduction is a TRUE
    /// implication: from `f4 ≤ s2`, `s2 ≤ 16·count²`, `1 ≤ count` (so
    /// `count ≤ count²` ⟹ `16·count² ≤ 16·count³`) and `0 ≤ count`,
    /// `f4 ≤ 16·count³` for EVERY assignment — no carrier instance can break it,
    /// so `refute_conjecture` must NOT manufacture a counterexample.
    ///
    /// By hand (tribes / dictator sanity): for the dictator derivative `g ≡ 2`
    /// on `n` coords, `count = 2^n`, `s2 = Σ sq(T_{1/9}g)·… ≤ 16·count²`, and
    /// `16·count³ ≥ 16·count² ≥ f4` since `count = 2^n ≥ 1`. The implication never
    /// fails.
    #[test]
    fn test_m2_not_refuted() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.m2_from_contraction"))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "the M2 contraction reduction is a TRUE implication; must NOT refute"
        );
    }
}
