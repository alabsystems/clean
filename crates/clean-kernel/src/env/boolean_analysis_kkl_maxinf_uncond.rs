// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL UNCONDITIONAL strengthening — the large-influence dichotomy.
//!
//! Discharges the small-influence premises of the conditional sharp-KKL bound
//! [`kkl_exists_max_influence`] via the `δ := 1/(P+1)` rational trick (with
//! `P := (k+1)·9^k`) and a `Classical.em` large-influence case split, yielding
//! the UNCONDITIONAL max-influence inequality:
//!
//! ```text
//! BoolAnalysis.kkl_exists_max_influence_uncond :
//!   ∀ (n k : Nat) (f : BoolFn n),
//!     Rat.le (Rat.mul (natCast (Nat.succ k)) (Rat.mul Q Q))   -- (k+1)·(P+1)² ≤ 2n
//!            (Rat.add (natCast n) (natCast n))                 --   [Rat threshold]
//!     → Nat.le (Nat.succ Nat.zero) n                          -- 0 < n
//!     → (∀ i, Rat.le Rat.zero (Influence n f i))
//!     → Exists (i : Fin n)
//!         (Rat.le (Rat.mul (natCast (Nat.succ k)) (Variance n f))      -- (k+1)·Var
//!                 (Rat.add (Rat.mul (natCast n) (Influence n f i))     -- ≤ 2n·Inf_i
//!                          (Rat.mul (natCast n) (Influence n f i))))
//! ```
//!
//! where `P := (k+1)·9^k`, `Q := P+1`, and the threshold `(k+1)·(P+1)² ≤ 2n`
//! (over `Rat`) is the genuine KKL threshold `(k+1)·((k+1)·9^k + 1)² ≤ 2n`
//! (non-vacuous, holds for `k` up to `~log₈₁ n`). The `Q := P+1` choice (rather
//! than `2P`) makes `1 < Q` follow from `0 < P` alone, avoiding any `1 ≤ 9^k`
//! exponent-monotonicity machinery. The `0 < n` premise is carried explicitly
//! (KKL is about `n ≥ 1` variables). The conclusion is the GENUINE KKL
//! max-influence lower bound `∃ i, Inf_i ≥ ((k+1)·Var)/(2n)` with NO
//! small-influence side condition.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! `δ := Rat.inv Q`, `τ := δ·δ`. Positivity scaffolding: `0<P`, `0<Q`, `P≤Q`,
//! `0≤δ`, `1<Q` (from `0<P` via `add_lt_add_right`), `δ<1`, hence `τ = δ·δ < 1`.
//! `Classical.em (∃ i, τ ≤ Inf_i)`:
//!
//! - **Case A** (`∃ i, τ ≤ Inf_i`): `(k+1)·Var ≤ (k+1) ≤ 2n·τ ≤ 2n·Inf_i`. The
//!   middle `(k+1) ≤ (Nn+Nn)·τ` is the threshold `(k+1)·QQ ≤ Nn+Nn` cancelled by
//!   `QQ·τ = 1` (`Rat.le_of_mul_le_mul_left_pos`, with `δ·δ = inv(Q·Q)` via
//!   `Rat.mul_inv`). `Var ≤ 1` is [`variance_le_one`].
//! - **Case B** (`∀ i, Inf_i ≤ τ`, derived from `hne` + `Rat.le_total`): feed
//!   [`kkl_exists_max_influence`] with `δ`; `hkt` holds because
//!   `(k+1)·(9^k·(δ·I)) = (P·δ)·I ≤ 1·I = I` (`P·δ ≤ Q·δ = Q·inv Q = 1`).
//!
//! `Classical.em`'s closure is foundational, so the result stays `Constructive`
//! with empty domain-axiom closure. No axiom added/removed. Idempotent. Gated
//! behind `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms. `natCast`/`pow9`/`Influence`/`Variance` spellings BYTE-MATCH
/// `MaxInfConsts` (the conditional theorem) so its instance applies directly.
struct UncondConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_of_nat: Expr,
    rat_mul: Expr,
    rat_add: Expr,
    rat_inv: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    pow_nat: Expr,
    fin: Expr,
    bool_fn: Expr,
    influence: Expr,
    variance: Expr,
    total_influence: Expr,
    u1: Level,
}

impl UncondConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_of_nat: k("Rat.ofNat"),
            rat_mul: k("Rat.mul"),
            rat_add: k("Rat.add"),
            rat_inv: k("Rat.inv"),
            rat_one: k("Rat.one"),
            rat_zero: k("Rat.zero"),
            pow_nat: k("Rat.powNat"),
            fin: k("Fin"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            influence: k("BoolAnalysis.Influence"),
            variance: k("BoolAnalysis.Variance"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
            u1: Level::succ(Level::zero()),
        }
    }

    fn succ(&self, n: &Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n.clone())
    }
    fn nat_lit(&self, v: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..v {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.le"), vec![]), [a, b])
    }
    fn rat_lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [a, b])
    }
    /// `natCast m := Rat.mk (Int.ofNat m) 1` — BYTE-MATCHES MaxInfConsts.
    fn natcast(&self, m: &Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), m.clone()),
                self.succ(&self.nat_zero.clone()),
            ],
        )
    }
    /// `9^k := powNat (Rat.ofNat 9) k` — BYTE-MATCHES MaxInfConsts::pow9.
    fn pow9(&self, k: &Expr) -> Expr {
        Expr::apps(
            self.pow_nat.clone(),
            [
                Expr::app(self.rat_of_nat.clone(), self.nat_lit(9)),
                k.clone(),
            ],
        )
    }
    /// `9 := Rat.ofNat 9` — the `powNat` base (BYTE-MATCHES MaxInfConsts::pow9).
    fn nine(&self) -> Expr {
        Expr::app(self.rat_of_nat.clone(), self.nat_lit(9))
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    /// `Nat.lt 0 n ≡ Nat.le (succ 0) n` — BYTE-MATCHES MaxInfConsts::pos_nat.
    fn pos_nat(&self, n: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.le"), vec![]),
            [self.succ(&self.nat_zero.clone()), n.clone()],
        )
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    fn variance_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.variance.clone(), [n.clone(), f.clone()])
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    /// `P := natCast(k+1)·9^k`.
    fn p_of(&self, k: &Expr) -> Expr {
        self.mul(self.natcast(&self.succ(k)), self.pow9(k))
    }
    /// `Q := P + 1`. Using `P+1` (rather than `2P`) makes `1 < Q` follow from
    /// `0 < P` alone — no `1 ≤ 9^k` exponent-monotonicity machinery needed.
    fn q_of(&self, k: &Expr) -> Expr {
        self.add(self.p_of(k), self.rat_one.clone())
    }

    // ── Eq.{1} plumbing over Rat ──────────────────────────────────────────────
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b],
        )
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.u1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h],
        )
    }
    /// `0 < Rat.ofNat 9` := `@Int.NonNeg.mk 8` — `Rat.lt 0 (ofNat 9)`
    /// def-reduces to the `Int.NonNeg` rep the constructor inhabits (same idiom
    /// as the conditional builder's `four_pos`).
    fn zero_lt_nine(&self) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]),
            self.nat_lit(8),
        )
    }
}

include!("boolean_analysis_kkl_maxinf_uncond_build.rs");

impl Environment {
    /// Register `BoolAnalysis.kkl_exists_max_influence_uncond` — the
    /// UNCONDITIONAL large-influence dichotomy. See module docs. Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent; no axiom
    /// added/removed.
    pub fn register_kkl_exists_max_influence_uncond(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_exists_max_influence_uncond");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.init_rat_field_inst()?; // left/right_distrib, mul_assoc, mul_comm, one_mul, mul_inv_cancel
        self.init_classical()?; // Classical.em, Or, Or.rec, False.elim
        self.init_exists()?;
        self.init_algebra_rat_inv_dyadic()?; // inv_pos, ne_zero_of_pos, inv_lt_of_one_lt_mul, mul_inv_cancel
        self.init_algebra_rat_inv_mul()?; // Rat.mul_inv
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_left/right, sq_nonneg
        self.init_boolean_analysis_order_toolkit_b1c()?; // lt_of_le_of_lt, lt_of_lt_of_le
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.register_rat_order_proofs()?; // Rat.zero_lt_one, Rat.le_refl, Rat.le_total
        self.register_rat_add_le_add()?; // Rat.add_le_add
        self.register_rat_add_lt_add_right()?; // Rat.add_lt_add_right (+ lt_trans spine)
        self.register_rat_le_of_mul_le_mul_left_pos()?; // Rat.le_of_mul_le_mul_left_pos
        self.register_rat_pow_nat_mul_base()?; // Rat.powNat_mul_base, Rat.powNat_pos
        self.register_nat_cast_le_of_ble()?; // Nat.cast_le_of_ble
        self.register_variance_le_one()?; // BoolAnalysis.variance_le_one
        self.register_total_influence_nonneg()?; // 0 ≤ I
        self.register_natcast_nonneg()?; // BoolAnalysis.natCast_nonneg
        self.register_kkl_exists_max_influence()?; // the conditional theorem
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = UncondConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_uncond(&c, false),
            value: build_uncond(&c, true),
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
    fn test_kkl_exists_max_influence_uncond_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_kkl_exists_max_influence_uncond()
            .expect("register_kkl_exists_max_influence_uncond");
        let nm = Name::from_string("BoolAnalysis.kkl_exists_max_influence_uncond");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("uncond proof must check: {e:?}"));
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
    fn test_uncond_idempotent() {
        let mut env = Environment::with_prelude();
        env.register_kkl_exists_max_influence_uncond()
            .expect("first");
        env.register_kkl_exists_max_influence_uncond()
            .expect("idempotent");
    }
}
