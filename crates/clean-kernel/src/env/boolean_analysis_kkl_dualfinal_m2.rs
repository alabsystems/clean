// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual `(4/3→2)` bound — Stage C-3, the M2-close COMPOSITION over a
//! materialised sequence `z : HCPoint n → Rat`.
//!
//! # What this lands
//!
//! `BoolAnalysis.m2_from_contraction`
//! (`boolean_analysis_kkl_dualres_m2.rs`) is the abstract M2 reduction over
//! `f4 s2 count : Rat`, taking H1 (`f4 ≤ s2`) and H2 (`s2 ≤ 16·count²`) as
//! hypotheses. With H1 now LANDED axiom-free at the `Fin.sum` level
//! (`BoolAnalysis.fin_sum_sq_le_sq_sum_nonneg`,
//! `boolean_analysis_kkl_dualfinal_h1.rs`), this module DISCHARGES H1 for the
//! CONCRETE per-cube-point `f4`/`s2` of a materialised sequence `z`, leaving
//! the squared spatial 2-norm contraction as the SOLE residual hypothesis:
//!
//! ```text
//! BoolAnalysis.dual_m2_for_seq :
//!   ∀ (n : Nat) (z : HCPoint n → Rat) (count : Rat),
//!     Rat.le Rat.zero count →                           -- 0 ≤ count
//!     Rat.le Rat.one  count →                           -- 1 ≤ count
//!     Rat.le (Rat.mul (subsetSum n (fun x => z x · z x))   -- (H2) (Σ z²)² ≤ 16·count²
//!                     (subsetSum n (fun x => z x · z x)))
//!            (Rat.mul (Rat.mul 16 count) count) →
//!     Rat.le (subsetSum n (fun x => (z x · z x) · (z x · z x)))  -- ⟹ Σ z⁴ ≤ 16·count³
//!            (Rat.mul (Rat.mul 16 count) (Rat.mul count count))
//! ```
//!
//! i.e. for the noise-operator value `z := T_{1/9} g` (once materialised — see
//! the residual note), `f4 = Σ pow4(z) ≤ 16·count³` follows from the SQUARED
//! 2-norm contraction `(Σ z²)² ≤ 16·count²` ALONE. The `16` and the cube
//! `(16·count)·(count·count)` are byte-for-byte the `m2_from_contraction` /
//! `two_norm_sq_le_of_holder_chain` shapes, so this output is def-eq to the
//! `h_m2` the assembly consumes.
//!
//! # Proof (constructive, empty admitted-axiom closure)
//!
//! Instantiate `m2_from_contraction` at
//! `f4 := subsetSum n (fun x => (z x·z x)·(z x·z x))` (= `Σ z⁴`),
//! `s2 := (subsetSum n (z²))·(subsetSum n (z²))` (= `(Σ z²)²`), `count`, with:
//! - `H1 : f4 ≤ s2` — `BoolAnalysis.fin_sum_sq_le_sq_sum_nonneg` instantiated at
//!   `m := Nat.pow 2 n`, `g := fun j => z (hcDecode n j)·z (hcDecode n j)` and
//!   `(fun j => Rat.sq_nonneg (z (hcDecode n j)))`. Because `subsetSum n G ≡
//!   Fin.sum (2^n) (fun j => G (hcDecode n j))` (reducible δ) and
//!   `pow4(z x) ≡ (z x·z x)·(z x·z x) = (z² x)·(z² x)`, the H1 instance's
//!   `Σ_j (g j·g j) ≤ (Σ_j g j)²` is def-eq to `f4 ≤ s2`.
//! - `H2` = the supplied squared-contraction hypothesis.
//!
//! Every leaf (`m2_from_contraction`, `fin_sum_sq_le_sq_sum_nonneg`,
//! `Rat.sq_nonneg`) is `Constructive` with empty admitted-axiom closure, so this
//! composition is too.
//!
//! # Residual (reported, NOT admitted)
//!
//! The CONCRETE consumer instance `z := T_{1/9}(D_i f)` is blocked on the
//! applied-operator MATERIALISATION `applyT (1/9) g : HCPoint n → Rat :=
//! fun x => Σ_y g(y)·noiseDensityW (1/9) n x y`, which does NOT exist axiom-free
//! (design §10.8). With `applyT` and the spatial 2-norm contraction
//! (`Σ sq(applyT(1/9)g) ≤ Σ sq(g) = 4·count`, squared) + the B3a Fubini, this
//! lemma's H2 is dischargeable and `m2_from_contraction` closes the squared dual
//! bound. This module pins M2 to EXACTLY that squared spatial contraction over a
//! materialised `z` — a kernel-checked object, NOT prose.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Cached atoms for the M2-close composition.
struct M2SeqConsts {
    o: OrderConsts,
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    hcpoint: Expr,
    hc_decode: Expr,
    subset_sum: Expr,
    sq_nonneg: Expr,
    m2_from_contraction: Expr,
    h1_lemma: Expr,
}

impl M2SeqConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            o: OrderConsts::new(),
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            hc_decode: k("BoolAnalysis.hcDecode"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            sq_nonneg: k("Rat.sq_nonneg"),
            m2_from_contraction: k("BoolAnalysis.m2_from_contraction"),
            h1_lemma: k("BoolAnalysis.fin_sum_sq_le_sq_sum_nonneg"),
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
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat())
    }
    /// `Nat.pow 2 n`.
    fn pow2(&self, n: &Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let two = Expr::app(self.nat_succ.clone(), one);
        Expr::apps(self.nat_pow.clone(), [two, n.clone()])
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), n.clone())
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn hc_decode(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.hc_decode.clone(), [n.clone(), j.clone()])
    }
    /// `16 : Rat` as `Rat.mk (Int.ofNat 16) 1` — byte-for-byte
    /// `M2Consts::lit16` / `AssembleConsts::lit16`.
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
    /// `fun (x : HCPoint n) => z x · z x` (the `z²` summand).
    fn sq_z_fn(&self, parent: &EnvDeclBuilder, n: &Expr, z: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let zx = Expr::app(z.clone(), x.clone());
        let body = self.mul(zx.clone(), zx);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (x : HCPoint n) => (z x · z x) · (z x · z x)` (the `pow4 z` summand).
    fn pow4_z_fn(&self, parent: &EnvDeclBuilder, n: &Expr, z: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let zx = Expr::app(z.clone(), x.clone());
        let zz = self.mul(zx.clone(), zx);
        let body = self.mul(zz.clone(), zz);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (j : Fin (2^n)) => z (hcDecode n j) · z (hcDecode n j)` — the
    /// `Fin.sum`-side `g` for instantiating H1 (its summand `g j·g j` is def-eq
    /// to `pow4 z` at `hcDecode n j`, and `Fin.sum (2^n) g ≡ subsetSum n (z²)`).
    fn sq_z_decoded_fn(&self, parent: &EnvDeclBuilder, n: &Expr, z: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_p = self.fin_of(&self.pow2(n));
        let (j_id, j) = d.fresh_local(fin_p.clone());
        let zx = Expr::app(z.clone(), self.hc_decode(n, &j));
        let body = self.mul(zx.clone(), zx);
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_p, body))
    }
    /// `fun (j : Fin (2^n)) => Rat.sq_nonneg (z (hcDecode n j))` — the per-term
    /// nonneg witness `0 ≤ z(…)·z(…)` H1 demands.
    fn sq_nonneg_decoded_fn(&self, parent: &EnvDeclBuilder, n: &Expr, z: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_p = self.fin_of(&self.pow2(n));
        let (j_id, j) = d.fresh_local(fin_p.clone());
        let body = Expr::app(
            self.sq_nonneg.clone(),
            Expr::app(z.clone(), self.hc_decode(n, &j)),
        );
        d.finish_child(d.mk_lam(j_id, BinderInfo::Default, fin_p, body))
    }
}

fn build_dual_m2_for_seq(c: &M2SeqConsts) -> (Expr, Expr) {
    // `16·count²` and `16·count³` (byte-for-byte m2_from_contraction).
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
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let zt = c.hcpoint_to_rat(&n);
        let (z_id, z) = b.fresh_local(zt.clone());
        let (cnt_id, cnt) = b.fresh_local(c.rat());

        let s2 = c.ssum(&n, c.sq_z_fn(&b, &n, &z)); // Σ z²
        let f4 = c.ssum(&n, c.pow4_z_fn(&b, &n, &z)); // Σ z⁴
        let s2_sq = c.mul(s2.clone(), s2); // (Σ z²)²

        let h0_ty = c.le(c.zero(), cnt.clone());
        let h1c_ty = c.le(c.one(), cnt.clone());
        let h2_ty = c.le(s2_sq, m2_of(&cnt)); // (Σ z²)² ≤ 16·count²
        let concl = c.le(f4, cube_of(&cnt)); // Σ z⁴ ≤ 16·count³

        let (h2_id, _) = b.fresh_local(h2_ty.clone());
        let e = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
        let (h1c_id, _) = b.fresh_local(h1c_ty.clone());
        let e = b.mk_pi(h1c_id, BinderInfo::Default, h1c_ty, e);
        let (h0_id, _) = b.fresh_local(h0_ty.clone());
        let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
        let e = b.mk_pi(cnt_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_pi(z_id, BinderInfo::Default, zt, e);
        b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(c.nat.clone());
        let zt = c.hcpoint_to_rat(&n);
        let (z_id, z) = b.fresh_local(zt.clone());
        let (cnt_id, cnt) = b.fresh_local(c.rat());

        let s2 = c.ssum(&n, c.sq_z_fn(&b, &n, &z)); // Σ z²
        let f4 = c.ssum(&n, c.pow4_z_fn(&b, &n, &z)); // Σ z⁴
        let s2_sq = c.mul(s2.clone(), s2.clone()); // (Σ z²)²

        let h0_ty = c.le(c.zero(), cnt.clone());
        let h1c_ty = c.le(c.one(), cnt.clone());
        let h2_ty = c.le(s2_sq.clone(), m2_of(&cnt));

        let (h0_id, h0) = b.fresh_local(h0_ty.clone());
        let (h1c_id, h1c) = b.fresh_local(h1c_ty.clone());
        let (h2_id, h2) = b.fresh_local(h2_ty.clone());

        // H1 instance : Fin.sum (2^n) (g·g) ≤ (Fin.sum (2^n) g)²
        //   where g := fun j => z(hcDecode n j)·z(hcDecode n j) — def-eq to f4 ≤ s2².
        let g_dec = c.sq_z_decoded_fn(&b, &n, &z);
        let sq_nn = c.sq_nonneg_decoded_fn(&b, &n, &z);
        let h1 = Expr::apps(c.h1_lemma.clone(), [c.pow2(&n), g_dec, sq_nn]);

        // m2_from_contraction f4 s2² count h0 h1c h1 h2 : f4 ≤ 16·count³.
        let proof = Expr::apps(
            c.m2_from_contraction.clone(),
            [f4, s2_sq, cnt.clone(), h0, h1c, h1, h2],
        );

        let e = b.mk_lam(h2_id, BinderInfo::Default, h2_ty, proof);
        let e = b.mk_lam(h1c_id, BinderInfo::Default, h1c_ty, e);
        let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
        let e = b.mk_lam(cnt_id, BinderInfo::Default, c.rat(), e);
        let e = b.mk_lam(z_id, BinderInfo::Default, zt, e);
        b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
    };

    (ty, value)
}

impl Environment {
    /// Register `BoolAnalysis.dual_m2_for_seq` — the M2-close composition over a
    /// materialised `z : HCPoint n → Rat`: `Σ z⁴ ≤ 16·count³` from the squared
    /// spatial 2-norm contraction `(Σ z²)² ≤ 16·count²` (under `0 ≤ count`,
    /// `1 ≤ count`), discharging H1 via the landed
    /// `BoolAnalysis.fin_sum_sq_le_sq_sum_nonneg`. Kernel-checked,
    /// `ProofQuality::Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_dual_m2_for_seq(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dual_m2_for_seq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_m2_from_contraction()?; // the abstract M2 reduction
        self.register_fin_sum_sq_le_sq_sum_nonneg()?; // H1 (+ subsetSum/hcDecode via init)
        self.init_boolean_analysis()?; // HCPoint, hcDecode, subsetSum, sq_nonneg surface
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = M2SeqConsts::new();
        let (ty, value) = build_dual_m2_for_seq(&c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// Init hook for the M2-close dual-final overlay module.
    pub fn init_boolean_analysis_kkl_dualfinal_m2(&mut self) -> Result<(), EnvError> {
        self.register_dual_m2_for_seq()
    }
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
        env.init_boolean_analysis_kkl_dualfinal_m2()
            .expect("init_boolean_analysis_kkl_dualfinal_m2");
        env.init_boolean_analysis_kkl_dualfinal_m2()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_dual_m2_for_seq_constructive() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.dual_m2_for_seq");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("theorem value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("dual_m2_for_seq proof must check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "closure must be foundational-only, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    /// THE TARGET-REFUTATION GATE. The composition is a TRUE implication: from
    /// `(Σz²)² ≤ 16·count²`, `1 ≤ count` (so `count ≤ count²` ⟹
    /// `16·count² ≤ 16·count³`) and `Σz⁴ ≤ (Σz²)²` (H1, always true for the
    /// nonneg `z²` terms), `Σz⁴ ≤ 16·count³` for EVERY assignment. No carrier
    /// instance can break it; `refute_conjecture` must NOT manufacture one.
    #[test]
    fn test_dual_m2_for_seq_not_refuted() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.dual_m2_for_seq"))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "dual_m2_for_seq is a TRUE implication; must NOT refute"
        );
    }
}
