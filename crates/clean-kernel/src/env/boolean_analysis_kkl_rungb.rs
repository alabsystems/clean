// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL chain — RUNG B: the derivative → low-band spectral link.
//!
//! The KKL-finish needs, alongside the carrier-side rungs, the purely
//! spectral/rational inequality
//!
//! ```text
//! 4 · M_{1..k}[f]  ≤  Σ_i W^{≤k}[D_i f]
//! ```
//!
//! where (writing `c S := f̂(S)·f̂(S)`, `|S| := setSizeNat n S`, `four := 4`):
//!   * `M_{1..k}[f] := subsetSum n (fun S =>
//!         ind (and (ble 1 |S|) (not (ble (k+1) |S|))) · c S)`
//!     is the non-empty low-degree Fourier mass — the EXACT integrand
//!     `variance_low_band_influence` / RUNG A use (`m_lo_fn`).
//!   * `W^{≤k}[D_i f] := subsetSum n (fun S => ind (S i) · w_band S)`, with
//!     `w_band S := ind (not (ble (k+1) |S|)) · (four · c S)`, is the
//!     band-restricted per-derivative low-band mass. The factor `4` is the
//!     `{0,±2}`-derivative collapse `D̂_i f(S)² = 4·[i∈S]·f̂(S)²` (spectrally,
//!     this is the *definition* of the band-restricted derivative weight; on the
//!     spatial side the same `4` is `deriv_4norm_eq_4_influence`).
//!
//! ## What this rung proves (constructive, empty domain-axiom closure)
//!
//! ```text
//! BoolAnalysis.kkl_derivative_lowband_link :
//!   ∀ (n k : Nat) (f : BoolFn n),
//!     Rat.mul four (M_{1..k}[f])
//!       ≤ Fin.sum n (fun i => subsetSum n (fun S => ind (S i) · w_band S))
//! ```
//!
//! ### Proof (three pieces; all leaves empty-closure)
//!
//! 1. **Fubini / popcount collapse** — `subsetSum_double_count n w_band`
//!    (the K2a double-count) gives
//!    `Σ_i subsetSum n (fun S => ind (S i) · w_band S)
//!       = subsetSum n (fun S => setSize n S · w_band S)`.
//!    The LHS is byte-identical to the goal RHS, so this rewrites the goal RHS to
//!    the popcount-weighted band mass `subsetSum n (setSize · w_band)`.
//!
//! 2. **Scalar pull-out** — `subsetSum_smul n four m_lo_fn` gives
//!    `subsetSum n (fun S => four · m_lo_fn S) = four · M_{1..k}[f]`; symm turns
//!    the goal LHS `four · M_{1..k}` into `subsetSum n (fun S => four · m_lo_fn S)`.
//!
//! 3. **Pointwise band domination** — `subsetSum_le_of_pointwise` lifts the
//!    per-`S` inequality
//!    `four · (ind (and b1 b2) · c) ≤ setSize n S · (ind b2 · (four · c))`
//!    (the new `BoolAnalysis.lowband_term_le`, a `Bool.rec`/`Bool.rec` case-split
//!    on `b1 := ble 1 |S|`, `b2 := not (ble (k+1) |S|)`) from
//!    `subsetSum (four·m_lo_fn) ≤ subsetSum (setSize · w_band)`. The threshold
//!    side-condition `b1 = true → 1 ≤ setSize n S` is discharged via the landed
//!    Nat-bridge (`Nat.cast_le_of_ble` + `setSize_eq_natCast`): from
//!    `ble 1 |S| = true`, `Nat.cast_le_of_ble` yields `mk(ofNat 1) 1 ≤
//!    mk(ofNat |S|) 1`, and `setSize_eq_natCast` rewrites the RHS to `setSize`.
//!
//! Chaining (1)–(3) by `Eq.subst` over the goal endpoints closes
//! `four · M_{1..k} ≤ Σ_i W^{≤k}[D_i f]`.
//!
//! Every leaf (`subsetSum_double_count`, `subsetSum_smul`,
//! `subsetSum_le_of_pointwise`, `lowband_term_le`, `Nat.cast_le_of_ble`,
//! `setSize_eq_natCast`, the Rat-order toolkit, Eq/Bool.rec built-ins) is
//! `Constructive` with empty closure, so this rung is too. NO axiom is added or
//! removed — the soundness-certificate golden TCB is unchanged. This rung
//! RETIRES no axiom by itself; it is a CHAIN INPUT toward the KKL finish.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the RUNG-B construction. Spellings are byte-identical to the
/// on-branch `LowBandConsts` (`boolean_analysis_kkl_lowband.rs`) so `m_lo_fn` is
/// the SAME object as `variance_low_band_influence` / RUNG A, and to the K2b
/// `LE.le`/`instLERat` order surface so the monotonicity/threshold bricks attach.
struct RungBConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_true: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    rat_mul: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fin: Expr,
    ind: Expr,
    fourier: Expr,
    set_size: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    fin_sum: Expr,
    nat_ble: Expr,
    bool_and: Expr,
    bool_not: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    u0: Level,
    u1: Level,
}

impl RungBConsts {
    fn new() -> Self {
        let u0 = Level::zero();
        let u1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            bool_true: k("Bool.true"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            rat_mul: k("Rat.mul"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fin: k("Fin"),
            ind: k("BoolAnalysis.ind"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            set_size: k("BoolAnalysis.setSize"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            fin_sum: k("Fin.sum"),
            nat_ble: k("Nat.ble"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![u0.clone()]),
            inst_le_rat: k("instLERat"),
            u0,
            u1,
        }
    }

    // ── type helpers ───────────────────────────────────────────────────────
    fn rat(&self) -> Expr {
        self.rat.clone()
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    #[cfg(test)]
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    /// `f̂(S) · f̂(S)` — byte-identical to `LowBandConsts.fsq`.
    fn fsq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
    }
    fn set_size_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size.clone(), [n.clone(), s.clone()])
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fin_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), g])
    }
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn one_nat(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    /// `Nat.ble 1 m` — the `|S| ≥ 1` (non-empty) bit `b1`.
    fn ble1(&self, m: Expr) -> Expr {
        self.ble(self.one_nat(), m)
    }
    /// `Nat.ble (k+1) m` — the `|S| > k` bit.
    fn ble_succ_k(&self, k: &Expr, m: Expr) -> Expr {
        self.ble(self.succ(k.clone()), m)
    }
    fn band(&self, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.bool_and.clone(), [b, c])
    }
    fn bnot(&self, b: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), b)
    }
    /// `four := Rat.mk (Int.ofNat 4) 1` — the rational `4`.
    fn four(&self) -> Expr {
        let four_nat = self.succ(self.succ(self.succ(self.succ(self.nat_zero.clone()))));
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), four_nat), self.one_nat()],
        )
    }
    /// `natCast m := Rat.mk (Int.ofNat m) 1`.
    fn natcast(&self, m: Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), m), self.one_nat()],
        )
    }
    /// `@LE.le Rat instLERat a b` — the canonical `a ≤ b` (the K2b / Nat-bridge
    /// order surface; `instLERat` δ-projects to `Rat.le`).
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.rat.clone(), l, r],
        )
    }
    fn eq_bool(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.bool_.clone(), l, r],
        )
    }
    fn refl_rat(&self, a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.u1.clone()]),
            [self.rat.clone(), a],
        )
    }
    fn refl_bool(&self, a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.u1.clone()]),
            [self.bool_.clone(), a],
        )
    }
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h_a : motive b`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.u1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }

    // ── the band integrands ──────────────────────────────────────────────────

    /// `fun S => ind (and (ble 1 |S|) (not (ble (k+1) |S|))) · (f̂·f̂)` — the
    /// `M_{1..k}` band integrand, byte-identical to `LowBandConsts.m_lo_fn`.
    fn m_lo_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let ss = self.set_size_nat_of(n, &s);
        let band = self.band(self.ble1(ss.clone()), self.bnot(self.ble_succ_k(k, ss)));
        let body = self.mul(self.ind_of(band), self.fsq(n, f, &s));
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => four · m_lo_fn S` — the scalar-scaled low-band integrand
    /// (`subsetSum_smul`'s LHS shape at `cc := four`).
    fn four_m_lo_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let ss = self.set_size_nat_of(n, &s);
        let band = self.band(self.ble1(ss.clone()), self.bnot(self.ble_succ_k(k, ss)));
        let m_lo_s = self.mul(self.ind_of(band), self.fsq(n, f, &s));
        let body = self.mul(self.four(), m_lo_s);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `w_band S := ind (not (ble (k+1) |S|)) · (four · (f̂·f̂))` — the
    /// band-restricted, 4-scaled per-derivative weight (no `i`).
    fn w_band_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let ss = self.set_size_nat_of(n, &s);
        let b2 = self.bnot(self.ble_succ_k(k, ss));
        let body = self.mul(self.ind_of(b2), self.mul(self.four(), self.fsq(n, f, &s)));
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => ind (S i) · w_band S` — the per-coordinate `W^{≤k}[D_i f]`
    /// integrand (matches `subsetSum_double_count`'s `ind (S i) · w S` shape).
    fn coord_w_band_fn(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        k: &Expr,
        f: &Expr,
        i: &Expr,
    ) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let s_i = Expr::app(s.clone(), i.clone());
        let ss = self.set_size_nat_of(n, &s);
        let b2 = self.bnot(self.ble_succ_k(k, ss));
        let w_band_s = self.mul(self.ind_of(b2), self.mul(self.four(), self.fsq(n, f, &s)));
        let body = self.mul(self.ind_of(s_i), w_band_s);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => setSize n S · w_band S` — the popcount-weighted band integrand
    /// (`subsetSum_double_count`'s RHS at `w := w_band`).
    fn size_w_band_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let ss = self.set_size_nat_of(n, &s);
        let b2 = self.bnot(self.ble_succ_k(k, ss));
        let w_band_s = self.mul(self.ind_of(b2), self.mul(self.four(), self.fsq(n, f, &s)));
        let body = self.mul(self.set_size_of(n, &s), w_band_s);
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

include!("boolean_analysis_kkl_rungb_term.rs");
include!("boolean_analysis_kkl_rungb_link.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_rungb()
            .expect("init_boolean_analysis_kkl_rungb");
        env.init_boolean_analysis_kkl_rungb().expect("idempotent");
        env
    }

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "{name} must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_lowband_term_le_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.lowband_term_le");
    }

    #[test]
    fn test_kkl_derivative_lowband_link_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.kkl_derivative_lowband_link");
    }

    /// THE TARGET-REFUTATION GATE. `refute_conjecture` must NOT refute
    /// `kkl_derivative_lowband_link` over the dictator/parity/constant battery —
    /// it is a true, unconditional spectral inequality.
    #[test]
    fn test_kkl_derivative_lowband_link_not_refuted() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.kkl_derivative_lowband_link",
            ))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "the derivative→low-band link is a true inequality; it must NOT refute"
        );
    }
}
