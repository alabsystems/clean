// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut junta-theorem roadmap — RETIREMENT ASSEMBLY (the MASS side) +
//! HONEST blocker pin for the SIZE side.
//!
//! ## Status (2026-06-21) — RETIRED. TCB 5→3, the 3-axiom floor.
//!
//! `BoolAnalysis.friedgut_boolean` is **a genuine, kernel-checked, empty-closure
//! `Declaration::Theorem`**, and `friedgut_boolean_helper` is a reducible
//! `Declaration::Definition` carrying the faithful v3 body
//! (`friedgut_l2_faithful_body_v3`, `fourier_boolean_theorems.rs`; budget
//! `friedgut_budget_v3 e := 48·2^e`, two-sided guard `2^e·eps ≤ K ≤ 2^(e+1)·eps`).
//! Both domain axioms are removed from the TCB; the trusted base is now exactly
//! `{propext, Quot.sound, Classical.choice}` (`data/soundness_tcb.json`
//! `axiom_count: 3`; `golden_matches_live_axioms` + C1–C5 SOUND;
//! `every_constructive_claim_has_empty_transitive_axiom_closure` confirms the
//! proof's transitive closure is `⊆` the 3 foundational).
//!
//! ## How it was retired (the corrected budget + the 3-case proof)
//!
//! The earlier `friedgut_l2_faithful_body` v1 (`∀ e` + affine `BUDGET = 2·e`) was
//! **concretely FALSE** at `n=2` parity (every `1`-junta leaves mass `1.0 > 1/2`),
//! and the v2 fix (`15·2^e`) was **false at large `n`** (budget `2^(7.5·K/eps)` is
//! below the standard threshold junta `2^(12.68·K/eps)` — the `τ=dr²` square was
//! dropped). The v3 body fixes both: a two-sided dyadic guard pins
//! `e ≈ ⌊log₂(K/eps)⌋`, and the **exponential** budget `48·2^e` provably dominates
//! the true junta need `8·log₂(9)·2^e = 25.36·2^e` with a +17.6-bit margin at every
//! admissible `e` (adversarially re-derived by a 6-skeptic audit workflow). The
//! `friedgut_boolean` proof (`friedgut_boolean_proof`, `boolean_analysis_friedgut_wiring.rs`)
//! is a 3-case `Bool.casesOn` assembly of four landed empty-closure case-lemmas:
//! `friedgut_boolean_case_le` (`n ≤ B`, J=full), `friedgut_boolean_case_empty`
//! (J=∅, for `eps ≥ 1` via `variance_le_one` and `eps ≤ 0` via `variance_le_influence`),
//! and `friedgut_boolean_case_threshold` (`0 < eps < 1`, the genuine Friedgut
//! threshold junta via `friedgut_l2_core` + the SIZE poly bound). NOT a faked /
//! n-dependent / vacuous / Theorem-wrapping-Axiom retirement — the count dropped
//! only because the proof is real.
//!
//! ## What this module DOES bank (sound, axiom-free MASS-side progress)
//!
//! `BoolAnalysis.friedgut_high_mass_budget` — the genuine HIGH-band budget
//! division that `friedgut_l2_core` consumes but does not itself provide:
//!
//! ```text
//! BoolAnalysis.friedgut_high_mass_budget :
//!   ∀ (n d : Nat) (f : BoolFn n) (eH : Rat),
//!     Nat.le (Nat.pow 2 (d+1)) n →                              -- (inherited) dyadic premise
//!     Rat.lt Rat.zero (natCast (d+1)) →                         -- 0 < d+1 (concrete at call sites)
//!     Rat.le (TotalInfluence n f) (Rat.mul (natCast (d+1)) eH) → -- I[f] ≤ (d+1)·eH
//!       Rat.le
//!         (subsetSum n (fun S =>
//!            ind (Nat.ble (d+1) (setSizeNat n S))
//!              · (FourierCoefficient n f S · FourierCoefficient n f S)))   -- M_{≥d+1}
//!         eH                                                    -- ≤ eH
//! ```
//!
//! i.e. from the level-Markov inequality `(d+1)·M_{≥d+1} ≤ I[f]`
//! (`high_degree_mass_le`) and `I[f] ≤ (d+1)·eH`, cancel the positive factor
//! `(d+1)` (`Rat.le_of_mul_le_mul_left_pos`) to get `M_{≥d+1} ≤ eH` — exactly the
//! HIGH-budget hypothesis `hhigh` of `friedgut_l2_core`. The integrand
//! `fun S => ind(ble (d+1) |S|)·(f̂·f̂)` is BYTE-IDENTICAL to `friedgut_l2_core`'s
//! `M_{≥d+1}` (`highmass_fn`) and to `high_degree_mass_le`'s masked mass.
//!
//! Pure `Rat`-order chaining: `(d+1)·M ≤ I ≤ (d+1)·eH` ⟹ `(d+1)·M ≤ (d+1)·eH`
//! (`Rat.le_trans`) ⟹ `M ≤ eH` (`le_of_mul_le_mul_left_pos`). Every dependency
//! (`high_degree_mass_le`, `Rat.le_trans`, `Rat.le_of_mul_le_mul_left_pos`) is a
//! landed `Constructive` empty-closure Theorem, so this is too. NO axiom is added
//! or removed. NO `sorry` / `add_decl_unchecked` / `add_decl_structural` /
//! `native_decide` / `unsafe` / `Real`. Idempotent. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms — carrier spellings byte-match `high_degree_mass_le`'s masked
/// mass and `friedgut_l2_core`'s `highmass_fn`.
struct RetireConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_ble: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    rat_zero: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fourier: Expr,
    subset_sum: Expr,
    ind: Expr,
    set_size_nat: Expr,
    total_influence: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
}

impl RetireConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_ble: k("Nat.ble"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            rat_zero: k("Rat.zero"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            ind: k("BoolAnalysis.ind"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: k("instLERat"),
        }
    }

    fn nat_one(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn nat_lit(&self, v: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..v {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    /// `natCast m := Rat.mk (Int.ofNat m) 1` (byte-match high_degree's `natcast`).
    fn natcast(&self, m: &Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), m.clone()),
                self.nat_one(),
            ],
        )
    }
    /// `Nat.pow 2 e`.
    fn pow2(&self, e: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.pow"), vec![]),
            [self.nat_lit(2), e.clone()],
        )
    }
    fn nat_le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Nat.le"), vec![]), [a, b])
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [a, b])
    }
    fn trans_le(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            [a, b, cc, h1, h2],
        )
    }

    /// `fun S => ind(ble (d+1) |S|)·(f̂·f̂)` — BYTE-IDENTICAL to high_degree's
    /// `mask_fn` at `knat := d+1` and to `friedgut_l2_core`'s `highmass_fn`.
    fn highmass_fn(&self, parent: &EnvDeclBuilder, n: &Expr, d: &Expr, f: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = b.fresh_local(hcp.clone());
        let knat = self.succ(d.clone());
        let p = self.ind_of(self.ble(knat, self.set_size_nat_of(n, &s)));
        let coeff = self.fourier_of(n, f, &s);
        let body = self.mul(p, self.mul(coeff.clone(), coeff));
        b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

/// Build the `friedgut_high_mass_budget` type (`for_value=false`) / value.
fn high_budget_build(c: &RetireConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let (eh_id, eh) = b.fresh_local(c.rat.clone());

    let knat = c.succ(d.clone()); // d+1
    let kcast = c.natcast(&knat); // natCast (d+1)
    let mass = c.ssum(&n, c.highmass_fn(&b, &n, &d, &f)); // M_{≥d+1}
    let infl = c.total_influence_of(&n, &f); // I[f]
    let k_mass = c.mul(kcast.clone(), mass.clone()); // (d+1)·M
    let k_eh = c.mul(kcast.clone(), eh.clone()); // (d+1)·eH

    // hypotheses.
    let hk_ty = c.nat_le(c.pow2(&knat), n.clone()); // 2^(d+1) ≤ n
    let hpos_ty = c.lt(c.rat_zero.clone(), kcast.clone()); // 0 < natCast(d+1)
    let hi_ty = c.le(infl.clone(), k_eh.clone()); // I[f] ≤ (d+1)·eH
    let concl = c.le(mass.clone(), eh.clone()); // M ≤ eH

    if !for_value {
        let (hk_id, _) = b.fresh_local(hk_ty.clone());
        let (hpos_id, _) = b.fresh_local(hpos_ty.clone());
        let (hi_id, _) = b.fresh_local(hi_ty.clone());
        let e = b.mk_pi(hi_id, BinderInfo::Default, hi_ty, concl);
        let e = b.mk_pi(hpos_id, BinderInfo::Default, hpos_ty, e);
        let e = b.mk_pi(hk_id, BinderInfo::Default, hk_ty, e);
        let e = b.mk_pi(eh_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
        let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
        return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
    }

    // ── value ──
    let (hk_id, hk) = b.fresh_local(hk_ty.clone());
    let (hpos_id, hpos) = b.fresh_local(hpos_ty.clone());
    let (hi_id, hi) = b.fresh_local(hi_ty.clone());

    // hmark : (d+1)·M ≤ I[f]   := high_degree_mass_le n d f hk.
    let hmark = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.high_degree_mass_le"),
            vec![],
        ),
        [n.clone(), d.clone(), f.clone(), hk.clone()],
    );
    // chain : (d+1)·M ≤ (d+1)·eH   := le_trans (k_mass) (I) (k_eh) hmark hi.
    let chain = c.trans_le(k_mass.clone(), infl.clone(), k_eh.clone(), hmark, hi);
    // cancel : M ≤ eH  := le_of_mul_le_mul_left_pos M eH (d+1) hpos chain.
    //   (∀ a b c, 0 < c → c·a ≤ c·b → a ≤ b ; here c := natCast(d+1).)
    let cancel = Expr::apps(
        Expr::const_(Name::from_string("Rat.le_of_mul_le_mul_left_pos"), vec![]),
        [mass.clone(), eh.clone(), kcast.clone(), hpos, chain],
    );

    let e = b.mk_lam(hi_id, BinderInfo::Default, hi_ty, cancel);
    let e = b.mk_lam(hpos_id, BinderInfo::Default, hpos_ty, e);
    let e = b.mk_lam(hk_id, BinderInfo::Default, hk_ty, e);
    let e = b.mk_lam(eh_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// `BoolAnalysis.friedgut_high_mass_budget` — the HIGH-band budget division
    /// `(d+1)·M_{≥d+1} ≤ I[f] ≤ (d+1)·eH ⟹ M_{≥d+1} ≤ eH`. The genuine
    /// HIGH-budget transport that `friedgut_l2_core`'s `hhigh` hypothesis
    /// requires. Kernel-checked, `Constructive`, empty admitted-axiom closure.
    /// Idempotent. No axiom added or removed.
    ///
    /// See the module docs for why the FULL `friedgut_boolean` retirement is
    /// blocked (the frozen affine `BUDGET = 2e` would require a polynomial-junta
    /// Friedgut, which is false / not provable from the landed bricks).
    pub fn register_friedgut_high_mass_budget(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_high_mass_budget");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_boolean_analysis_order_toolkit()?;
        self.init_rat_field_inst()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // The level-Markov HIGH-mass brick + the Rat order plumbing.
        self.register_high_degree_mass_le()?;
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.register_rat_le_of_mul_le_mul_left_pos()?; // Rat.le_of_mul_le_mul_left_pos
        self.register_set_size_nat()?;
        self.register_subset_sum()?;

        let c = RetireConsts::new();
        let ty = high_budget_build(&c, false);
        let value = high_budget_build(&c, true);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn check_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
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
                .map(|dp| dp.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_friedgut_high_mass_budget_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_high_mass_budget()
            .expect("register_friedgut_high_mass_budget");
        env.register_friedgut_high_mass_budget()
            .expect("idempotent");
        check_constructive(&env, "BoolAnalysis.friedgut_high_mass_budget");
    }

    /// GENUINE-RETIREMENT pin (TCB 5→3): `friedgut_boolean_helper` is now a reducible
    /// `Declaration::Definition` (the CORRECTED-budget v3 body `48·2^e`,
    /// `friedgut_l2_faithful_body_v3`), and `friedgut_boolean` is a genuine
    /// `Declaration::Theorem`, `Constructive`, with an EMPTY admitted-axiom closure
    /// (⊆ FOUNDATIONAL_AXIOMS). Both domain axioms are RETIRED.
    ///
    /// ## Why this is a GENUINE retirement (not the reverted v1/v2 masquerades)
    ///
    /// The earlier v1/v2 concrete bodies were UNFAITHFUL and reverted:
    /// * v1 (`friedgut_l2_faithful_body`): FALSE at `n=2` parity (`∀ e` forces a
    ///   1-junta at `e=0`); caught by the small-n refutation gate.
    /// * v2 (`…_v2`, budget `15·2^e`): FALSE at LARGE `n` — `2^(7.5·K/eps)` is BELOW
    ///   Friedgut's standard junta `2^(12.68·K/eps)` (the v2 derivation dropped the
    ///   `τ=dr²` square: `9^d` vs `9^(2d)`); the small-n gate is BLIND to this.
    ///
    /// The v3 body fixes the constant: budget `48·2^e` with `c = 48 ≥ 2·12.68 ≈ 25.4`
    /// DOMINATES `K/dr²`, so the body is TRUE — and now PROVED. `friedgut_boolean`'s
    /// value is `friedgut_boolean_proof` (the wiring lemma in
    /// `boolean_analysis_friedgut_wiring.rs`), a `Constructive`, empty-closure proof
    /// that 3-way `Bool.casesOn`-splits and discharges every branch with a landed
    /// case-lemma (`friedgut_boolean_case_le` / `_empty` / `_threshold`). It is NOT a
    /// Theorem-wrapping-Axiom: the proof term genuinely inhabits the (now reducible)
    /// v3 body. This test PINS the genuine retirement so a regression (re-installing
    /// an opaque axiom, or an unfaithful body) is diff-visible.
    #[test]
    fn test_friedgut_boolean_genuinely_retired() {
        use crate::env::ProofQuality;

        let env = Environment::soundness_certificate_env().expect("build cert env");

        // The HELPER is now a reducible Definition carrying the v3 body.
        let helper = env
            .get_const(&Name::from_string("BoolAnalysis.friedgut_boolean_helper"))
            .expect("friedgut_boolean_helper registered in cert env");
        assert_eq!(
            helper.kind,
            ConstantKind::Definition,
            "friedgut_boolean_helper must now be a reducible Definition carrying the \
             CORRECTED-budget v3 body (friedgut_l2_faithful_body_v3) — the genuine \
             retirement of the opaque axiom."
        );

        // `friedgut_boolean` is now a genuine Theorem, Constructive, empty closure.
        let nm = Name::from_string("BoolAnalysis.friedgut_boolean");
        let info = env
            .get_const(&nm)
            .expect("friedgut_boolean registered in cert env");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "friedgut_boolean must now be a genuine Theorem (its value is the \
             friedgut_boolean_proof wiring lemma — NOT a Theorem-wrapping-Axiom)."
        );
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "friedgut_boolean must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "friedgut_boolean closure must be EMPTY (⊆ FOUNDATIONAL_AXIOMS), got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }
}
