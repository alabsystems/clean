// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut junta-theorem roadmap — the CHEAP, friedgut-specific rungs banked
//! as sound, axiom-free, kernel-checked bricks toward retiring the
//! `BoolAnalysis.friedgut_boolean(+_helper)` admitted axioms (TCB → 3 campaign).
//!
//! These rungs are INDEPENDENT of the shared hard crux (rung 5
//! `deriv_level_mass_lower`, a parallel agent owns the `kkl`/`deriv_level_mass`
//! surface). This module touches NONE of that surface — it only carries the
//! "zero new math" pieces of `designs/2026-06-13-friedgut-junta-theorem-roadmap.md`
//! (§"Ordered build (8 rungs)").
//!
//! # RUNG 1 — `BoolAnalysis.notSubsetMask` (carrier, reducible Definition)
//!
//! ```text
//! BoolAnalysis.notSubsetMask (n : Nat) (S J : HCPoint n) : Bool
//!   := Nat.ble 1 (setSizeNat n (fun (i : Fin n) => Bool.and (S i) (Bool.not (J i))))
//! ```
//!
//! The "`S` not ⊆ `J`" indicator: `notSubsetMask n S J = true` iff `S` has at
//! least one coordinate `i` with `S i = true` and `J i = false` — i.e. `S ⊄ J`.
//! The inner `setSizeNat n (fun i => S i ∧ ¬ J i)` is the popcount of the
//! coordinate-set `S \ J` (the `Bool.and (S i) (Bool.not (J i))` is the `S \ J`
//! indicator at `i`); `Nat.ble 1 _` is `1 ≤ |S \ J|`, the "non-empty difference"
//! test. This reuses the codebase's level-`≥ 1` idiom (the same `Nat.ble` /
//! `setSizeNat` spelling as the on-branch level-mass machinery). It is the
//! `notSubsetMask` carrier of the Friedgut helper's masked `subsetSum`
//! (roadmap §"Helper carriers"): `‖f − proj_J f‖₂² = Σ_{S⊄J} f̂(S)²`.
//!
//! Registered as a `Declaration::Definition`, `is_reducible: true`. Its body
//! bottoms out in reducible carriers (`Nat.ble`, `BoolAnalysis.setSizeNat`,
//! `Bool.and`, `Bool.not`), each of which is itself constructive with an empty
//! admitted-axiom closure, so `notSubsetMask` has an EMPTY admitted-axiom
//! closure and is `ProofQuality::Constructive`. NO `sorry` / `sorryAx` /
//! `trustedArith` / `add_decl_unchecked` / `add_decl_structural` /
//! `native_decide` / `unsafe` / `Rat.dist` / `Real`. Zero new math.
//!
//! See `crates/clean-kernel/src/env/boolean_analysis_kkl_natbridge.rs`
//! (`register_set_size_nat`) for the `setSizeNat` carrier this builds over, and
//! `boolean_analysis_chi_quad_diag.rs` / `boolean_analysis_high_degree_mass.rs`
//! for the mask-construction idiom.
//!
//! # RUNG 2 — `BoolAnalysis.influence_threshold_card_le` (the level-Markov bound)
//!
//! ```text
//! BoolAnalysis.influence_threshold_card_le :
//!   ∀ (n : Nat) (f : BoolFn n) (tau : Rat) (b : Fin n → Bool),
//!     (∀ i : Fin n, 0 ≤ Influence n f i) →                         -- influences ≥ 0
//!     (∀ i : Fin n, b i = Bool.true → tau ≤ Influence n f i) →     -- b is a tau-threshold mask
//!       Rat.mul tau (Fin.sum n (fun i => ind (b i)))               -- tau · |{i : b i}|
//!         ≤ TotalInfluence n f                                     -- ≤ I[f]
//! ```
//!
//! This is the **coordinate-wise Markov inequality** for the influence sum
//! (O'Donnell, *Analysis of Boolean Functions*, the standard
//! `tau·|{i : Inf_i ≥ tau}| ≤ I[f]` counting bound). The threshold mask `b` and
//! its correctness `b i = true → tau ≤ Inf_i` are supplied abstractly (the same
//! shape `subsetSum_threshold_le` consumes one level up); instantiating
//! `b i := (tau ≤ Inf_i)` recovers the literal `tau·|{i : Inf_i ≥ tau}| ≤ I[f]`.
//! `Fin.sum n (fun i => ind (b i))` is the `Rat`-valued cardinality
//! `|{i : b i = true}|` (sum of `{0,1}` indicators over `Fin n`, the `setSize`
//! idiom over coordinates). `TotalInfluence n f ≡ Fin.sum n (fun i => Inf_i)`
//! (reducible), so the RHS is the genuine total influence.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! 1. **Per-coordinate** `tau · ind(b i) ≤ Inf_i` by `Bool.casesOn` on `b i`
//!    (the `chi_quad_diag` eq-threaded `Bool.casesOn` idiom):
//!    - `b i = false`: `ind false ≡ Rat.zero`, so the LHS is `tau·0 ≡ 0`
//!      (`Rat.mul_zero`); discharged by `hnn i : 0 ≤ Inf_i`.
//!    - `b i = true`: `ind true ≡ Rat.one`, so the LHS is `tau·1 ≡ tau`
//!      (`Rat.mul_one`); discharged by `hb i (Eq.refl) : tau ≤ Inf_i`.
//! 2. **Sum the bound** with `Fin.sum_le n (fun i => tau·ind(b i))
//!    (fun i => Inf_i)`: `Σ_i tau·ind(b i) ≤ Σ_i Inf_i`.
//! 3. **Pull `tau` out** of the left sum with `Fin.sum_smul n tau (fun i =>
//!    ind(b i))`: `Σ_i tau·ind(b i) = tau · Σ_i ind(b i)`; rewrite the bound's
//!    LHS via `Eq.subst`.
//! 4. The right sum `Σ_i Inf_i` is `TotalInfluence n f` definitionally
//!    (`TotalInfluence` is the reducible `Fin.sum n (fun i => Influence n f i)`).
//!
//! Every dependency (`Bool.casesOn`, `BoolAnalysis.ind`, `Rat.mul_zero`,
//! `Rat.mul_one`, `Fin.sum_le`, `Fin.sum_smul`, `BoolAnalysis.Influence`,
//! `BoolAnalysis.TotalInfluence`, `Eq`/`Eq.subst`/`Eq.symm`/`Eq.refl`) is
//! itself `Constructive` with an empty admitted-axiom closure, so this rung is
//! `ProofQuality::Constructive` with an empty closure. It is INDEPENDENT of the
//! `kkl`/`deriv_level_mass` surface (no constant from that surface is used) —
//! the per-coordinate bound is re-derived here rather than imported from
//! `Rat.threshold_term_le`. NO `sorry` / `add_decl_unchecked` /
//! `add_decl_structural` / `native_decide` / `unsafe` / `Real`. No axiom added.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Cached carrier atoms for the cheap friedgut rungs.
struct CheapRungConsts {
    nat: Expr,
    bool_: Expr,
    fin: Expr,
    hcpoint: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_ble: Expr,
    bool_and: Expr,
    bool_not: Expr,
    set_size_nat: Expr,
}

impl CheapRungConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            bool_: k("Bool"),
            fin: k("Fin"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_ble: k("Nat.ble"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    /// `Nat.succ Nat.zero` — the literal `1`.
    fn one_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    /// `Nat.ble k m`.
    fn ble(&self, k: Expr, m: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [k, m])
    }
    /// `Bool.and a b`.
    fn band(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.bool_and.clone(), [a, b])
    }
    /// `Bool.not a`.
    fn bnot(&self, a: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), a)
    }
    /// `BoolAnalysis.setSizeNat n S`.
    fn set_size_nat_of(&self, n: &Expr, s: Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s])
    }
    /// `fun (i : Fin n) => Bool.and (S i) (Bool.not (J i))` — the `S \ J`
    /// (set-difference) coordinate indicator.
    fn diff_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, j: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let s_i = Expr::app(s.clone(), i.clone());
        let j_i = Expr::app(j.clone(), i.clone());
        let body = self.band(s_i, self.bnot(j_i));
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
}

impl Environment {
    /// Initialize the cheap friedgut-specific rungs. Registers RUNG 1
    /// (`BoolAnalysis.notSubsetMask`) and RUNG 2
    /// (`BoolAnalysis.influence_threshold_card_le`). Idempotent. No axiom added
    /// or removed.
    pub fn init_boolean_analysis_friedgut_cheap_rungs(&mut self) -> Result<(), EnvError> {
        self.register_not_subset_mask()?;
        self.register_influence_threshold_card_le()?;
        Ok(())
    }

    /// RUNG 1: register the reducible carrier
    /// `BoolAnalysis.notSubsetMask (n : Nat) (S J : HCPoint n) : Bool
    ///   := Nat.ble 1 (setSizeNat n (fun i => Bool.and (S i) (Bool.not (J i))))`.
    ///
    /// The "`S ⊄ J`" indicator (`true` iff `S \ J` is non-empty). Reducible
    /// `Declaration::Definition`; its closure bottoms out in reducible
    /// `Nat.ble` / `setSizeNat` / `Bool.and` / `Bool.not`, so theorems over it
    /// stay `Constructive` with an empty admitted-axiom closure. Idempotent.
    pub fn register_not_subset_mask(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.notSubsetMask");
        if self
            .get_const(&name)
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        // Carriers: setSizeNat (+ HCPoint, Fin.sumNat, Bool.rec via foundations),
        // Bool.and / Bool.not (init_bool), Nat.ble (init_nat_cmp).
        self.register_set_size_nat()?; // BoolAnalysis.setSizeNat, HCPoint
        self.init_bool()?; // Bool.and, Bool.not
        self.init_nat_cmp()?; // Nat.ble

        let c = CheapRungConsts::new();

        // Type: (n : Nat) -> HCPoint n -> HCPoint n -> Bool
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, _s) = b.fresh_local(hcp.clone());
            let (j_id, _j) = b.fresh_local(hcp.clone());
            let r = b.mk_pi(j_id, BinderInfo::Default, hcp.clone(), c.bool_.clone());
            let r = b.mk_pi(s_id, BinderInfo::Default, hcp, r);
            let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        // Value:
        //   fun (n) (S) (J) =>
        //     Nat.ble 1 (setSizeNat n (fun (i : Fin n) => Bool.and (S i) (Bool.not (J i))))
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let hcp = c.hcpoint_of(&n);
            let (s_id, s) = b.fresh_local(hcp.clone());
            let (j_id, j) = b.fresh_local(hcp.clone());

            let diff = c.diff_fn(&b, &n, &s, &j);
            let size = c.set_size_nat_of(&n, diff);
            let body = c.ble(c.one_nat(), size);

            let r = b.mk_lam(j_id, BinderInfo::Default, hcp.clone(), body);
            let r = b.mk_lam(s_id, BinderInfo::Default, hcp, r);
            let r = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}

// ===========================================================================
// RUNG 2 — influence_threshold_card_le (coordinate-wise level Markov).
// ===========================================================================

/// Shared atoms for the RUNG 2 threshold-Markov bound. Embeds `OrderConsts`
/// for the `LE.le @Rat instLERat` order spelling shared with `Fin.sum_le`.
struct RungTwoConsts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_true: Expr,
    fin: Expr,
    bool_fn: Expr,
    influence: Expr,
    total_influence: Expr,
    ind: Expr,
    fin_sum: Expr,
    fin_sum_le: Expr,
    fin_sum_smul: Expr,
    rat_mul: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul_zero: Expr,
    rat_mul_one: Expr,
    bool_cases_on: Expr,
    eq_bool: Expr,
    eq_refl_bool: Expr,
}

impl RungTwoConsts {
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            bool_true: k("Bool.true"),
            fin: k("Fin"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            influence: k("BoolAnalysis.Influence"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
            ind: k("BoolAnalysis.ind"),
            fin_sum: k("Fin.sum"),
            fin_sum_le: k("Fin.sum_le"),
            fin_sum_smul: k("Fin.sum_smul"),
            rat_mul: k("Rat.mul"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul_zero: k("Rat.mul_zero"),
            rat_mul_one: k("Rat.mul_one"),
            // Bool.casesOn into a Prop motive (Sort 0).
            bool_cases_on: Expr::const_(Name::from_string("Bool.casesOn"), vec![l0]),
            eq_bool: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_refl_bool: Expr::const_(Name::from_string("Eq.refl"), vec![l1]),
        }
    }

    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn rat_le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    fn fin_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), g])
    }
    /// `b i = Bool.true`.
    fn bit_eq_true(&self, bit: Expr) -> Expr {
        Expr::apps(
            self.eq_bool.clone(),
            [self.bool_.clone(), bit, self.bool_true.clone()],
        )
    }
    /// `Eq Bool a b`.
    fn eq_bool_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq_bool.clone(), [self.bool_.clone(), a, b])
    }
    /// `@Eq.subst Rat motive a b h_eq h_motive_a : motive b`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_motive_a: Expr) -> Expr {
        self.order.subst(motive, a, b, h_eq, h_motive_a)
    }
    /// `Eq.symm.{1} Rat a b h : Eq b a`.
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
    /// `Rat.mul_zero a : Rat.mul a Rat.zero = a·0 = Rat.zero`.
    fn mul_zero(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_mul_zero.clone(), a.clone())
    }
    /// `Rat.mul_one a : Rat.mul a Rat.one = a·1 = a`.
    fn mul_one(&self, a: &Expr) -> Expr {
        Expr::app(self.rat_mul_one.clone(), a.clone())
    }

    /// `fun (i : Fin n) => ind (b i)` — the Rat-valued indicator of the mask `b`
    /// (so `Fin.sum n (this)` is the cardinality `|{i : b i = true}|`).
    fn card_fn(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let body = self.ind_of(Expr::app(b.clone(), i.clone()));
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `fun (i : Fin n) => Rat.mul tau (ind (b i))` — the tau-scaled indicator
    /// (the `Fin.sum_smul` integrand, and the LHS of `Fin.sum_le`).
    fn scaled_fn(&self, parent: &EnvDeclBuilder, n: &Expr, tau: &Expr, b: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let body = self.mul(tau.clone(), self.ind_of(Expr::app(b.clone(), i.clone())));
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `fun (i : Fin n) => Influence n f i` — the per-coordinate influence
    /// integrand (the RHS of `Fin.sum_le`; `Fin.sum n (this) ≡ TotalInfluence`).
    fn infl_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let body = self.influence_of(n, f, &i);
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `∀ (i : Fin n), 0 ≤ Influence n f i` — the influence-nonnegativity
    /// hypothesis `hnn`.
    fn hnn_type(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let body = self.rat_le(self.order.rat_zero.clone(), self.influence_of(n, f, &i));
        ch.finish_child(ch.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `∀ (i : Fin n), b i = Bool.true → tau ≤ Influence n f i` — the threshold
    /// hypothesis `hb`.
    fn hb_type(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, tau: &Expr, b: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let prem = self.bit_eq_true(Expr::app(b.clone(), i.clone()));
        let concl = self.rat_le(tau.clone(), self.influence_of(n, f, &i));
        let body = Expr::pi(BinderInfo::Default, prem, concl);
        ch.finish_child(ch.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    }

    /// Per-coordinate bound proof `tau · ind (b i) ≤ Influence n f i` at a fixed
    /// local `i`, via the eq-threaded `Bool.casesOn` on `b i`.
    ///
    /// `hnn_i : 0 ≤ Inf_i`, `hb_i : b i = true → tau ≤ Inf_i`.
    fn pointwise_bound(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        f: &Expr,
        tau: &Expr,
        b: &Expr,
        i: &Expr,
        hnn_i: Expr,
        hb_i: Expr,
    ) -> Expr {
        let b_i = Expr::app(b.clone(), i.clone());
        let inf_i = self.influence_of(n, f, i);
        // goal at a bit value `bb`: tau · ind(bb) ≤ Inf_i.
        let goal_at = |bb: Expr| self.rat_le(self.mul(tau.clone(), self.ind_of(bb)), inf_i.clone());

        // motive : fun (bb : Bool) => (b i = bb) → (tau · ind bb ≤ Inf_i)
        let motive = {
            let mut m = EnvDeclBuilder::child_of(parent);
            let (bb_id, bb) = m.fresh_local(self.bool_.clone());
            let prem = self.eq_bool_of(b_i.clone(), bb.clone());
            let body = Expr::pi(BinderInfo::Default, prem, goal_at(bb));
            m.finish_child(m.mk_lam(bb_id, BinderInfo::Default, self.bool_.clone(), body))
        };

        // false branch : (b i = false) → tau · ind(false) ≤ Inf_i.
        //   ind false ≡ 0, so goal ≡ tau·0 ≤ Inf_i. From hnn_i : 0 ≤ Inf_i,
        //   rewrite 0 ← tau·0 via Eq.symm (Rat.mul_zero tau).
        let false_branch = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
            let prem = self.eq_bool_of(b_i.clone(), bool_false.clone());
            let (he_id, _he) = d.fresh_local(prem.clone());
            let tau_zero = self.mul(tau.clone(), self.rat_zero.clone());
            // motive_le : fun (t : Rat) => t ≤ Inf_i
            let motive_le = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (t_id, t) = e.fresh_local(self.rat.clone());
                let body = self.rat_le(t, inf_i.clone());
                e.finish_child(e.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
            };
            // h_symm : Rat.zero = tau·0   (symm (Rat.mul_zero tau))
            let h_symm = self.symm_rat(tau_zero.clone(), self.rat_zero.clone(), self.mul_zero(tau));
            // subst motive_le (a := 0) (b := tau·0) h_symm hnn_i : tau·0 ≤ Inf_i
            let body = self.subst_rat(motive_le, self.rat_zero.clone(), tau_zero, h_symm, hnn_i);
            d.finish_child(d.mk_lam(he_id, BinderInfo::Default, prem, body))
        };

        // true branch : (b i = true) → tau · ind(true) ≤ Inf_i.
        //   ind true ≡ 1, so goal ≡ tau·1 ≤ Inf_i. From hb_i he : tau ≤ Inf_i,
        //   rewrite tau ← tau·1 via Eq.symm (Rat.mul_one tau).
        let true_branch = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let prem = self.eq_bool_of(b_i.clone(), self.bool_true.clone());
            let (he_id, he) = d.fresh_local(prem.clone());
            let tau_one = self.mul(tau.clone(), self.rat_one.clone());
            let motive_le = {
                let mut e = EnvDeclBuilder::child_of(&d);
                let (t_id, t) = e.fresh_local(self.rat.clone());
                let body = self.rat_le(t, inf_i.clone());
                e.finish_child(e.mk_lam(t_id, BinderInfo::Default, self.rat.clone(), body))
            };
            // hle : tau ≤ Inf_i   (hb_i he)
            let hle = Expr::app(hb_i, he);
            // h_symm : tau = tau·1   (symm (Rat.mul_one tau))
            let h_symm = self.symm_rat(tau_one.clone(), tau.clone(), self.mul_one(tau));
            // subst motive_le (a := tau) (b := tau·1) h_symm hle : tau·1 ≤ Inf_i
            let body = self.subst_rat(motive_le, tau.clone(), tau_one, h_symm, hle);
            d.finish_child(d.mk_lam(he_id, BinderInfo::Default, prem, body))
        };

        // @Bool.casesOn motive (b i) false_branch true_branch (Eq.refl Bool (b i))
        let refl_bi = Expr::apps(self.eq_refl_bool.clone(), [self.bool_.clone(), b_i.clone()]);
        Expr::apps(
            self.bool_cases_on.clone(),
            [motive, b_i, false_branch, true_branch, refl_bi],
        )
    }
}

impl Environment {
    /// RUNG 2: register
    /// `BoolAnalysis.influence_threshold_card_le :
    ///   ∀ (n) (f : BoolFn n) (tau : Rat) (b : Fin n → Bool),
    ///     (∀ i, 0 ≤ Influence n f i) →
    ///     (∀ i, b i = true → tau ≤ Influence n f i) →
    ///       tau · Fin.sum n (fun i => ind (b i)) ≤ TotalInfluence n f`.
    ///
    /// The coordinate-wise level-Markov bound `tau·|{i : Inf_i ≥ tau}| ≤ I[f]`
    /// (the threshold mask `b` supplied abstractly). Per-coordinate
    /// `Bool.casesOn` bound, summed via `Fin.sum_le`, with `tau` pulled out by
    /// `Fin.sum_smul`; the RHS `Σ_i Inf_i ≡ TotalInfluence n f` reducibly.
    /// Kernel-checked, constructive, empty admitted-axiom closure. Idempotent.
    pub fn register_influence_threshold_card_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.influence_threshold_card_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Carriers / bricks (each idempotent, each constructive, empty closure):
        self.init_boolean_analysis()?; // BoolFn, Influence, TotalInfluence, ind
        self.init_boolean_analysis_order_toolkit()?; // LE.le/instLERat order surface
        self.init_rat_field_inst()?; // Rat.mul_zero, Rat.mul_one
        self.init_fin_sum()?; // Fin.sum, Fin.sum_le, Fin.sum_smul
        self.init_bool()?; // Bool.casesOn, Bool.true/false
        self.init_eq()?; // Eq, Eq.refl, Eq.symm, Eq.subst

        let c = RungTwoConsts::new();

        // ── Type ──
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (tau_id, tau) = b.fresh_local(c.rat.clone());
            let mask_ty = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, _i) = d.fresh_local(fin_n.clone());
                d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, c.bool_.clone()))
            };
            let (b_id, bmask) = b.fresh_local(mask_ty.clone());

            let hnn_ty = c.hnn_type(&b, &n, &f);
            let hb_ty = c.hb_type(&b, &n, &f, &tau, &bmask);
            let (hnn_id, _) = b.fresh_local(hnn_ty.clone());
            let (hb_id, _) = b.fresh_local(hb_ty.clone());

            let lhs = c.mul(tau.clone(), c.fin_sum_of(&n, c.card_fn(&b, &n, &bmask)));
            let rhs = c.total_influence_of(&n, &f);
            let concl = c.rat_le(lhs, rhs);

            let e = b.mk_pi(hb_id, BinderInfo::Default, hb_ty, concl);
            let e = b.mk_pi(hnn_id, BinderInfo::Default, hnn_ty, e);
            let e = b.mk_pi(b_id, BinderInfo::Default, mask_ty, e);
            let e = b.mk_pi(tau_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // ── Value ──
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (tau_id, tau) = b.fresh_local(c.rat.clone());
            let mask_ty = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, _i) = d.fresh_local(fin_n.clone());
                d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, c.bool_.clone()))
            };
            let (b_id, bmask) = b.fresh_local(mask_ty.clone());
            let hnn_ty = c.hnn_type(&b, &n, &f);
            let hb_ty = c.hb_type(&b, &n, &f, &tau, &bmask);
            let (hnn_id, hnn) = b.fresh_local(hnn_ty.clone());
            let (hb_id, hb) = b.fresh_local(hb_ty.clone());

            // Integrands.
            let card = c.card_fn(&b, &n, &bmask);
            let scaled = c.scaled_fn(&b, &n, &tau, &bmask);
            let infl = c.infl_fn(&b, &n, &f);

            let sum_scaled = c.fin_sum_of(&n, scaled.clone());
            let sum_card = c.fin_sum_of(&n, card.clone());
            let sum_infl = c.fin_sum_of(&n, infl.clone());
            let tau_sum_card = c.mul(tau.clone(), sum_card.clone());

            // pointwise : ∀ i, tau · ind(b i) ≤ Inf_i
            //   = fun i => pointwise_bound … (hnn i) (hb i)
            let pointwise = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let fin_n = c.fin_of(&n);
                let (i_id, i) = d.fresh_local(fin_n.clone());
                let hnn_i = Expr::app(hnn.clone(), i.clone());
                let hb_i = Expr::app(hb.clone(), i.clone());
                let body = c.pointwise_bound(&d, &n, &f, &tau, &bmask, &i, hnn_i, hb_i);
                d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
            };

            // step1 : Fin.sum n scaled ≤ Fin.sum n infl
            //   := Fin.sum_le n scaled infl pointwise
            let step1 = Expr::apps(
                c.fin_sum_le.clone(),
                [n.clone(), scaled.clone(), infl.clone(), pointwise],
            );

            // smul : Fin.sum n scaled = tau · Fin.sum n card
            //   := Fin.sum_smul n tau card
            //   (Fin.sum_smul gives Fin.sum n (fun i => tau · card i) = tau · Fin.sum n card;
            //    `scaled` IS `fun i => tau · (ind (b i))` = `fun i => tau · card i`.)
            let smul = Expr::apps(
                c.fin_sum_smul.clone(),
                [n.clone(), tau.clone(), card.clone()],
            );

            // Rewrite step1's LHS `Fin.sum n scaled` to `tau · Fin.sum n card`
            // via Eq.subst (motive t => t ≤ Fin.sum n infl) along `smul`.
            //   Result : tau · Fin.sum n card ≤ Fin.sum n infl.
            // Fin.sum n infl ≡ TotalInfluence n f (reducible), so this is the goal.
            let motive_le = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = d.fresh_local(c.rat.clone());
                let body = c.rat_le(t, sum_infl.clone());
                d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            let body = c.subst_rat(motive_le, sum_scaled, tau_sum_card, smul, step1);

            let e = b.mk_lam(hb_id, BinderInfo::Default, hb_ty, body);
            let e = b.mk_lam(hnn_id, BinderInfo::Default, hnn_ty, e);
            let e = b.mk_lam(b_id, BinderInfo::Default, mask_ty, e);
            let e = b.mk_lam(tau_id, BinderInfo::Default, c.rat.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

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

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_friedgut_cheap_rungs()
            .expect("init_boolean_analysis_friedgut_cheap_rungs");
        env.init_boolean_analysis_friedgut_cheap_rungs()
            .expect("idempotent");
        env
    }

    /// RUNG 1 is a reducible `Definition`, kernel-checks, and carries an EMPTY
    /// admitted-axiom closure (foundational only) — the soundness rail for a
    /// carrier Definition. (`proof_quality` returns `NotATheorem` for any
    /// `Definition`; the `Constructive` label is theorem-specific, so the
    /// empty-`axiom_deps` closure below is the carrier's axiom-freeness check —
    /// it is exactly what powers `Constructive` for theorems built over it.)
    #[test]
    fn test_not_subset_mask_is_reducible_definition_empty_closure() {
        let env = env();
        let name = "BoolAnalysis.notSubsetMask";
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "{name} must be a Definition"
        );
        assert!(info.is_reducible, "{name} must be a reducible Definition");
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "{name} closure must be foundational-only: {:?}",
            env.axiom_deps(&nm)
        );
    }

    /// RUNG 2 is a `Theorem`, kernel-checks, is `Constructive`, and carries an
    /// empty admitted-axiom closure.
    #[test]
    fn test_influence_threshold_card_le_is_constructive_theorem() {
        let env = env();
        let name = "BoolAnalysis.influence_threshold_card_le";
        let nm = Name::from_string(name);
        let info = env
            .get_const(&nm)
            .unwrap_or_else(|| panic!("{name} registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
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
