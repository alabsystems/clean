// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut TCB 5→3 CO-LAND — the WIRING lemma `BoolAnalysis.friedgut_boolean_proof`.
//!
//! This module assembles the four landed, constructive, empty-closure case-lemmas
//! (`friedgut_boolean_case_le` / `_empty` / `_threshold` + the `variance_le_*` /
//! `total_influence_nonneg` supports) into ONE proof term whose type is exactly the
//! v3 faithful helper body (`Environment::friedgut_l2_faithful_body_v3`):
//!
//! ```text
//! BoolAnalysis.friedgut_boolean_proof :
//!   ∀ (n : Nat) (f : BoolFn n) (K eps : Rat),
//!     Rat.le (TotalInfluence n f) K →                  -- hI : I[f] ≤ K
//!     Rat.le Rat.zero eps →                            -- heps : 0 ≤ eps
//!     ∀ (e : Nat),
//!       And (Rat.le (natCast(2^e)·eps) K)
//!           (Rat.le K (natCast(2^(e+1))·eps)) →        -- guard (two-sided band)
//!         Exists (fun (J : HCPoint n) =>
//!           And (Nat.le (setSizeNat n J) (Nat.pow 2 (48·2^e)))
//!               (Rat.le (subsetSum n (fun S =>
//!                          ind(notSubsetMask n S J)·(f̂ S·f̂ S))) eps))
//! ```
//!
//! # The assembly (3-way `Bool.casesOn` split, no tactics)
//!
//! Let `B := Nat.pow 2 (48·2^e)` (the v3 junta budget). Case on `Nat.ble n B`:
//!
//! * `Nat.ble n B = true`  (`n ≤ B`): `friedgut_boolean_case_le n f eps B
//!   (Nat.le_of_ble_eq_true n B refl) heps` — the full-coordinate witness.
//!
//! * `Nat.ble n B = false` (`n > B`): case on `Rat.ble 1 eps`:
//!   - `= true`  (`1 ≤ eps`): `friedgut_boolean_case_empty n f eps B hvar`, where
//!     `hvar : Variance ≤ eps` is `Var ≤ 1 ≤ eps`
//!     (`variance_le_one` + `Rat.le_of_ble_eq_true 1 eps`).
//!   - `= false` (`eps < 1`): case on `Rat.ble eps 0`:
//!     - `= true`  (`eps ≤ 0`): with `heps : 0 ≤ eps` we get `eps = 0`
//!       (`Rat.le_antisymm`); `friedgut_boolean_case_empty n f eps B hvar`, where
//!       `hvar : Var ≤ eps` is `Var ≤ I ≤ K ≤ 2^(e+1)·eps = 2^(e+1)·0 = 0 = eps`.
//!     - `= false` (`0 < eps`): `friedgut_boolean_case_threshold n f K eps e hI
//!       (0<eps) (eps<1) guard (B<n)` — the genuine Friedgut threshold junta.
//!
//! The discriminant equalities are recovered with the standard dependent-`casesOn`
//! eq-thread: motive `fun (b:Bool) => Eq Bool disc b → Goal`, branches take
//! `h : Eq Bool disc <ctor>`, applied to `Eq.refl Bool disc`. The `B < n` fact in
//! the threshold branch comes from `Nat.le_or_lt n B` + `Nat.not_le_of_ble_eq_false`.
//!
//! Every case-lemma's `Exists` predicate is BYTE-IDENTICAL to the v3 body at
//! `B := Nat.pow 2 (48·2^e)` (workflow-verified), so the assembly type-checks to the
//! v3 body verbatim. Kernel-checked, `Constructive`, EMPTY admitted-axiom closure
//! (⊆ {propext, Quot.sound, Classical.choice}). Hand-constructed `Expr` (no tactics).
//! Idempotent. No axiom added or removed. NO `sorry` / `sorryAx` /
//! `add_decl_unchecked` / `add_decl_structural` / `native_decide` / `unsafe` /
//! `Real` / `Rat.dist` / new `Axiom`. Gated behind
//! `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared carrier atoms — spellings byte-match the v3 body
/// (`friedgut_l2_faithful_body_v3`) and the four case-lemmas.
struct WireConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_true: Expr,
    bool_false: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_mul: Expr,
    nat_pow: Expr,
    nat_ble: Expr,
    nat_le: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_mul: Expr,
    rat_ble: Expr,
    rat_mk: Expr,
    int_of_nat: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fourier: Expr,
    subset_sum: Expr,
    ind: Expr,
    not_subset_mask: Expr,
    set_size_nat: Expr,
    total_influence: Expr,
    variance: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    l0: Level,
    l1: Level,
}

impl WireConsts {
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_mul: k("Nat.mul"),
            nat_pow: k("Nat.pow"),
            nat_ble: k("Nat.ble"),
            nat_le: k("Nat.le"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_mul: k("Rat.mul"),
            rat_ble: k("Rat.ble"),
            rat_mk: k("Rat.mk"),
            int_of_nat: k("Int.ofNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            ind: k("BoolAnalysis.ind"),
            not_subset_mask: k("BoolAnalysis.notSubsetMask"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
            variance: k("BoolAnalysis.Variance"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: k("instLERat"),
            l0,
            l1,
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
    fn succ(&self, x: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), x)
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn nmul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_mul.clone(), [a, b])
    }
    /// `Nat.pow 2 e`.
    fn pow2(&self, e: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.nat_lit(2), e.clone()])
    }
    fn nat_ble_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    fn rat_ble_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_ble.clone(), [a, b])
    }
    fn nat_le_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `Nat.lt a b ≡ Nat.le (succ a) b`.
    fn nat_lt_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Nat.lt"), vec![]), [a, b])
    }
    /// `natCast m := Rat.mk (Int.ofNat m) 1`.
    fn natcast(&self, m: &Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), m.clone()),
                self.nat_one(),
            ],
        )
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn not_subset_mask_of(&self, n: &Expr, s: &Expr, j: &Expr) -> Expr {
        Expr::apps(
            self.not_subset_mask.clone(),
            [n.clone(), s.clone(), j.clone()],
        )
    }
    fn set_size_nat_of(&self, n: &Expr, j: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), j.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    fn variance_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.variance.clone(), [n.clone(), f.clone()])
    }
    /// `@LE.le.{0} Rat instLERat a b` — the v3-body order spelling.
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), a, b],
        )
    }
    /// Bare `Rat.le a b` — the spelling `Rat.le_trans` / `Rat.le_antisymm` consume.
    fn rle(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.le"), vec![]), [a, b])
    }
    fn and(&self, p: Expr, q: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("And"), vec![]), [p, q])
    }
    /// `Eq.{1} Bool a b`.
    fn eq_bool(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.bool_.clone(), a, b],
        )
    }
    /// `Eq.refl.{1} Bool x`.
    fn refl_bool(&self, x: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.l1.clone()]),
            [self.bool_.clone(), x],
        )
    }
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    /// `Eq.subst.{2} Rat motive a b h_eq h_a : motive b`.
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }
    /// `Rat.le_trans a b c h1 h2 : Rat.le a c`.
    fn le_trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            [a, b, cc, h1, h2],
        )
    }

    /// `fun (J : HCPoint n) => And (Nat.le (setSizeNat n J) B)
    ///   (Rat.le (subsetSum n (fun S => ind(notSubsetMask n S J)·(f̂ S·f̂ S))) eps))`
    /// — the v3-body `Exists` predicate at bound `B`. BYTE-IDENTICAL to all four
    /// case-lemmas (which leave the bound as a `∀ B` parameter) at
    /// `B := Nat.pow 2 (48·2^e)`, and to `friedgut_l2_faithful_body_v3`.
    fn pred_of(
        &self,
        parent: &EnvDeclBuilder,
        n: &Expr,
        f: &Expr,
        eps: &Expr,
        big_b: &Expr,
    ) -> Expr {
        let mut g = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (j_id, j) = g.fresh_local(hcp.clone());
        let size_concl = self.nat_le_of(self.set_size_nat_of(n, &j), big_b.clone());
        let mass_fn = {
            let mut h = EnvDeclBuilder::child_of(&g);
            let (s_id, s) = h.fresh_local(hcp.clone());
            let coeff = self.fourier_of(n, f, &s);
            let sq = self.mul(coeff.clone(), coeff);
            let mask = self.not_subset_mask_of(n, &s, &j);
            let body = self.mul(self.ind_of(mask), sq);
            h.finish_child(h.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
        };
        let mass_concl = self.le(self.ssum(n, mass_fn), eps.clone());
        let and = self.and(size_concl, mass_concl);
        g.finish_child(g.mk_lam(j_id, BinderInfo::Default, hcp, and))
    }
}

/// Build the `friedgut_boolean_proof` type (`for_value=false`) / proof
/// (`for_value=true`). Hand-constructed `Expr`, no tactics.
fn wiring_build(for_value: bool) -> Expr {
    let c = WireConsts::new();
    let u1 = c.l1.clone();
    let exists_c = Expr::const_(Name::from_string("Exists"), vec![u1.clone()]);

    // Const handles for the case-lemmas + bridges.
    let case_le = Expr::const_(
        Name::from_string("BoolAnalysis.friedgut_boolean_case_le"),
        vec![],
    );
    let case_empty = Expr::const_(
        Name::from_string("BoolAnalysis.friedgut_boolean_case_empty"),
        vec![],
    );
    let case_threshold = Expr::const_(
        Name::from_string("BoolAnalysis.friedgut_boolean_case_threshold"),
        vec![],
    );
    let variance_le_one = Expr::const_(Name::from_string("BoolAnalysis.variance_le_one"), vec![]);
    let variance_le_influence = Expr::const_(
        Name::from_string("BoolAnalysis.variance_le_influence"),
        vec![],
    );
    let nat_le_of_ble = Expr::const_(Name::from_string("Nat.le_of_ble_eq_true"), vec![]);
    let rat_le_of_ble = Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]);
    let rat_lt_of_ble_false = Expr::const_(Name::from_string("Rat.lt_of_ble_eq_false"), vec![]);
    let le_antisymm = Expr::const_(Name::from_string("Rat.le_antisymm"), vec![]);
    let mul_zero = Expr::const_(Name::from_string("Rat.mul_zero"), vec![]);
    let nat_le_or_lt = Expr::const_(Name::from_string("Nat.le_or_lt"), vec![]);
    let not_le_of_ble_false = Expr::const_(Name::from_string("Nat.not_le_of_ble_eq_false"), vec![]);
    let false_elim = Expr::const_(Name::from_string("False.elim"), vec![c.l0.clone()]);
    let or_rec = Expr::const_(Name::from_string("Or.rec"), vec![]);
    let bool_cases = Expr::const_(Name::from_string("Bool.casesOn"), vec![c.l0.clone()]);

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let (k_id, kk) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let infl = c.total_influence_of(&n, &f);
    // hI : I[f] ≤ K   (v3 body spelling: @LE.le Rat instLERat).
    let hi_ty = c.le(infl.clone(), kk.clone());
    // heps : 0 ≤ eps.
    let heps_ty = c.le(c.rat_zero.clone(), eps.clone());

    if !for_value {
        // Build the `∀ e, guard → Exists …` tail as a child of `b`.
        let mut d = EnvDeclBuilder::child_of(&b);
        let (e_id, e) = d.fresh_local(c.nat.clone());
        let pow_e = c.pow2(&e);
        let e1 = c.succ(e.clone());
        let pow_e1 = c.pow2(&e1);
        let guard_lo = c.le(c.mul(c.natcast(&pow_e), eps.clone()), kk.clone());
        let guard_hi = c.le(kk.clone(), c.mul(c.natcast(&pow_e1), eps.clone()));
        let guard_ty = c.and(guard_lo, guard_hi);
        let (g_id, _guard) = d.fresh_local(guard_ty.clone());
        let budget = c.nmul(c.nat_lit(48), pow_e.clone());
        let big_b = Expr::apps(c.nat_pow.clone(), [c.nat_lit(2), budget]);
        let pred = c.pred_of(&d, &n, &f, &eps, &big_b);
        let goal = Expr::apps(exists_c.clone(), [c.hcpoint_of(&n), pred]);
        let body = d.mk_pi(g_id, BinderInfo::Default, guard_ty, goal);
        let tail = d.finish_child(d.mk_pi(e_id, BinderInfo::Default, c.nat.clone(), body));

        let (heps_id, _) = b.fresh_local(heps_ty.clone());
        let (hi_id, _) = b.fresh_local(hi_ty.clone());
        let e = b.mk_pi(heps_id, BinderInfo::Default, heps_ty, tail);
        let e = b.mk_pi(hi_id, BinderInfo::Default, hi_ty, e);
        let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_pi(k_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
        return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
    }

    // ── value ──
    let (hi_id, hi) = b.fresh_local(hi_ty.clone());
    let (heps_id, heps) = b.fresh_local(heps_ty.clone());

    // `∀ e, guard → Goal` proof, built in the `d` child of `b`.
    let mut d = EnvDeclBuilder::child_of(&b);
    let (e_id, e) = d.fresh_local(c.nat.clone());
    let pow_e = c.pow2(&e);
    let e1 = c.succ(e.clone());
    let pow_e1 = c.pow2(&e1);
    let guard_lo = c.le(c.mul(c.natcast(&pow_e), eps.clone()), kk.clone());
    let guard_hi = c.le(kk.clone(), c.mul(c.natcast(&pow_e1), eps.clone()));
    let guard_ty = c.and(guard_lo.clone(), guard_hi.clone());
    let (g_id, guard) = d.fresh_local(guard_ty.clone());

    // B := Nat.pow 2 (48·2^e) ; Goal := Exists (pred_of … B).
    let budget = c.nmul(c.nat_lit(48), pow_e.clone());
    let big_b = Expr::apps(c.nat_pow.clone(), [c.nat_lit(2), budget]);
    let pred = c.pred_of(&d, &n, &f, &eps, &big_b);
    let goal = Expr::apps(exists_c.clone(), [c.hcpoint_of(&n), pred]);

    // discriminants.
    let disc_e0 = c.rat_ble_of(eps.clone(), c.rat_zero.clone());
    let disc_1e = c.rat_ble_of(c.rat_one.clone(), eps.clone());
    let disc_nb = c.nat_ble_of(n.clone(), big_b.clone());

    // ---- helper: B < n from hn_false : Eq Bool (Nat.ble n B) false ----
    let mk_bltn = |g: &EnvDeclBuilder, hn_false: Expr| -> Expr {
        let le_n_b = c.nat_le_of(n.clone(), big_b.clone());
        let lt_b_n = c.nat_lt_of(big_b.clone(), n.clone());
        let or_motive = {
            let mut m = EnvDeclBuilder::child_of(g);
            let or_ty = Expr::apps(
                Expr::const_(Name::from_string("Or"), vec![]),
                [le_n_b.clone(), lt_b_n.clone()],
            );
            let (z_id, _z) = m.fresh_local(or_ty.clone());
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, or_ty, lt_b_n.clone()))
        };
        let left = {
            let mut m = EnvDeclBuilder::child_of(g);
            let (hle_id, hle) = m.fresh_local(le_n_b.clone());
            let not_le = Expr::apps(
                not_le_of_ble_false.clone(),
                [n.clone(), big_b.clone(), hn_false.clone()],
            );
            let false_val = Expr::app(not_le, hle);
            let body = Expr::apps(false_elim.clone(), [lt_b_n.clone(), false_val]);
            m.finish_child(m.mk_lam(hle_id, BinderInfo::Default, le_n_b.clone(), body))
        };
        let right = {
            let mut m = EnvDeclBuilder::child_of(g);
            let (hlt_id, hlt) = m.fresh_local(lt_b_n.clone());
            m.finish_child(m.mk_lam(hlt_id, BinderInfo::Default, lt_b_n.clone(), hlt))
        };
        let tot = Expr::apps(nat_le_or_lt.clone(), [n.clone(), big_b.clone()]);
        Expr::apps(
            or_rec.clone(),
            [le_n_b, lt_b_n, or_motive, left, right, tot],
        )
    };

    // ---- eps≤0 branch: hvar : Var ≤ eps ----
    let mk_hvar_le0 = |g: &EnvDeclBuilder, h_le0_ble: Expr, guard_hi_proof: Expr| -> Expr {
        // h_le0 : Rat.le eps 0 := Rat.le_of_ble_eq_true eps 0 h_le0_ble.
        let h_le0 = Expr::apps(
            rat_le_of_ble.clone(),
            [eps.clone(), c.rat_zero.clone(), h_le0_ble],
        );
        // eps_eq_0 : Eq Rat eps 0 := Rat.le_antisymm eps 0 h_le0 heps.
        let eps_eq_0 = Expr::apps(
            le_antisymm.clone(),
            [eps.clone(), c.rat_zero.clone(), h_le0, heps.clone()],
        );
        let var = c.variance_of(&n, &f);
        // v_le_i : Var ≤ I (bare Rat.le).
        let v_le_i = Expr::apps(variance_le_influence.clone(), [n.clone(), f.clone()]);
        // v_le_k : Var ≤ K := le_trans Var I K v_le_i hI.
        let v_le_k = c.le_trans(var.clone(), infl.clone(), kk.clone(), v_le_i, hi.clone());
        // v_le_2e1eps : Var ≤ 2^(e+1)·eps := le_trans Var K (2^(e+1)·eps).
        let two_pe1 = c.natcast(&pow_e1);
        let two_pe1_eps = c.mul(two_pe1.clone(), eps.clone());
        let v_le_2e1eps = c.le_trans(
            var.clone(),
            kk.clone(),
            two_pe1_eps.clone(),
            v_le_k,
            guard_hi_proof,
        );
        // congr_eps : 2^(e+1)·eps = 2^(e+1)·0  := congrArg (fun z => 2^(e+1)·z) eps_eq_0.
        let f_mul = {
            let mut m = EnvDeclBuilder::child_of(g);
            let (z_id, z) = m.fresh_local(c.rat.clone());
            let body = c.mul(two_pe1.clone(), z);
            m.finish_child(m.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
        };
        let congr_eps = Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![c.l1.clone(), c.l1.clone()],
            ),
            [
                c.rat.clone(),
                c.rat.clone(),
                eps.clone(),
                c.rat_zero.clone(),
                f_mul,
                eps_eq_0.clone(),
            ],
        );
        // mz : 2^(e+1)·0 = 0 := Rat.mul_zero (2^(e+1)).
        let two_pe1_zero = c.mul(two_pe1.clone(), c.rat_zero.clone());
        let mz = Expr::app(mul_zero.clone(), two_pe1.clone());
        // chain : 2^(e+1)·eps = 0 := Eq.trans congr_eps mz.
        let chain = Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![c.l1.clone()]),
            [
                c.rat.clone(),
                two_pe1_eps.clone(),
                two_pe1_zero,
                c.rat_zero.clone(),
                congr_eps,
                mz,
            ],
        );
        // motive_t : fun (t : Rat) => Rat.le Var t.
        let motive_t = {
            let mut m = EnvDeclBuilder::child_of(g);
            let (t_id, t) = m.fresh_local(c.rat.clone());
            let body = c.rle(var.clone(), t);
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
        };
        // v_le_0 : Var ≤ 0  := subst motive_t (2^(e+1)eps) 0 chain v_le_2e1eps.
        let v_le_0 = c.subst_rat(
            motive_t.clone(),
            two_pe1_eps,
            c.rat_zero.clone(),
            chain,
            v_le_2e1eps,
        );
        // zero_eq_eps : 0 = eps := symm eps_eq_0.
        let zero_eq_eps = c.symm_rat(eps.clone(), c.rat_zero.clone(), eps_eq_0);
        // Var ≤ eps := subst motive_t 0 eps zero_eq_eps v_le_0.
        c.subst_rat(
            motive_t,
            c.rat_zero.clone(),
            eps.clone(),
            zero_eq_eps,
            v_le_0,
        )
    };

    // ---- eps≥1 branch: hvar : Var ≤ eps ----
    let mk_hvar_ge1 = |h1t_ble: Expr| -> Expr {
        let var = c.variance_of(&n, &f);
        let v_le_1 = Expr::apps(variance_le_one.clone(), [n.clone(), f.clone()]);
        let one_le_eps = Expr::apps(
            rat_le_of_ble.clone(),
            [c.rat_one.clone(), eps.clone(), h1t_ble],
        );
        c.le_trans(var, c.rat_one.clone(), eps.clone(), v_le_1, one_le_eps)
    };

    let mk_case_empty = |hvar: Expr| -> Expr {
        Expr::apps(
            case_empty.clone(),
            [n.clone(), f.clone(), eps.clone(), big_b.clone(), hvar],
        )
    };

    // (A) eps<1 branch: case on `Rat.ble eps 0`.
    let eps_lt1_body = |g: &EnvDeclBuilder, h1f: Expr, hn_false: Expr| -> Expr {
        let motive_e0 = {
            let mut m = EnvDeclBuilder::child_of(g);
            let (bb_id, bb) = m.fresh_local(c.bool_.clone());
            let prem = c.eq_bool(disc_e0.clone(), bb.clone());
            let body = Expr::pi(BinderInfo::Default, prem, goal.clone());
            m.finish_child(m.mk_lam(bb_id, BinderInfo::Default, c.bool_.clone(), body))
        };
        // false (0 < eps) → THRESHOLD.
        let false_branch = {
            let mut m = EnvDeclBuilder::child_of(g);
            let prem = c.eq_bool(disc_e0.clone(), c.bool_false.clone());
            let (h0_id, h0) = m.fresh_local(prem.clone());
            let h_pos = Expr::apps(
                rat_lt_of_ble_false.clone(),
                [eps.clone(), c.rat_zero.clone(), h0],
            );
            let h_lt1 = Expr::apps(
                rat_lt_of_ble_false.clone(),
                [c.rat_one.clone(), eps.clone(), h1f.clone()],
            );
            let bltn = mk_bltn(&m, hn_false.clone());
            let body = Expr::apps(
                case_threshold.clone(),
                [
                    n.clone(),
                    f.clone(),
                    kk.clone(),
                    eps.clone(),
                    e.clone(),
                    hi.clone(),
                    h_pos,
                    h_lt1,
                    guard.clone(),
                    bltn,
                ],
            );
            m.finish_child(m.mk_lam(h0_id, BinderInfo::Default, prem, body))
        };
        // true (eps ≤ 0) → EMPTY.
        let true_branch = {
            let mut m = EnvDeclBuilder::child_of(g);
            let prem = c.eq_bool(disc_e0.clone(), c.bool_true.clone());
            let (h0_id, h0t) = m.fresh_local(prem.clone());
            let guard_hi_proof = Expr::apps(
                Expr::const_(Name::from_string("And.right"), vec![]),
                [guard_lo.clone(), guard_hi.clone(), guard.clone()],
            );
            let hvar = mk_hvar_le0(&m, h0t, guard_hi_proof);
            let body = mk_case_empty(hvar);
            m.finish_child(m.mk_lam(h0_id, BinderInfo::Default, prem, body))
        };
        let cases = Expr::apps(
            bool_cases.clone(),
            [motive_e0, disc_e0.clone(), false_branch, true_branch],
        );
        Expr::app(cases, c.refl_bool(disc_e0.clone()))
    };

    // (B) n>B branch: case on `Rat.ble 1 eps`.
    let n_gt_b_body = |g: &EnvDeclBuilder, hn_false: Expr| -> Expr {
        let motive_1e = {
            let mut m = EnvDeclBuilder::child_of(g);
            let (bb_id, bb) = m.fresh_local(c.bool_.clone());
            let prem = c.eq_bool(disc_1e.clone(), bb.clone());
            let body = Expr::pi(BinderInfo::Default, prem, goal.clone());
            m.finish_child(m.mk_lam(bb_id, BinderInfo::Default, c.bool_.clone(), body))
        };
        // false (eps < 1) → eps_lt1_body.
        let false_branch = {
            let mut m = EnvDeclBuilder::child_of(g);
            let prem = c.eq_bool(disc_1e.clone(), c.bool_false.clone());
            let (h1f_id, h1f) = m.fresh_local(prem.clone());
            let body = eps_lt1_body(&m, h1f, hn_false.clone());
            m.finish_child(m.mk_lam(h1f_id, BinderInfo::Default, prem, body))
        };
        // true (1 ≤ eps) → EMPTY.
        let true_branch = {
            let mut m = EnvDeclBuilder::child_of(g);
            let prem = c.eq_bool(disc_1e.clone(), c.bool_true.clone());
            let (h1t_id, h1t) = m.fresh_local(prem.clone());
            let hvar = mk_hvar_ge1(h1t);
            let body = mk_case_empty(hvar);
            m.finish_child(m.mk_lam(h1t_id, BinderInfo::Default, prem, body))
        };
        let cases = Expr::apps(
            bool_cases.clone(),
            [motive_1e, disc_1e.clone(), false_branch, true_branch],
        );
        Expr::app(cases, c.refl_bool(disc_1e.clone()))
    };

    // (C) outermost: case on `Nat.ble n B`.
    let motive_nb = {
        let mut m = EnvDeclBuilder::child_of(&d);
        let (bb_id, bb) = m.fresh_local(c.bool_.clone());
        let prem = c.eq_bool(disc_nb.clone(), bb.clone());
        let body = Expr::pi(BinderInfo::Default, prem, goal.clone());
        m.finish_child(m.mk_lam(bb_id, BinderInfo::Default, c.bool_.clone(), body))
    };
    let nb_false_branch = {
        let mut m = EnvDeclBuilder::child_of(&d);
        let prem = c.eq_bool(disc_nb.clone(), c.bool_false.clone());
        let (hnf_id, hnf) = m.fresh_local(prem.clone());
        let body = n_gt_b_body(&m, hnf);
        m.finish_child(m.mk_lam(hnf_id, BinderInfo::Default, prem, body))
    };
    let nb_true_branch = {
        let mut m = EnvDeclBuilder::child_of(&d);
        let prem = c.eq_bool(disc_nb.clone(), c.bool_true.clone());
        let (hnt_id, hnt) = m.fresh_local(prem.clone());
        let n_le_b = Expr::apps(nat_le_of_ble.clone(), [n.clone(), big_b.clone(), hnt]);
        let body = Expr::apps(
            case_le.clone(),
            [
                n.clone(),
                f.clone(),
                eps.clone(),
                big_b.clone(),
                n_le_b,
                heps.clone(),
            ],
        );
        m.finish_child(m.mk_lam(hnt_id, BinderInfo::Default, prem, body))
    };
    let cases_nb = Expr::apps(
        bool_cases.clone(),
        [motive_nb, disc_nb.clone(), nb_false_branch, nb_true_branch],
    );
    let goal_proof = Expr::app(cases_nb, c.refl_bool(disc_nb.clone()));

    // λ e, λ guard, goal_proof.
    let lam_guard = d.mk_lam(g_id, BinderInfo::Default, guard_ty, goal_proof);
    let tail = d.finish_child(d.mk_lam(e_id, BinderInfo::Default, c.nat.clone(), lam_guard));

    // λ n f K eps, λ hI, λ heps, tail.
    let ee = b.mk_lam(heps_id, BinderInfo::Default, heps_ty, tail);
    let ee = b.mk_lam(hi_id, BinderInfo::Default, hi_ty, ee);
    let ee = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), ee);
    let ee = b.mk_lam(k_id, BinderInfo::Default, c.rat.clone(), ee);
    let ee = b.mk_lam(f_id, BinderInfo::Default, bf_ty, ee);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), ee))
}

impl Environment {
    /// `BoolAnalysis.friedgut_boolean_proof` — the WIRING lemma: the four landed
    /// case-lemmas assembled into a single proof of the v3 faithful helper body.
    /// Kernel-checked, `Constructive`, EMPTY admitted-axiom closure. Idempotent.
    /// No axiom added or removed. See the module docs for the assembly.
    pub fn register_friedgut_boolean_proof(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_boolean_proof");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_boolean_analysis_order_toolkit()?;
        self.init_bool()?; // Bool.casesOn, Bool.true/false
        self.init_or()?; // Or.rec
        self.init_true_false()?; // False.elim
        self.init_rat_field_inst()?; // Rat.mul_zero
                                     // The four case-lemmas + supports.
        self.register_friedgut_boolean_case_le()?;
        self.register_friedgut_boolean_case_empty()?;
        self.register_friedgut_boolean_case_threshold()?;
        self.register_variance_le_one()?;
        self.register_variance_le_influence()?;
        self.register_total_influence_nonneg()?;
        // Bridges.
        self.register_nat_ble_le_lemmas()?; // Nat.le_of_ble_eq_true, Nat.not_le_of_ble_eq_false
        self.register_rat_minmax_proofs()?; // Rat.le_of_ble_eq_true, Rat.ble
        self.init_algebra_nnreal_sqrt_strict()?; // Rat.lt_of_ble_eq_false
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.register_nat_mul_left_cancel_succ_proof()?; // Nat.le_or_lt
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let ty = wiring_build(false);
        let value = wiring_build(true);
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

    #[test]
    fn test_friedgut_boolean_proof_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_boolean_proof()
            .expect("register_friedgut_boolean_proof");
        env.register_friedgut_boolean_proof().expect("idempotent");

        let nm = Name::from_string("BoolAnalysis.friedgut_boolean_proof");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "friedgut_boolean_proof must be a Theorem"
        );
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("friedgut_boolean_proof must kernel-check");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "friedgut_boolean_proof must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "friedgut_boolean_proof closure must be empty, got {:?}",
            env.axiom_deps(&nm)
                .expect("deps")
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }
}
