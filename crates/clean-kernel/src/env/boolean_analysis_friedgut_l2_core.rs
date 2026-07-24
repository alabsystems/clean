// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut junta-theorem roadmap — STEP 5 ASSEMBLY: `friedgut_l2_core` and the
//! two new transport bricks it consumes (`subsetSum_add`, the degree-band split
//! `friedgut_band_split`, and the high-degree mask-drop
//! `friedgut_high_mask_drop`).
//!
//! This module closes the faithful O'Donnell §9.6 **L2-distance** Friedgut
//! conclusion (NOT the Bool-junta corollary): the masked Fourier mass
//! `Σ_{S⊄J} f̂(S)²` is bounded by `eps`, with the LOW band charged by the banked
//! `friedgut_restricted_mass_le` (`Σ_{S⊄J,|S|≤d} f̂² ≤ 9^d·(dr·I)`) and the HIGH
//! band by the banked `high_degree_mass_le` (`(d+1)·M_{≥d+1} ≤ I`).
//!
//! ## What this module proves (all `Constructive`, EMPTY admitted-axiom closure)
//!
//! 1. `BoolAnalysis.subsetSum_add` —
//!    `Σ_S (G S + H S) = Σ_S G S + Σ_S H S` (`Fin.sum_add` lifted to `subsetSum`).
//! 2. `BoolAnalysis.friedgut_band_split` —
//!    `Σ_S ind(notSubset)·f̂² = LOW + HIGH`, where
//!    `LOW := Σ_S ind(notSubset)·(ind(ble |S| d)·f̂²)` (byte-identical to the
//!    banked LOW band's integrand) and
//!    `HIGH := Σ_S ind(notSubset)·(ind(ble (d+1) |S|)·f̂²)`. Proved via the
//!    pointwise band-complement `w = ind(ble m d)·w + ind(ble (d+1) m)·w`
//!    (`Nat.not_ble_succ_eq_ble` + `Bool.casesOn` on `ble m d`), masked on the
//!    left by `ind(notSubset)` and distributed, then `subsetSum_congr` +
//!    `subsetSum_add`.
//! 3. `BoolAnalysis.friedgut_high_mask_drop` —
//!    `HIGH ≤ Σ_S ind(ble (d+1) |S|)·f̂² = M_{≥d+1}` (drop the `ind(notSubset) ≤ 1`
//!    factor; per-`S` `ind_le_one` + nonneg `ind(ble..)·f̂²`, `subsetSum_le`).
//! 4. `BoolAnalysis.friedgut_l2_core` (the assembly) —
//!    `∀ n d f J dr K eps, … → Σ_{S⊄J} f̂² ≤ eps`, given the LOW-band hypotheses
//!    (the outside-J coords have `Inf_i ≤ dr²`), `9^d·(dr·I) ≤ eps/2`,
//!    `(d+1)·(eps/2) hi-degree budget` (`M_{≥d+1} ≤ eps/2` via
//!    `high_degree_mass_le` divided through), and `2^(d+1) ≤ n`. No `eps`/`tau`
//!    DIVISION is performed: the caller supplies the two half-budget hypotheses
//!    directly as `Rat.le` facts, so the assembly is pure `Rat` order chaining.
//!
//! ## Honest scoping of `friedgut_l2_core`'s hypotheses
//!
//! The hypotheses are exactly the two band budgets plus the LOW-band side
//! conditions — the SAME explicit-witness data Friedgut needs (a junta `J`, a
//! degree cutoff `d`, a threshold `dr²`). The `Exists J` packaging (`|J|` bound +
//! mass bound) is assembled in the retirement step (`friedgut_boolean`), where
//! `J := the threshold set`, `|J| ≤ 2^{BUDGET e}` via `influence_threshold_card_le`,
//! and the mass bound is THIS `friedgut_l2_core`. See the retirement in
//! `fourier_boolean_theorems.rs`.
//!
//! NO `sorry` / `add_decl_unchecked` / `add_decl_structural` / `native_decide` /
//! `unsafe` / `Real`. No axiom added or removed by these bricks. Idempotent.
//! Gated behind `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the L2-core assembly. Carrier spellings byte-match the
/// banked LOW band (`mass_x_fn`), the high-degree mass brick, and the masked
/// toolkit.
struct L2Consts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_ble: Expr,
    bool_true: Expr,
    bool_false: Expr,
    rat_zero: Expr,
    rat_one: Expr,
    rat_add: Expr,
    rat_mul: Expr,
    rat_of_nat: Expr,
    rat_mk: Expr,
    int_of_nat: Expr,
    pow_nat: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fin: Expr,
    fourier: Expr,
    subset_sum: Expr,
    ind: Expr,
    set_size_nat: Expr,
    not_subset_mask: Expr,
    influence: Expr,
    total_influence: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    l0: Level,
    l1: Level,
}

impl L2Consts {
    fn new() -> Self {
        let l0 = Level::zero();
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_ble: k("Nat.ble"),
            bool_true: k("Bool.true"),
            bool_false: k("Bool.false"),
            rat_zero: k("Rat.zero"),
            rat_one: k("Rat.one"),
            rat_add: k("Rat.add"),
            rat_mul: k("Rat.mul"),
            rat_of_nat: k("Rat.ofNat"),
            rat_mk: k("Rat.mk"),
            int_of_nat: k("Int.ofNat"),
            pow_nat: k("Rat.powNat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fin: k("Fin"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            ind: k("BoolAnalysis.ind"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            not_subset_mask: k("BoolAnalysis.notSubsetMask"),
            influence: k("BoolAnalysis.Influence"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: k("instLERat"),
            l0,
            l1,
        }
    }

    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn nat_one(&self) -> Expr {
        self.succ(self.nat_zero.clone())
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
    /// `9^d := powNat (Rat.ofNat 9) d` (byte-match the LOW band's `pow9`).
    fn pow9(&self, d: &Expr) -> Expr {
        Expr::apps(
            self.pow_nat.clone(),
            [
                Expr::app(self.rat_of_nat.clone(), self.nat_lit(9)),
                d.clone(),
            ],
        )
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
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn not_subset_mask_of(&self, n: &Expr, s: &Expr, j: &Expr) -> Expr {
        Expr::apps(
            self.not_subset_mask.clone(),
            [n.clone(), s.clone(), j.clone()],
        )
    }
    /// `low_bit S := Nat.ble |S| d` — `|S| ≤ d` (byte-match the LOW band).
    fn low_bit(&self, n: &Expr, d: &Expr, s: &Expr) -> Expr {
        self.ble(self.set_size_nat_of(n, s), d.clone())
    }
    /// `high_bit S := Nat.ble (d+1) |S|` — `|S| ≥ d+1` (byte-match high_degree's
    /// mask, whose `knat := Nat.succ d`).
    fn high_bit(&self, n: &Expr, d: &Expr, s: &Expr) -> Expr {
        self.ble(self.succ(d.clone()), self.set_size_nat_of(n, s))
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    /// `f̂(S)·f̂(S)`.
    fn x_sq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
    }
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
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
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b],
        )
    }
    fn eq_bool(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.l1.clone()]),
            [self.bool_.clone(), a, b],
        )
    }
    fn refl_rat(&self, a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.l1.clone()]),
            [self.rat.clone(), a],
        )
    }
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    fn trans_rat(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.l1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }
    fn trans_le(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            [a, b, cc, h1, h2],
        )
    }
    /// `congrArg.{1,1} A B a b f h : f a = f b`.
    fn congr_arg(&self, dom: Expr, cod: Expr, a: Expr, b: Expr, f: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.l1.clone(), self.l1.clone()],
            ),
            [dom, cod, a, b, f, h],
        )
    }
}

// ────────────────── integrand spellings (byte-match the banked bricks) ─────────

/// `fun S => ind(notSubsetMask n S J)·(f̂·f̂)` — the masked-mass integrand (the
/// conclusion's LHS integrand for `friedgut_l2_core`).
fn full_fn(c: &L2Consts, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, j: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let r = c.ind_of(c.not_subset_mask_of(n, &s, j));
    let body = c.mul(r, c.x_sq(n, f, &s));
    b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// `fun S => ind(notSubsetMask)·(ind(ble |S| d)·(f̂·f̂))` — BYTE-IDENTICAL to the
/// banked LOW band's `mass_x_fn`.
fn low_fn(c: &L2Consts, parent: &EnvDeclBuilder, n: &Expr, d: &Expr, f: &Expr, j: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let r = c.ind_of(c.not_subset_mask_of(n, &s, j));
    let p = c.ind_of(c.low_bit(n, d, &s));
    let body = c.mul(r, c.mul(p, c.x_sq(n, f, &s)));
    b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// `fun S => ind(notSubsetMask)·(ind(ble (d+1) |S|)·(f̂·f̂))` — the HIGH band.
fn high_fn(c: &L2Consts, parent: &EnvDeclBuilder, n: &Expr, d: &Expr, f: &Expr, j: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let r = c.ind_of(c.not_subset_mask_of(n, &s, j));
    let p = c.ind_of(c.high_bit(n, d, &s));
    let body = c.mul(r, c.mul(p, c.x_sq(n, f, &s)));
    b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// `fun S => ind(ble (d+1) |S|)·(f̂·f̂)` — BYTE-IDENTICAL to high_degree's
/// `mask_fn` at `knat := d+1`: the full (un-masked-by-J) high-degree mass
/// `M_{≥d+1}` integrand.
fn highmass_fn(c: &L2Consts, parent: &EnvDeclBuilder, n: &Expr, d: &Expr, f: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let p = c.ind_of(c.high_bit(n, d, &s));
    let body = c.mul(p, c.x_sq(n, f, &s));
    b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

// ────────────────── BRICK 1: subsetSum_add (Fin.sum_add lifted) ────────────────

/// `fun S => Rat.add (G S) (H S)` — the pointwise sum integrand.
fn add_fn(c: &L2Consts, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, h: &Expr) -> Expr {
    let mut b = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let body = c.add(
        Expr::app(g.clone(), s.clone()),
        Expr::app(h.clone(), s.clone()),
    );
    b.finish_child(b.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// `fun (j : Fin (2^n)) => G (hcDecode n j)` — the `Fin.sum` summand of
/// `subsetSum n G` (subsetSum δ-unfolds to this `Fin.sum`).
fn decoded_fn(c: &L2Consts, parent: &EnvDeclBuilder, n: &Expr, g: &Expr) -> Expr {
    let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
    let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
    let two = c.nat_lit(2);
    let pow2 = Expr::apps(nat_pow, [two, n.clone()]);
    let mut b = EnvDeclBuilder::child_of(parent);
    let fin_pow = Expr::app(c.fin.clone(), pow2);
    let (j_id, j) = b.fresh_local(fin_pow.clone());
    let decoded = Expr::apps(hc_decode, [n.clone(), j]);
    let body = Expr::app(g.clone(), decoded);
    b.finish_child(b.mk_lam(j_id, BinderInfo::Default, fin_pow, body))
}

impl Environment {
    /// `BoolAnalysis.subsetSum_add : ∀ (n) (G H : HCPoint n → Rat),
    ///   subsetSum n (fun S => G S + H S) = subsetSum n G + subsetSum n H`.
    ///
    /// `subsetSum`-level additivity, proved by `Fin.sum_add` at the decoded
    /// integrands (both sides δ-unfold to the matching `Fin.sum`). Kernel-checked,
    /// `Constructive`, empty admitted-axiom closure. Idempotent. Mirrors the
    /// banked `subsetSum_smul`.
    pub fn register_subset_sum_add(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_add");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_foundations()?;
        self.register_subset_sum()?;
        self.init_fin_sum()?;
        self.register_fin_sum_add_theorem()?;

        let c = L2Consts::new();
        let g_ty = |b: &EnvDeclBuilder, n: &Expr| c.hcpoint_to_rat(n);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let gt = g_ty(&b, &n);
            let (g_id, g) = b.fresh_local(gt.clone());
            let (h_id, h) = b.fresh_local(gt.clone());
            let lhs = c.ssum(&n, add_fn(&c, &b, &n, &g, &h));
            let rhs = c.add(c.ssum(&n, g.clone()), c.ssum(&n, h.clone()));
            let concl = c.eq_rat(lhs, rhs);
            let e = b.mk_pi(h_id, BinderInfo::Default, gt.clone(), concl);
            let e = b.mk_pi(g_id, BinderInfo::Default, gt, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // value: fun n G H => Fin.sum_add (2^n) (j => G (hcDecode n j))
        //                                      (j => H (hcDecode n j)).
        // The conclusion δ-unfolds (subsetSum reducible) to
        //   Fin.sum (2^n) (j => G(dec j) + H(dec j)) = Fin.sum (2^n) (G∘dec) + Fin.sum (2^n) (H∘dec),
        // which is exactly Fin.sum_add's conclusion at the decoded integrands.
        let value = {
            let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
            let fin_sum_add = Expr::const_(Name::from_string("Fin.sum_add"), vec![]);
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let gt = g_ty(&b, &n);
            let (g_id, g) = b.fresh_local(gt.clone());
            let (h_id, h) = b.fresh_local(gt.clone());
            let pow2 = Expr::apps(nat_pow, [c.nat_lit(2), n.clone()]);
            let g_dec = decoded_fn(&c, &b, &n, &g);
            let h_dec = decoded_fn(&c, &b, &n, &h);
            let proof = Expr::apps(fin_sum_add, [pow2, g_dec, h_dec]);
            let e = b.mk_lam(h_id, BinderInfo::Default, gt.clone(), proof);
            let e = b.mk_lam(g_id, BinderInfo::Default, gt, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

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

// ───────── BRICK 2: band_split_term + friedgut_band_split ──────────────────────

impl L2Consts {
    fn refl_bool(&self, a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![self.l1.clone()]),
            [self.bool_.clone(), a],
        )
    }
    fn symm_bool(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.l1.clone()]),
            [self.bool_.clone(), a, b, h],
        )
    }
    fn trans_bool(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.l1.clone()]),
            [self.bool_.clone(), a, b, cc, h1, h2],
        )
    }
    fn bnot(&self, a: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_string("Bool.not"), vec![]), a)
    }
    /// `Nat.not_ble_succ_eq_ble d m : not(ble (d+1) m) = ble m d`.
    fn not_ble_succ(&self, d: &Expr, m: &Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Nat.not_ble_succ_eq_ble"), vec![]),
            [d.clone(), m.clone()],
        )
    }
    /// `congrArg (fun (b : Bool) => Bool.not b) h : not a = not b`.
    fn congr_not(&self, parent: &EnvDeclBuilder, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.bool_.clone());
            let body = self.bnot(z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.bool_.clone(), body))
        };
        self.congr_arg(self.bool_.clone(), self.bool_.clone(), a, b, f, h)
    }
    /// `congrArg (fun (bit : Bool) => ind bit · w) h : ind a·w = ind b·w`.
    fn congr_indmul(&self, parent: &EnvDeclBuilder, w: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.bool_.clone());
            let body = self.mul(self.ind_of(z), w.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.bool_.clone(), body))
        };
        self.congr_arg(self.bool_.clone(), self.rat.clone(), a, b, f, h)
    }
    /// `Rat.one_mul a : 1·a = a`.
    fn one_mul(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
            a.clone(),
        )
    }
    /// `Rat.zero_mul a : 0·a = 0`.
    fn zero_mul(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.zero_mul"), vec![]),
            a.clone(),
        )
    }
    /// `Rat.add_zero a : a + 0 = a`.
    fn add_zero(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.add_zero"), vec![]),
            a.clone(),
        )
    }
    /// `Rat.zero_add a : 0 + a = a`.
    fn zero_add(&self, a: &Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Rat.zero_add"), vec![]),
            a.clone(),
        )
    }
    /// `congrArg (fun (z : Rat) => Rat.add z r) h : (a + r) = (b + r)`.
    fn congr_add_l(&self, parent: &EnvDeclBuilder, r: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.add(z, r.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr_arg(self.rat.clone(), self.rat.clone(), a, b, f, h)
    }
    /// `congrArg (fun (z : Rat) => Rat.add l z) h : (l + a) = (l + b)`.
    fn congr_add_r(&self, parent: &EnvDeclBuilder, l: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.add(l.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr_arg(self.rat.clone(), self.rat.clone(), a, b, f, h)
    }
    /// `Rat.lt a b`.
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.lt"), vec![]), [a, b])
    }
    /// `Rat.add_le_add a b c d (h1: a≤b)(h2: c≤d) : (a+c) ≤ (b+d)`.
    fn add_le_add(&self, a: Expr, b: Expr, cc: Expr, dd: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.add_le_add"), vec![]),
            [a, b, cc, dd, h1, h2],
        )
    }
}

/// `band_split_term` type: `∀ (d m : Nat) (w : Rat),
///   Eq Rat w (Rat.add (ind(ble m d)·w) (ind(ble (d+1) m)·w))`.
fn bst_type(c: &L2Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (w_id, w) = b.fresh_local(c.rat.clone());
    let lo = c.mul(c.ind_of(c.ble(m.clone(), d.clone())), w.clone());
    let hi = c.mul(c.ind_of(c.ble(c.succ(d.clone()), m.clone())), w.clone());
    let concl = c.eq_rat(w.clone(), c.add(lo, hi));
    let e = b.mk_pi(w_id, BinderInfo::Default, c.rat.clone(), concl);
    let e = b.mk_pi(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e))
}

/// `band_split_term` value — `Bool.casesOn (ble (d+1) m)` eq-threaded.
fn bst_value(c: &L2Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let (m_id, m) = b.fresh_local(c.nat.clone());
    let (w_id, w) = b.fresh_local(c.rat.clone());

    let lo_bit = c.ble(m.clone(), d.clone()); // ble m d
    let hi = c.ble(c.succ(d.clone()), m.clone()); // ble (d+1) m
    let lo_mul = c.mul(c.ind_of(lo_bit.clone()), w.clone()); // ind(ble m d)·w
                                                             // compl : not(ble (d+1) m) = ble m d ; symm : ble m d = not(ble (d+1) m).
    let compl = c.not_ble_succ(&d, &m);
    let not_hi = c.bnot(hi.clone());
    let lo_eq_nothi = c.symm_bool(not_hi.clone(), lo_bit.clone(), compl); // ble m d = not(ble(d+1)m)

    // goal_at(x) := Eq Rat w (add (ind(ble m d)·w) (ind x · w)).
    let goal_at = |x: Expr| {
        let hi_mul = c.mul(c.ind_of(x), w.clone());
        c.eq_rat(w.clone(), c.add(lo_mul.clone(), hi_mul))
    };

    // motive : fun (x : Bool) => (ble (d+1) m = x) → goal_at(x).
    let motive = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let (x_id, x) = e.fresh_local(c.bool_.clone());
        let prem = c.eq_bool(hi.clone(), x.clone());
        let body = Expr::pi(BinderInfo::Default, prem, goal_at(x.clone()));
        e.finish_child(e.mk_lam(x_id, BinderInfo::Default, c.bool_.clone(), body))
    };

    // Common: ind false·w = 0, ind true·w = w. (def-eq via ind false ≡ 0, ind true ≡ 1.)
    let zero_w = c.mul(c.rat_zero.clone(), w.clone());
    let one_w = c.mul(c.rat_one.clone(), w.clone());
    let indf_w = c.mul(c.ind_of(c.bool_false.clone()), w.clone()); // ≡ 0·w
    let indt_w = c.mul(c.ind_of(c.bool_true.clone()), w.clone()); // ≡ 1·w

    // false branch : (ble (d+1) m = false) → goal_at(false).
    //   ble m d = not(ble(d+1)m) = not false = true.
    //   ⟹ ind(ble m d)·w = ind true·w = 1·w = w.
    //   ind false·w = 0·w = 0. RHS = w + 0. goal w = w + 0 = symm(add_zero w).
    let false_branch = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let prem = c.eq_bool(hi.clone(), c.bool_false.clone());
        let (h_id, h) = e.fresh_local(prem.clone());
        // not(ble(d+1)m) = not false   (congr_not h).
        let not_h = c.congr_not(&e, hi.clone(), c.bool_false.clone(), h.clone());
        // ble m d = not false   (trans (ble m d = not hi) (not hi = not false)).
        let lo_eq_notfalse = c.trans_bool(
            lo_bit.clone(),
            not_hi.clone(),
            c.bnot(c.bool_false.clone()),
            lo_eq_nothi.clone(),
            not_h,
        );
        // ind(ble m d)·w = ind(not false)·w   (congr_indmul).
        //   ind(not false) ≡ ind true ≡ 1, so ind(not false)·w ≡ 1·w def-eq.
        let indlo_w_eq = c.congr_indmul(
            &e,
            &w,
            lo_bit.clone(),
            c.bnot(c.bool_false.clone()),
            lo_eq_notfalse,
        );
        // 1·w = w.
        let onew_eq_w = c.one_mul(&w);
        // ind(ble m d)·w = 1·w (def-eq RHS), then = w. Chain via trans on the
        // typed endpoints (ind(not false)·w is def-eq to 1·w = one_w).
        let lo_eq_w = c.trans_rat(
            lo_mul.clone(),
            one_w.clone(),
            w.clone(),
            indlo_w_eq,
            onew_eq_w,
        );
        // RHS = lo_mul + indf_w. Rewrite lo_mul → w (congr_add_l), indf_w ≡ 0·w → 0.
        //   step1 : lo_mul + indf_w = w + indf_w  (congr_add_l (symm? no: lo_eq_w forward)).
        //   We need (w + 0) form. Build: w = w + 0 (symm add_zero), then w+0 = lo_mul+indf_w.
        // Forward: lo_mul + indf_w
        //   =[congr_add_l lo_eq_w] w + indf_w
        //   =[congr_add_r (zero_mul w : indf_w ≡ 0·w = 0)] w + 0
        //   =[add_zero w] w.
        // Then symm gives w = lo_mul + indf_w.
        let zmul = c.zero_mul(&w); // 0·w = 0  (indf_w ≡ 0·w def-eq)
        let w_plus_indf = c.add(w.clone(), indf_w.clone());
        let w_plus_zero = c.add(w.clone(), c.rat_zero.clone());
        let rhs = c.add(lo_mul.clone(), indf_w.clone());
        // s1 : rhs = w + indf_w.
        let s1 = c.congr_add_l(&e, &indf_w, lo_mul.clone(), w.clone(), lo_eq_w);
        // s2 : w + indf_w = w + 0.   (congr_add_r (indf_w ≡ 0·w; zmul : 0·w = 0)).
        let s2 = c.congr_add_r(&e, &w, indf_w.clone(), c.rat_zero.clone(), zmul);
        // s3 : w + 0 = w.
        let s3 = c.add_zero(&w);
        // chain : rhs = w.
        let c12 = c.trans_rat(
            rhs.clone(),
            w_plus_indf.clone(),
            w_plus_zero.clone(),
            s1,
            s2,
        );
        let rhs_eq_w = c.trans_rat(rhs.clone(), w_plus_zero, w.clone(), c12, s3);
        // body : w = rhs   (symm).
        let body = c.symm_rat(rhs, w.clone(), rhs_eq_w);
        e.finish_child(e.mk_lam(h_id, BinderInfo::Default, prem, body))
    };

    // true branch : (ble (d+1) m = true) → goal_at(true).
    //   ble m d = not true = false ⟹ ind(ble m d)·w = ind false·w = 0·w = 0.
    //   ind true·w = 1·w = w. RHS = 0 + w. goal w = 0 + w = symm(zero_add w).
    let true_branch = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let prem = c.eq_bool(hi.clone(), c.bool_true.clone());
        let (h_id, h) = e.fresh_local(prem.clone());
        let not_h = c.congr_not(&e, hi.clone(), c.bool_true.clone(), h.clone());
        let lo_eq_nottrue = c.trans_bool(
            lo_bit.clone(),
            not_hi.clone(),
            c.bnot(c.bool_true.clone()),
            lo_eq_nothi.clone(),
            not_h,
        );
        // ind(ble m d)·w = ind(not true)·w ≡ ind false·w ≡ 0·w.
        let indlo_w_eq = c.congr_indmul(
            &e,
            &w,
            lo_bit.clone(),
            c.bnot(c.bool_true.clone()),
            lo_eq_nottrue,
        );
        // 0·w = 0.
        let zmul = c.zero_mul(&w);
        let lo_eq_zero = c.trans_rat(
            lo_mul.clone(),
            zero_w.clone(),
            c.rat_zero.clone(),
            indlo_w_eq,
            zmul,
        );
        // RHS = lo_mul + indt_w. indt_w ≡ 1·w. one_mul : 1·w = w.
        let onew = c.one_mul(&w);
        let zero_plus_indt = c.add(c.rat_zero.clone(), indt_w.clone());
        let zero_plus_w = c.add(c.rat_zero.clone(), w.clone());
        let rhs = c.add(lo_mul.clone(), indt_w.clone());
        // s1 : rhs = 0 + indt_w   (congr_add_l lo_eq_zero).
        let s1 = c.congr_add_l(&e, &indt_w, lo_mul.clone(), c.rat_zero.clone(), lo_eq_zero);
        // s2 : 0 + indt_w = 0 + w   (congr_add_r onew, indt_w ≡ 1·w).
        let s2 = c.congr_add_r(&e, &c.rat_zero.clone(), indt_w.clone(), w.clone(), onew);
        // s3 : 0 + w = w.
        let s3 = c.zero_add(&w);
        let c12 = c.trans_rat(
            rhs.clone(),
            zero_plus_indt.clone(),
            zero_plus_w.clone(),
            s1,
            s2,
        );
        let rhs_eq_w = c.trans_rat(rhs.clone(), zero_plus_w, w.clone(), c12, s3);
        let body = c.symm_rat(rhs, w.clone(), rhs_eq_w);
        e.finish_child(e.mk_lam(h_id, BinderInfo::Default, prem, body))
    };

    let bool_cases = Expr::const_(Name::from_string("Bool.casesOn"), vec![c.l0.clone()]);
    let refl_hi = c.refl_bool(hi.clone());
    let cases = Expr::apps(
        bool_cases,
        [motive, hi.clone(), false_branch, true_branch, refl_hi],
    );
    let e = b.mk_lam(w_id, BinderInfo::Default, c.rat.clone(), cases);
    let e = b.mk_lam(m_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// `BoolAnalysis.band_split_term : ∀ (d m : Nat) (w : Rat),
    ///   Eq Rat w (Rat.add (ind(ble m d)·w) (ind(ble (d+1) m)·w))`.
    ///
    /// The per-degree band-complement identity: a weight `w` splits into its
    /// low-band (`|S| ≤ d`) and high-band (`|S| ≥ d+1`) shares, because the masks
    /// are Boolean complements (`Nat.not_ble_succ_eq_ble`). `Bool.casesOn` on
    /// `ble (d+1) m`. Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_band_split_term(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.band_split_term");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_nat()?;
        self.init_bool()?;
        self.init_rat()?;
        self.init_rat_field_inst()?; // Rat.one_mul, zero_mul, add_zero, zero_add
        self.init_boolean_analysis()?; // BoolAnalysis.ind
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_nat_not_ble_succ_eq_ble()?;

        let c = L2Consts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: bst_type(&c),
            value: bst_value(&c),
        })
    }

    /// `BoolAnalysis.friedgut_band_split : ∀ (n d : Nat) (f : BoolFn n) (J : HCPoint n),
    ///   Eq Rat (subsetSum n (fun S => ind(notSubset)·(f̂·f̂)))
    ///          (Rat.add (subsetSum n LOW) (subsetSum n HIGH))`
    ///
    /// where `LOW S := ind(notSubset)·(ind(ble |S| d)·(f̂·f̂))` (byte-identical to
    /// the banked LOW band) and `HIGH S := ind(notSubset)·(ind(ble (d+1) |S|)·(f̂·f̂))`.
    /// Proved by `subsetSum_congr` over the per-`S` masked band-complement
    /// (`band_split_term` + `Rat.left_distrib`), then `subsetSum_add`.
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_friedgut_band_split(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_band_split");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_rat_field_inst()?; // Rat.left_distrib
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_band_split_term()?;
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_add()?;
        self.register_not_subset_mask()?;
        self.register_set_size_nat()?;

        let c = L2Consts::new();
        let left_distrib = Expr::const_(Name::from_string("Rat.left_distrib"), vec![]);
        let band_split_term =
            Expr::const_(Name::from_string("BoolAnalysis.band_split_term"), vec![]);
        let subset_sum_congr =
            Expr::const_(Name::from_string("BoolAnalysis.subsetSum_congr"), vec![]);
        let subset_sum_add = Expr::const_(Name::from_string("BoolAnalysis.subsetSum_add"), vec![]);

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let bf_ty = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bf_ty.clone());
            let hcp = c.hcpoint_of(&n);
            let (j_id, j) = b.fresh_local(hcp.clone());

            let full = full_fn(&c, &b, &n, &f, &j);
            let low = low_fn(&c, &b, &n, &d, &f, &j);
            let high = high_fn(&c, &b, &n, &d, &f, &j);
            let ss_full = c.ssum(&n, full.clone());
            let ss_low = c.ssum(&n, low.clone());
            let ss_high = c.ssum(&n, high.clone());
            let rhs = c.add(ss_low.clone(), ss_high.clone());

            if !for_value {
                let concl = c.eq_rat(ss_full, rhs);
                let e = b.mk_pi(j_id, BinderInfo::Default, hcp, concl);
                let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
                let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
                return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
            }

            // per_s : ∀ S, full S = low S + high S.
            //   full S ≡ R·w ; goal R·w = R·(ind(ble m d)·w) + R·(ind(ble(d+1)m)·w).
            //   from band_split_term d m w : w = ind(ble m d)·w + ind(ble(d+1)m)·w,
            //     congrArg (R··) : R·w = R·(ind(..d..)·w + ind(..d+1..)·w),
            //     left_distrib R A B : R·(A+B) = R·A + R·B  (trans).
            let per_s = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let (s_id, s) = e.fresh_local(hcp.clone());
                let rr = c.ind_of(c.not_subset_mask_of(&n, &s, &j)); // R
                let m = c.set_size_nat_of(&n, &s); // |S|
                let w = c.x_sq(&n, &f, &s); // f̂·f̂
                let lo_inner = c.mul(c.ind_of(c.ble(m.clone(), d.clone())), w.clone()); // ind(ble m d)·w
                let hi_inner = c.mul(c.ind_of(c.ble(c.succ(d.clone()), m.clone())), w.clone()); // ind(ble(d+1)m)·w
                let rw = c.mul(rr.clone(), w.clone()); // R·w = full S
                let sum_inner = c.add(lo_inner.clone(), hi_inner.clone());
                let r_sum = c.mul(rr.clone(), sum_inner.clone()); // R·(A+B)
                let r_lo = c.mul(rr.clone(), lo_inner.clone()); // R·A = low S
                let r_hi = c.mul(rr.clone(), hi_inner.clone()); // R·B = high S
                let r_lo_plus_hi = c.add(r_lo.clone(), r_hi.clone());

                // bst : w = A + B.
                let bst = Expr::apps(band_split_term.clone(), [d.clone(), m.clone(), w.clone()]);
                // congr (R··) bst : R·w = R·(A+B).
                let congr_r = {
                    let f2 = {
                        let mut g = EnvDeclBuilder::child_of(&e);
                        let (z_id, z) = g.fresh_local(c.rat.clone());
                        let body = c.mul(rr.clone(), z);
                        g.finish_child(g.mk_lam(z_id, BinderInfo::Default, c.rat.clone(), body))
                    };
                    c.congr_arg(
                        c.rat.clone(),
                        c.rat.clone(),
                        w.clone(),
                        sum_inner.clone(),
                        f2,
                        bst,
                    )
                };
                // ld : R·(A+B) = R·A + R·B.
                let ld = Expr::apps(
                    left_distrib.clone(),
                    [rr.clone(), lo_inner.clone(), hi_inner.clone()],
                );
                // body : R·w = R·A + R·B  (trans).
                let body =
                    c.trans_rat(rw.clone(), r_sum.clone(), r_lo_plus_hi.clone(), congr_r, ld);
                e.finish_child(e.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
            };

            // step1 : subsetSum n full = subsetSum n (fun S => low S + high S).
            //   subsetSum_congr n full (add_fn low high) per_s.
            //   (add_fn low high) ≡ fun S => low S + high S, which per_s matches.
            let mid = add_fn(&c, &b, &n, &low, &high);
            let ss_mid = c.ssum(&n, mid.clone());
            let step1 = Expr::apps(
                subset_sum_congr.clone(),
                [n.clone(), full.clone(), mid.clone(), per_s],
            );
            // step2 : subsetSum n (fun S => low S + high S) = subsetSum n low + subsetSum n high.
            //   subsetSum_add n low high.
            let step2 = Expr::apps(
                subset_sum_add.clone(),
                [n.clone(), low.clone(), high.clone()],
            );
            let body = c.trans_rat(ss_full, ss_mid, rhs, step1, step2);

            let e = b.mk_lam(j_id, BinderInfo::Default, hcp, body);
            let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, e);
            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
        };

        let ty = mk(false);
        let value = mk(true);
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

    /// `BoolAnalysis.friedgut_high_mask_drop :
    ///   ∀ (n d : Nat) (f : BoolFn n) (J : HCPoint n),
    ///     Rat.le (subsetSum n HIGH) (subsetSum n (fun S => ind(ble (d+1) |S|)·(f̂·f̂)))`
    ///
    /// where `HIGH S := ind(notSubset)·(ind(ble (d+1) |S|)·(f̂·f̂))`. Drops the
    /// `ind(notSubset) ≤ 1` factor: per-`S` `ind(notSubset)·X ≤ 1·X = X` with
    /// `X := ind(ble (d+1) |S|)·(f̂·f̂) ≥ 0`, lifted by `subsetSum_le_of_pointwise`.
    /// The RHS is the full high-degree mass `M_{≥d+1}` (BYTE-IDENTICAL to
    /// `high_degree_mass_le`'s masked integrand). Kernel-checked, `Constructive`,
    /// empty closure. Idempotent.
    pub fn register_friedgut_high_mask_drop(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_high_mask_drop");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        self.init_boolean_analysis_order_toolkit()?; // mul_le_right, sq_nonneg, mul_nonneg
        self.init_rat_field_inst()?; // Rat.one_mul
        self.init_boolean_analysis_kkl_hcdual()?; // ind_nonneg
        self.init_boolean_analysis_friedgut_masked_finsum()?; // ind_le_one
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_subset_sum_le_of_pointwise()?;
        self.register_not_subset_mask()?;
        self.register_set_size_nat()?;

        let c = L2Consts::new();
        let mul_le_right =
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_right"), vec![]);
        let mul_nonneg = Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]);
        let sq_nonneg = Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]);
        let ind_nonneg = Expr::const_(Name::from_string("BoolAnalysis.ind_nonneg"), vec![]);
        let ind_le_one = Expr::const_(Name::from_string("BoolAnalysis.ind_le_one"), vec![]);
        let subset_sum_le = Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_le_of_pointwise"),
            vec![],
        );

        let mk = |for_value: bool| -> Expr {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let bf_ty = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bf_ty.clone());
            let hcp = c.hcpoint_of(&n);
            let (j_id, j) = b.fresh_local(hcp.clone());

            let high = high_fn(&c, &b, &n, &d, &f, &j);
            let highmass = highmass_fn(&c, &b, &n, &d, &f);
            let ss_high = c.ssum(&n, high.clone());
            let ss_highmass = c.ssum(&n, highmass.clone());

            if !for_value {
                let concl = c.le(ss_high, ss_highmass);
                let e = b.mk_pi(j_id, BinderInfo::Default, hcp, concl);
                let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
                let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
                return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
            }

            // per_s : ∀ S, high S ≤ highmass S.
            //   high S ≡ R·X, highmass S ≡ X, X := ind(ble (d+1) |S|)·(f̂·f̂).
            //   X ≥ 0 : mul_nonneg (ind_nonneg ..) (sq_nonneg f̂).
            //   R ≤ 1 : ind_le_one (notSubset).
            //   mul_le_right X R 1 (ind_le_one R) (X≥0) : R·X ≤ 1·X.
            //   one_mul X : 1·X = X ⟹ rewrite RHS to X.
            let per_s = {
                let mut e = EnvDeclBuilder::child_of(&b);
                let (s_id, s) = e.fresh_local(hcp.clone());
                let r_bit = c.not_subset_mask_of(&n, &s, &j);
                let rr = c.ind_of(r_bit.clone()); // R
                let hbit = c.high_bit(&n, &d, &s);
                let coeff = c.fourier_of(&n, &f, &s);
                let sq = c.mul(coeff.clone(), coeff.clone()); // f̂·f̂
                let xx = c.mul(c.ind_of(hbit.clone()), sq.clone()); // X
                let rx = c.mul(rr.clone(), xx.clone()); // R·X = high S
                let one_x = c.mul(c.rat_one.clone(), xx.clone()); // 1·X

                // X ≥ 0.
                let x_nonneg = Expr::apps(
                    mul_nonneg.clone(),
                    [
                        c.ind_of(hbit.clone()),
                        sq.clone(),
                        Expr::app(ind_nonneg.clone(), hbit.clone()),
                        Expr::app(sq_nonneg.clone(), coeff.clone()),
                    ],
                );
                // R ≤ 1.
                let r_le_one = Expr::app(ind_le_one.clone(), r_bit.clone());
                // R·X ≤ 1·X.
                let bound = Expr::apps(
                    mul_le_right.clone(),
                    [
                        xx.clone(),
                        rr.clone(),
                        c.rat_one.clone(),
                        r_le_one,
                        x_nonneg,
                    ],
                );
                // 1·X = X.
                let one_mul_x = c.one_mul(&xx);
                // rewrite : R·X ≤ X. subst (motive t => R·X ≤ t) along one_mul_x (1·X → X).
                let motive = {
                    let mut g = EnvDeclBuilder::child_of(&e);
                    let (t_id, t) = g.fresh_local(c.rat.clone());
                    let body = c.le(rx.clone(), t);
                    g.finish_child(g.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
                };
                let body = c.subst_rat(motive, one_x, xx.clone(), one_mul_x, bound);
                e.finish_child(e.mk_lam(s_id, BinderInfo::Default, hcp.clone(), body))
            };

            // subsetSum_le_of_pointwise n high highmass per_s.
            let body = Expr::apps(
                subset_sum_le.clone(),
                [n.clone(), high.clone(), highmass.clone(), per_s],
            );
            let e = b.mk_lam(j_id, BinderInfo::Default, hcp, body);
            let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, e);
            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
        };

        let ty = mk(false);
        let value = mk(true);
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

// ─────────────────────── BRICK 4: friedgut_l2_core (assembly) ──────────────────

/// Build the `friedgut_l2_core` type/value. The shared LOW-band hypothesis
/// builders mirror `restricted_mass_type` byte-for-byte (so the banked LOW band
/// applies directly), plus the two band budgets `eL`, `eH` and the additive
/// `eL+eH ≤ eps`.
fn l2_core_build(c: &L2Consts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let bf_ty = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bf_ty.clone());
    let hcp = c.hcpoint_of(&n);
    let (j_id, j) = b.fresh_local(hcp.clone());
    let (dr_id, dr) = b.fresh_local(c.rat.clone());
    let (el_id, el) = b.fresh_local(c.rat.clone());
    let (eh_id, eh) = b.fresh_local(c.rat.clone());
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let dd = c.mul(dr.clone(), dr.clone()); // dr·dr = dr²
                                            // `1 : Rat` byte-match the LOW band's `one_rat := mk(ofNat 1) 1`.
    let one_lit = Expr::apps(
        c.rat_mk.clone(),
        [Expr::app(c.int_of_nat.clone(), c.nat_one()), c.nat_one()],
    );

    // LOW-band hypotheses (byte-match restricted_mass_type).
    let hd_ty = c.le(c.rat_zero.clone(), dr.clone()); // 0 ≤ dr
    let hdd0_ty = c.le(c.rat_zero.clone(), dd.clone()); // 0 ≤ dr²
    let hdd1_ty = c.lt(dd.clone(), one_lit.clone()); // dr² < 1
    let h0_ty = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = e.fresh_local(fin_n.clone());
        let body = c.le(c.rat_zero.clone(), c.influence_of(&n, &f, &i));
        e.finish_child(e.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };
    let h1m_ty = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = e.fresh_local(fin_n.clone());
        let prem = c.eq_bool(c.bnot(Expr::app(j.clone(), i.clone())), c.bool_true.clone());
        let concl = c.le(c.influence_of(&n, &f, &i), dd.clone());
        let body = Expr::pi(BinderInfo::Default, prem, concl);
        e.finish_child(e.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };

    // band terms.
    let full = full_fn(c, &b, &n, &f, &j);
    let low = low_fn(c, &b, &n, &d, &f, &j);
    let high = high_fn(c, &b, &n, &d, &f, &j);
    let highmass = highmass_fn(c, &b, &n, &d, &f);
    let ss_full = c.ssum(&n, full.clone());
    let ss_low = c.ssum(&n, low.clone());
    let ss_high = c.ssum(&n, high.clone());
    let ss_highmass = c.ssum(&n, highmass.clone());
    let infl = c.total_influence_of(&n, &f);
    let dr_i = c.mul(dr.clone(), infl.clone()); // dr·I
    let q9_dri = c.mul(c.pow9(&d), dr_i.clone()); // 9^d·(dr·I) = LOW band RHS

    // budgets.
    let hlow_ty = c.le(q9_dri.clone(), el.clone()); // 9^d·(dr·I) ≤ eL
    let hhigh_ty = c.le(ss_highmass.clone(), eh.clone()); // M_{≥d+1} ≤ eH
    let el_eh = c.add(el.clone(), eh.clone());
    let hsum_ty = c.le(el_eh.clone(), eps.clone()); // eL + eH ≤ eps

    let concl = c.le(ss_full.clone(), eps.clone());

    if !for_value {
        // fresh binder ids for the hypotheses.
        let (hd_id, _) = b.fresh_local(hd_ty.clone());
        let (hdd0_id, _) = b.fresh_local(hdd0_ty.clone());
        let (hdd1_id, _) = b.fresh_local(hdd1_ty.clone());
        let (h0_id, _) = b.fresh_local(h0_ty.clone());
        let (h1m_id, _) = b.fresh_local(h1m_ty.clone());
        let (hlow_id, _) = b.fresh_local(hlow_ty.clone());
        let (hhigh_id, _) = b.fresh_local(hhigh_ty.clone());
        let (hsum_id, _) = b.fresh_local(hsum_ty.clone());

        let e = b.mk_pi(hsum_id, BinderInfo::Default, hsum_ty, concl);
        let e = b.mk_pi(hhigh_id, BinderInfo::Default, hhigh_ty, e);
        let e = b.mk_pi(hlow_id, BinderInfo::Default, hlow_ty, e);
        let e = b.mk_pi(h1m_id, BinderInfo::Default, h1m_ty, e);
        let e = b.mk_pi(h0_id, BinderInfo::Default, h0_ty, e);
        let e = b.mk_pi(hdd1_id, BinderInfo::Default, hdd1_ty, e);
        let e = b.mk_pi(hdd0_id, BinderInfo::Default, hdd0_ty, e);
        let e = b.mk_pi(hd_id, BinderInfo::Default, hd_ty, e);
        let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_pi(eh_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_pi(el_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_pi(dr_id, BinderInfo::Default, c.rat.clone(), e);
        let e = b.mk_pi(j_id, BinderInfo::Default, hcp, e);
        let e = b.mk_pi(f_id, BinderInfo::Default, bf_ty, e);
        let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
        return b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e));
    }

    // ── value ──
    let (hd_id, hd) = b.fresh_local(hd_ty.clone());
    let (hdd0_id, hdd0) = b.fresh_local(hdd0_ty.clone());
    let (hdd1_id, hdd1) = b.fresh_local(hdd1_ty.clone());
    let (h0_id, h0) = b.fresh_local(h0_ty.clone());
    let (h1m_id, h1m) = b.fresh_local(h1m_ty.clone());
    let (hlow_id, hlow) = b.fresh_local(hlow_ty.clone());
    let (hhigh_id, hhigh) = b.fresh_local(hhigh_ty.clone());
    let (hsum_id, hsum) = b.fresh_local(hsum_ty.clone());

    // (1) band split : ss_full = ss_low + ss_high.
    let split = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.friedgut_band_split"),
            vec![],
        ),
        [n.clone(), d.clone(), f.clone(), j.clone()],
    );
    // (2) LOW : ss_low ≤ 9^d·(dr·I).
    let low_le = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.friedgut_restricted_mass_le"),
            vec![],
        ),
        [
            n.clone(),
            d.clone(),
            f.clone(),
            j.clone(),
            dr.clone(),
            hd.clone(),
            hdd0.clone(),
            hdd1.clone(),
            h0.clone(),
            h1m.clone(),
        ],
    );
    // (3) HIGH mask-drop : ss_high ≤ M_{≥d+1}.
    let high_drop = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.friedgut_high_mask_drop"),
            vec![],
        ),
        [n.clone(), d.clone(), f.clone(), j.clone()],
    );

    // add_le_add: ss_low + ss_high ≤ (9^d·(dr·I)) + M_{≥d+1}.
    let sum_low_high = c.add(ss_low.clone(), ss_high.clone());
    let sum_bounds = c.add(q9_dri.clone(), ss_highmass.clone());
    let step_a = c.add_le_add(
        ss_low.clone(),
        q9_dri.clone(),
        ss_high.clone(),
        ss_highmass.clone(),
        low_le,
        high_drop,
    );
    // rewrite LHS ss_low+ss_high to ss_full via symm split: ss_full = ss_low+ss_high,
    //   subst (motive t => t ≤ sum_bounds) along (symm split) ? Use forward:
    //   split : ss_full = sum_low_high. subst (motive t => t ≤ sum_bounds)
    //     transports step_a (sum_low_high ≤ sum_bounds) backward to ss_full.
    let motive_a = {
        let mut e = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = e.fresh_local(c.rat.clone());
        let body = c.le(t.clone(), sum_bounds.clone());
        e.finish_child(e.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let split_symm = c.symm_rat(ss_full.clone(), sum_low_high.clone(), split);
    // split_symm : sum_low_high = ss_full ; subst (a := sum_low_high) (b := ss_full).
    let step_a_full = c.subst_rat(
        motive_a,
        sum_low_high.clone(),
        ss_full.clone(),
        split_symm,
        step_a,
    );
    // step_a_full : ss_full ≤ (9^d·(dr·I)) + M_{≥d+1}.

    // add_le_add: (9^d·(dr·I)) + M_{≥d+1} ≤ eL + eH.
    let step_b = c.add_le_add(
        q9_dri.clone(),
        el.clone(),
        ss_highmass.clone(),
        eh.clone(),
        hlow,
        hhigh,
    );
    // step_b : sum_bounds ≤ eL + eH.

    // chain : ss_full ≤ sum_bounds ≤ eL+eH ≤ eps.
    let chain1 = c.trans_le(
        ss_full.clone(),
        sum_bounds.clone(),
        el_eh.clone(),
        step_a_full,
        step_b,
    );
    let proof = c.trans_le(ss_full.clone(), el_eh.clone(), eps.clone(), chain1, hsum);

    let e = b.mk_lam(hsum_id, BinderInfo::Default, hsum_ty, proof);
    let e = b.mk_lam(hhigh_id, BinderInfo::Default, hhigh_ty, e);
    let e = b.mk_lam(hlow_id, BinderInfo::Default, hlow_ty, e);
    let e = b.mk_lam(h1m_id, BinderInfo::Default, h1m_ty, e);
    let e = b.mk_lam(h0_id, BinderInfo::Default, h0_ty, e);
    let e = b.mk_lam(hdd1_id, BinderInfo::Default, hdd1_ty, e);
    let e = b.mk_lam(hdd0_id, BinderInfo::Default, hdd0_ty, e);
    let e = b.mk_lam(hd_id, BinderInfo::Default, hd_ty, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(eh_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(el_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(dr_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(j_id, BinderInfo::Default, hcp, e);
    let e = b.mk_lam(f_id, BinderInfo::Default, bf_ty, e);
    let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

impl Environment {
    /// Register the four L2-core bricks and `BoolAnalysis.friedgut_l2_core`.
    /// Idempotent. No axiom added or removed.
    pub fn init_boolean_analysis_friedgut_l2_core(&mut self) -> Result<(), EnvError> {
        self.register_subset_sum_add()?;
        self.register_band_split_term()?;
        self.register_friedgut_band_split()?;
        self.register_friedgut_high_mask_drop()?;
        self.register_friedgut_l2_core()?;
        Ok(())
    }

    /// `BoolAnalysis.friedgut_l2_core :
    ///   ∀ (n d : Nat) (f : BoolFn n) (J : HCPoint n) (dr eL eH eps : Rat),
    ///     0 ≤ dr → 0 ≤ dr² → dr² < 1 →
    ///     (∀ i, 0 ≤ Inf_i) → (∀ i, ¬J i = true → Inf_i ≤ dr²) →
    ///     9^d·(dr·I) ≤ eL →                              -- LOW budget
    ///     (Σ_{|S|≥d+1} f̂²) ≤ eH →                        -- HIGH budget (M_{≥d+1})
    ///     eL + eH ≤ eps →
    ///       Σ_{S⊄J} f̂(S)² ≤ eps`
    ///
    /// The faithful O'Donnell §9.6 L2-distance mass bound: the masked Fourier
    /// mass splits (`friedgut_band_split`) into the LOW band (charged by
    /// `friedgut_restricted_mass_le` ≤ `9^d·(dr·I)` ≤ `eL`) and the HIGH band
    /// (`friedgut_high_mask_drop` ≤ `M_{≥d+1}` ≤ `eH`), and `eL+eH ≤ eps`. Pure
    /// `Rat`-order chaining (`Rat.add_le_add`, `Rat.le_trans`) — NO division.
    /// Kernel-checked, `Constructive`, empty admitted-axiom closure. Idempotent.
    pub fn register_friedgut_l2_core(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.friedgut_l2_core");
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
        // The four assembled bricks + the banked LOW band, the Rat order plumbing.
        self.register_friedgut_band_split()?;
        self.register_friedgut_high_mask_drop()?;
        self.init_boolean_analysis_friedgut_restricted_mass()?;
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.register_rat_add_le_add()?; // Rat.add_le_add

        let c = L2Consts::new();
        let ty = l2_core_build(&c, false);
        let value = l2_core_build(&c, true);
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
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_subset_sum_add_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_add()
            .expect("register_subset_sum_add");
        env.register_subset_sum_add().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.subsetSum_add");
    }

    #[test]
    fn test_band_split_term_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_band_split_term()
            .expect("register_band_split_term");
        env.register_band_split_term().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.band_split_term");
    }

    #[test]
    fn test_friedgut_band_split_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_band_split()
            .expect("register_friedgut_band_split");
        env.register_friedgut_band_split().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.friedgut_band_split");
    }

    #[test]
    fn test_friedgut_high_mask_drop_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_friedgut_high_mask_drop()
            .expect("register_friedgut_high_mask_drop");
        env.register_friedgut_high_mask_drop().expect("idempotent");
        check_constructive(&env, "BoolAnalysis.friedgut_high_mask_drop");
    }

    #[test]
    fn test_friedgut_l2_core_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_friedgut_l2_core()
            .expect("init_boolean_analysis_friedgut_l2_core");
        env.init_boolean_analysis_friedgut_l2_core()
            .expect("idempotent");
        check_constructive(&env, "BoolAnalysis.friedgut_l2_core");
    }
}
