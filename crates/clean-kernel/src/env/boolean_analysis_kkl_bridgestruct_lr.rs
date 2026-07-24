// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL hypercontractive BRIDGE — the LEVEL-RESTRICTION SUM (axiom-free).
//!
//! # Where this sits in the §9.6 bridge
//!
//! The genuine O'Donnell §9.6 per-coordinate bridge is
//!
//! ```text
//!   W^{≤k}[D_i f]  ≤  9^k · ‖T_{1/3} D_i f‖₂²            (A) low-band extraction
//!                  ≤  9^k · ‖D_i f‖_{4/3}²  =  9^k·4·Inf_i^{3/2}.   (B) DUAL HC step
//! ```
//!
//! This module owns **step (A) at the SUM granularity** — the level-restriction
//! `W^{≤k}[a] ≤ 9^k·‖T_{1/3} a‖₂²`. It is INDEPENDENT of the (separately in-flight)
//! dual `(4/3→2)` bound (B): it is pure Fourier/influence combinatorics, lifting
//! the LANDED per-subset atom
//! [`BoolAnalysis.lowband_term_le_noise_term`] (`bridge_level.rs`) over all `S`
//! with `|S| ≤ k`.
//!
//! ## The overlay definitions (stated, NOT new constants — inlined in the type)
//!
//! For a coefficient function `a : HCPoint n → Rat`, write its un-normalized
//! Fourier coefficient (byte-for-byte the `noise_spectral_level` inner sum)
//!
//! ```text
//!   A_S := Â_a(S) := subsetSum n (fun x => a x · chi n S x).
//! ```
//!
//! The two bands the bridge talks about:
//!
//! ```text
//!   W^{≤k}[a]      := subsetSum n (fun S => ind (Nat.ble (setSizeNat n S) k) · (A_S · A_S))
//!   ‖T_{1/3} a‖₂²  := subsetSum n (fun S => levelWt (1/3) n S · (A_S · A_S))
//! ```
//!
//! `W^{≤k}[a]` is the low-degree mass `Σ_{|S| ≤ k} A_S²` — the indicator
//! `ind (Nat.ble |S| k)` is the `{0,1}` mask of `|S| ≤ k` (the `Nat.ble`
//! reflection bridges the boolean test to `Nat.le`). `‖T_{1/3} a‖₂²` is exactly
//! the RHS of [`BoolAnalysis.noise_spectral_level`] at `ρ = 1/3`
//! (`levelWt (1/3) n S = (1/9)^{|S|}` is the `ρ²`-weight), so the deliverable
//! plugs directly into the spectral-2-norm identity.
//!
//! ## Deliverables
//!
//! ```text
//! BoolAnalysis.lowband_term_le_noise_term_masked :          -- per-S masked atom
//!   ∀ (n k : Nat) (S : HCPoint n) (A : Rat) (bit : Bool),
//!     (bit = Bool.true → Nat.le (setSizeNat n S) k) →
//!       Rat.le (Rat.mul (ind bit) (Rat.mul A A))
//!              (Rat.mul (powNat (ofNat 9) k)
//!                       (Rat.mul (levelWt (1/3) n S) (Rat.mul A A)))
//!
//! BoolAnalysis.lowband_le_noise_sum :                       -- THE LR SUM (target)
//!   ∀ (n k : Nat) (a : HCPoint n → Rat),
//!     Rat.le (subsetSum n (fun S => ind (Nat.ble (setSizeNat n S) k) · (A_S · A_S)))
//!            (Rat.mul (powNat (ofNat 9) k)
//!                     (subsetSum n (fun S => levelWt (1/3) n S · (A_S · A_S))))
//! ```
//!
//! ## Proof route (constructive, empty admitted-axiom closure)
//!
//! 1. **Per-S masked atom** — `Bool.rec` on `bit` (the `threshold_term_le`
//!    precedent). The threshold hypothesis is carried INTO the recursor motive so
//!    the true branch can apply it.
//!    - `bit = false`: `ind false ≡ 0`, LHS `≡ 0·(A·A)`; RHS is nonneg
//!      (`9^k ≥ 0` via `powNat_nonneg`; `levelWt ≥ 0` via `levelWt_eq_powNat` +
//!      `powNat_nonneg` of `(1/3)² ≥ 0`; `A² ≥ 0` via `sq_nonneg`), and
//!      `0 = 0·(A·A)` (`zero_mul`) transports `0 ≤ RHS` onto the goal.
//!    - `bit = true`: `ind true ≡ 1`, LHS `≡ 1·(A·A)`; the LANDED atom
//!      `lowband_term_le_noise_term n k S A (hyp Eq.refl)` is `A·A ≤ RHS`, and
//!      `1·(A·A) = A·A` (`one_mul`) transports it onto the goal.
//! 2. **Lift** — `subsetSum_le_of_pointwise n LOW HI hyp`, with the pointwise
//!    hypothesis `hyp S := masked-atom at (A_S, Nat.ble |S| k,
//!    fun he => Nat.le_of_ble_eq_true |S| k he)`. LHS `LOW` is `W^{≤k}[a]`; the
//!    RHS `HI S := 9^k·(levelWt·A²)` sums to `subsetSum n HI`.
//! 3. **Pull `9^k` out** — `subsetSum_smul n (9^k) (fun S => levelWt·A²)` is
//!    `subsetSum n HI = 9^k · ‖T_{1/3} a‖₂²`; `Eq.subst` (motive
//!    `t ↦ W^{≤k}[a] ≤ t`) transports (2) along it.
//!
//! Every leaf (`lowband_term_le_noise_term`, `subsetSum_le_of_pointwise`,
//! `subsetSum_smul`, `Nat.le_of_ble_eq_true`, `Rat.powNat_nonneg`, `Rat.sq_nonneg`,
//! `Rat.mul_nonneg`, `Rat.zero_mul`, `Rat.one_mul`, `levelWt_eq_powNat`, the Eq /
//! `Bool.rec` / `Nat.rec` built-ins) is `Constructive` with empty closure, so both
//! deliverables are too. No `sorry`/`add_decl_unchecked`/`add_decl_structural`. No
//! axiom is added or removed. Gated behind `cfg(any(test, feature =
//! "math-overlays"))`, matching its sibling `boolean_analysis_kkl_bridge_level`.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the level-restriction SUM.
struct BridgeStructConsts {
    order: OrderConsts,
    nat: Expr,
    bool_: Expr,
    bool_true: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_le: Expr,
    nat_ble: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    pow_nat: Expr,
    of_nat: Expr,
    ind: Expr,
    chi: Expr,
    level_wt: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    hcpoint: Expr,
    u1: Level,
}

impl BridgeStructConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            bool_: k("Bool"),
            bool_true: k("Bool.true"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_le: k("Nat.le"),
            nat_ble: k("Nat.ble"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            pow_nat: k("Rat.powNat"),
            of_nat: k("Rat.ofNat"),
            ind: k("BoolAnalysis.ind"),
            chi: k("BoolAnalysis.chi"),
            level_wt: k("BoolAnalysis.levelWt"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            u1: l1,
        }
    }

    fn rat(&self) -> Expr {
        self.order.rat.clone()
    }
    fn zero(&self) -> Expr {
        self.order.rat_zero.clone()
    }
    fn one(&self) -> Expr {
        self.order.rat_one.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn le0(&self, a: Expr) -> Expr {
        self.le(self.zero(), a)
    }
    fn symm_rat(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
    fn subst_rat(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        self.order.subst(motive, a, b, h_eq, h_a)
    }

    fn nat_lit(&self, v: u64) -> Expr {
        let mut e = self.nat_zero.clone();
        for _ in 0..v {
            e = Expr::app(self.nat_succ.clone(), e);
        }
        e
    }
    /// `Rat.mk (Int.ofNat num) den`.
    fn rat_lit(&self, num: u64, den: u64) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), self.nat_lit(num)),
                self.nat_lit(den),
            ],
        )
    }
    fn rho_third(&self) -> Expr {
        self.rat_lit(1, 3)
    }
    /// `Rat.ofNat 9`.
    fn nine(&self) -> Expr {
        Expr::app(self.of_nat.clone(), self.nat_lit(9))
    }
    fn pow(&self, b: &Expr, e: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [b.clone(), e.clone()])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat())
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn set_size(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn level_wt_of(&self, rho: &Expr, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.level_wt.clone(), [rho.clone(), n.clone(), s.clone()])
    }
    fn chi_of(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `Nat.ble a b`.
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    /// `Nat.le a b`.
    fn nat_le_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `bit = Bool.true`.
    fn bit_eq_true(&self, bit: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.bool_.clone(), bit, self.bool_true.clone()],
        )
    }

    /// The un-normalized Fourier coefficient `A_a(S) := subsetSum n (fun x =>
    /// a x · chi n S x)` — byte-for-byte the `noise_spectral_level` `a_coeff`.
    fn a_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(a.clone(), x.clone()), self.chi_of(n, s, &x));
        let g = b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g)
    }

    /// `Rat.powNat_nonneg b k h : 0 ≤ b^k`.
    fn pow_nonneg(&self, b: Expr, e: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.powNat_nonneg"), vec![]),
            [b, e, h],
        )
    }
    /// `Rat.mul_nonneg a b ha hb : 0 ≤ a·b`.
    fn mul_nonneg(&self, a: Expr, b: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_nonneg"), vec![]),
            [a, b, ha, hb],
        )
    }
    /// `Rat.sq_nonneg a : 0 ≤ a·a`.
    fn sq_nonneg(&self, a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]),
            [a],
        )
    }
}

/// `0 ≤ Rat.ofNat v` via the `Rat.le_of_ble_eq_true` native-reduction idiom.
fn build_zero_le_ofnat(c: &BridgeStructConsts, v: u64) -> Expr {
    let val = Expr::app(c.of_nat.clone(), c.nat_lit(v));
    let bool_c = c.bool_.clone();
    let btrue = c.bool_true.clone();
    let eq_refl_bool = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![c.u1.clone()]),
        [bool_c, btrue],
    );
    Expr::apps(
        Expr::const_(Name::from_string("Rat.le_of_ble_eq_true"), vec![]),
        [c.zero(), val, eq_refl_bool],
    )
}

impl Environment {
    /// Register the KKL level-restriction SUM half. Idempotent.
    pub fn init_boolean_analysis_kkl_bridgestruct_lr(&mut self) -> Result<(), EnvError> {
        self.register_lowband_term_le_noise_term_masked()?;
        self.register_lowband_le_noise_sum()?;
        Ok(())
    }

    /// `BoolAnalysis.lowband_term_le_noise_term_masked` — the per-S masked atom.
    /// Constructive, empty admitted-axiom closure. Idempotent.
    pub fn register_lowband_term_le_noise_term_masked(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.lowband_term_le_noise_term_masked");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_boolean_analysis()?; // ind, levelWt prerequisites
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_lowband_term_le_noise_term()?; // the LANDED unmasked atom
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_nonneg()?;
        self.register_levelwt_eq_pow_nat()?; // levelWt = powNat (ρ²) |S|
        self.register_level_wt()?;
        self.register_set_size_nat()?;
        self.register_rat_ofnat()?;
        self.init_boolean_analysis_order_toolkit()?; // sq_nonneg, mul_nonneg
        self.init_rat_field_inst()?; // zero_mul, one_mul

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BridgeStructConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_masked_type(&c),
            value: build_masked_value(&c),
        })
    }

    /// `BoolAnalysis.lowband_le_noise_sum` — the level-restriction SUM (target):
    /// `W^{≤k}[a] ≤ 9^k · ‖T_{1/3} a‖₂²`. Constructive, empty admitted-axiom
    /// closure. Idempotent.
    pub fn register_lowband_le_noise_sum(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.lowband_le_noise_sum");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_bool()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_lowband_term_le_noise_term_masked()?;
        self.register_subset_sum()?;
        self.register_subset_sum_le_of_pointwise()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_level_wt()?;
        self.register_set_size_nat()?;
        self.register_rat_pow_nat()?;
        self.register_rat_ofnat()?;
        self.register_nat_ble_le_lemmas()?; // Nat.le_of_ble_eq_true

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = BridgeStructConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_sum_type(&c),
            value: build_sum_value(&c),
        })
    }
}

// ─────────────────────────── per-S masked atom ──────────────────────────────

/// `RHS(S,A) := 9^k · (levelWt (1/3) n S · (A·A))`.
fn masked_rhs(c: &BridgeStructConsts, n: &Expr, k: &Expr, s: &Expr, a: &Expr) -> Expr {
    let aa = c.mul(a.clone(), a.clone());
    let lvl = c.level_wt_of(&c.rho_third(), n, s);
    c.mul(c.pow(&c.nine(), k), c.mul(lvl, aa))
}

fn build_masked_type(c: &BridgeStructConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (s_id, s) = b.fresh_local(c.hcpoint_of(&n));
    let (a_id, a) = b.fresh_local(c.rat());
    let (bit_id, bit) = b.fresh_local(c.bool_.clone());

    // hyp : bit = true → |S| ≤ k
    let hyp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let ante = c.bit_eq_true(bit.clone());
        let (a2_id, _) = d.fresh_local(ante.clone());
        let cons = c.nat_le_of(c.set_size(&n, &s), k.clone());
        d.finish_child(d.mk_pi(a2_id, BinderInfo::Default, ante, cons))
    };
    let (h_id, _) = b.fresh_local(hyp.clone());

    let lhs = c.mul(c.ind_of(bit.clone()), c.mul(a.clone(), a.clone()));
    let rhs = masked_rhs(c, &n, &k, &s, &a);
    let concl = c.le(lhs, rhs);

    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(bit_id, BinderInfo::Default, c.bool_.clone(), e);
    let e = b.mk_pi(a_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_pi(s_id, BinderInfo::Default, c.hcpoint_of(&n), e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn build_masked_value(c: &BridgeStructConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let (s_id, s) = b.fresh_local(c.hcpoint_of(&n));
    let (a_id, a) = b.fresh_local(c.rat());
    let (bit_id, bit) = b.fresh_local(c.bool_.clone());

    let rho = c.rho_third();
    let aa = c.mul(a.clone(), a.clone());
    let lvl = c.level_wt_of(&rho, &n, &s);
    let p9k = c.pow(&c.nine(), &k);
    let rhs = masked_rhs(c, &n, &k, &s, &a);

    // Per-bit threshold-hypothesis type: (b' = true → |S| ≤ k).
    let thr_ty_of = |bb: &Expr, parent: &EnvDeclBuilder| -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let ante = c.bit_eq_true(bb.clone());
        let (a2_id, _) = d.fresh_local(ante.clone());
        let cons = c.nat_le_of(c.set_size(&n, &s), k.clone());
        d.finish_child(d.mk_pi(a2_id, BinderInfo::Default, ante, cons))
    };
    // Goal closure: G(bit) := ind bit · (A·A) ≤ RHS.
    let goal_of = |bb: &Expr| c.le(c.mul(c.ind_of(bb.clone()), aa.clone()), rhs.clone());

    // motive : fun (b' : Bool) => (b' = true → |S| ≤ k) → G(b')
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (bp_id, bp) = m.fresh_local(c.bool_.clone());
        let thr = thr_ty_of(&bp, &m);
        let (h_id, _) = m.fresh_local(thr.clone());
        let imp = m.mk_pi(h_id, BinderInfo::Default, thr, goal_of(&bp));
        m.finish_child(m.mk_lam(bp_id, BinderInfo::Default, c.bool_.clone(), imp))
    };

    // ── nonnegativity of RHS (the false-branch witness) ─────────────────────
    // 0 ≤ 9^k    via powNat_nonneg (ofNat 9) k (0 ≤ ofNat 9).
    let h_p9k_nn = c.pow_nonneg(c.nine(), k.clone(), build_zero_le_ofnat(c, 9));
    // 0 ≤ A·A    via sq_nonneg a.
    let h_aa_nn = c.sq_nonneg(a.clone());
    // 0 ≤ levelWt (1/3) n S:
    //   levelWt_eq_powNat (1/3) n S : levelWt = powNat ((1/3)²) |S|;  symm gives
    //   powNat ((1/3)²) |S| = levelWt; transport 0 ≤ powNat ((1/3)²) |S| onto levelWt.
    let rho_sq = c.mul(rho.clone(), rho.clone());
    let size = c.set_size(&n, &s);
    let pow_rho_sq = c.pow(&rho_sq, &size);
    let h_pow_rho_nn = c.pow_nonneg(rho_sq.clone(), size.clone(), c.sq_nonneg(rho.clone()));
    let lvl_eq_pow = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.levelWt_eq_powNat"), vec![]),
        [rho.clone(), n.clone(), s.clone()],
    );
    // motive t => 0 ≤ t ; subst along (levelWt = pow) from (0 ≤ pow) to (0 ≤ levelWt):
    //   levelWt_eq_powNat : levelWt = pow ; we need motive pow → motive levelWt, so
    //   use symm (pow = levelWt) then subst the (0 ≤ pow) witness.
    let pow_eq_lvl = c.symm_rat(lvl.clone(), pow_rho_sq.clone(), lvl_eq_pow);
    let motive_nn = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat());
        let body = c.le0(t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    let h_lvl_nn = c.subst_rat(
        motive_nn,
        pow_rho_sq.clone(),
        lvl.clone(),
        pow_eq_lvl,
        h_pow_rho_nn,
    );
    // 0 ≤ levelWt · (A·A)
    let h_lvl_aa_nn = c.mul_nonneg(lvl.clone(), aa.clone(), h_lvl_nn, h_aa_nn.clone());
    // 0 ≤ 9^k · (levelWt · (A·A)) = 0 ≤ RHS
    let lvl_aa = c.mul(lvl.clone(), aa.clone());
    let h_rhs_nn = c.mul_nonneg(p9k.clone(), lvl_aa.clone(), h_p9k_nn, h_lvl_aa_nn);

    // ── false branch: ind false ≡ 0, LHS ≡ 0·(A·A). ────────────────────────
    // 0·(A·A) = 0 (zero_mul); symm: 0 = 0·(A·A); subst h_rhs_nn (0 ≤ RHS) onto
    // motive t => t ≤ RHS.
    let false_proof = {
        let zero_mul_aa = c.mul(c.zero(), aa.clone());
        // e0 : 0·(A·A) = 0
        let e0 = Expr::app(
            Expr::const_(Name::from_string("Rat.zero_mul"), vec![]),
            aa.clone(),
        );
        let e_sym = c.symm_rat(zero_mul_aa.clone(), c.zero(), e0); // 0 = 0·(A·A)
        let motive2 = {
            let mut m = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = m.fresh_local(c.rat());
            let body = c.le(t, rhs.clone());
            m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        c.subst_rat(motive2, c.zero(), zero_mul_aa, e_sym, h_rhs_nn)
    };
    let false_case = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let thr_false = thr_ty_of(&bool_false, &m);
        let (h_id, _) = m.fresh_local(thr_false.clone());
        m.finish_child(m.mk_lam(h_id, BinderInfo::Default, thr_false, false_proof))
    };

    // ── true branch: ind true ≡ 1, LHS ≡ 1·(A·A). ──────────────────────────
    // lowband_term_le_noise_term n k S A (ht Eq.refl) : A·A ≤ RHS; transport LHS
    // A·A → 1·(A·A) via one_mul (reversed).
    let true_case = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let thr_true = thr_ty_of(&c.bool_true, &m);
        let (ht_id, ht) = m.fresh_local(thr_true.clone());

        // hk : |S| ≤ k  := ht (Eq.refl Bool Bool.true)
        let refl_true = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![c.u1.clone()]),
            [c.bool_.clone(), c.bool_true.clone()],
        );
        let hk = Expr::app(ht, refl_true);
        // base : A·A ≤ RHS  := lowband_term_le_noise_term n k S A hk
        let base = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.lowband_term_le_noise_term"),
                vec![],
            ),
            [n.clone(), k.clone(), s.clone(), a.clone(), hk],
        );
        // transport A·A → 1·(A·A) via one_mul (A·A) : 1·(A·A) = A·A ; symm reversed.
        let one_aa = c.mul(c.one(), aa.clone());
        let e0 = Expr::app(
            Expr::const_(Name::from_string("Rat.one_mul"), vec![]),
            aa.clone(),
        );
        let e_sym = c.symm_rat(one_aa.clone(), aa.clone(), e0); // A·A = 1·(A·A)
        let motive1 = {
            let mut mm = EnvDeclBuilder::child_of(&m);
            let (t_id, t) = mm.fresh_local(c.rat());
            let body = c.le(t, rhs.clone());
            mm.finish_child(mm.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        let proof = c.subst_rat(motive1, aa.clone(), one_aa, e_sym, base);
        m.finish_child(m.mk_lam(ht_id, BinderInfo::Default, thr_true, proof))
    };

    // @Bool.rec.{0} motive false_case true_case bit : (bit = true → |S| ≤ k) → G(bit)
    let bool_rec = Expr::const_(Name::from_string("Bool.rec"), vec![Level::zero()]);
    let rec = Expr::apps(bool_rec, [motive, false_case, true_case, bit.clone()]);

    // hyp : bit = true → |S| ≤ k ; body := rec hyp.
    let hyp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let ante = c.bit_eq_true(bit.clone());
        let (a2_id, _) = d.fresh_local(ante.clone());
        let cons = c.nat_le_of(c.set_size(&n, &s), k.clone());
        d.finish_child(d.mk_pi(a2_id, BinderInfo::Default, ante, cons))
    };
    let (h_id, h) = b.fresh_local(hyp.clone());
    let body = Expr::app(rec, h);

    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
    let e = b.mk_lam(bit_id, BinderInfo::Default, c.bool_.clone(), e);
    let e = b.mk_lam(a_id, BinderInfo::Default, c.rat(), e);
    let e = b.mk_lam(s_id, BinderInfo::Default, c.hcpoint_of(&n), e);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

// ─────────────────────────── the LR SUM (target) ────────────────────────────

/// `LOW(a,k) := fun S => ind (Nat.ble |S| k) · (A_S · A_S)` — the `W^{≤k}` integrand.
fn low_fn(c: &BridgeStructConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, a: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let bit = c.ble(c.set_size(n, &s), k.clone());
    let coeff = c.a_coeff(&d, n, a, &s);
    let body = c.mul(c.ind_of(bit), c.mul(coeff.clone(), coeff));
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// `LVL(a) := fun S => levelWt (1/3) n S · (A_S · A_S)` — the `‖T_{1/3}a‖₂²`
/// integrand (byte-for-byte the `noise_spectral_level` RHS at `ρ = 1/3`).
fn lvl_fn(c: &BridgeStructConsts, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let lvl = c.level_wt_of(&c.rho_third(), n, &s);
    let coeff = c.a_coeff(&d, n, a, &s);
    let body = c.mul(lvl, c.mul(coeff.clone(), coeff));
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

/// `HI(a,k) := fun S => 9^k · (levelWt (1/3) n S · (A_S · A_S))` — the
/// scalar-folded RHS integrand (`subsetSum_smul`'s `fun S => c·f S` shape).
fn hi_fn(c: &BridgeStructConsts, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, a: &Expr) -> Expr {
    let mut d = EnvDeclBuilder::child_of(parent);
    let hcp = c.hcpoint_of(n);
    let (s_id, s) = d.fresh_local(hcp.clone());
    let lvl = c.level_wt_of(&c.rho_third(), n, &s);
    let coeff = c.a_coeff(&d, n, a, &s);
    let body = c.mul(c.pow(&c.nine(), k), c.mul(lvl, c.mul(coeff.clone(), coeff)));
    d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
}

fn build_sum_type(c: &BridgeStructConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let a_ty = c.hcpoint_to_rat(&n);
    let (a_id, a) = b.fresh_local(a_ty.clone());

    let lhs = c.ssum(&n, low_fn(c, &b, &n, &k, &a));
    let rhs = c.mul(c.pow(&c.nine(), &k), c.ssum(&n, lvl_fn(c, &b, &n, &a)));
    let concl = c.le(lhs, rhs);

    let e = b.mk_pi(a_id, BinderInfo::Default, a_ty, concl);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn build_sum_value(c: &BridgeStructConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let a_ty = c.hcpoint_to_rat(&n);
    let (a_id, a) = b.fresh_local(a_ty.clone());

    let p9k = c.pow(&c.nine(), &k);
    let low = low_fn(c, &b, &n, &k, &a);
    let hi = hi_fn(c, &b, &n, &k, &a);
    let lvl = lvl_fn(c, &b, &n, &a);

    let ss_low = c.ssum(&n, low.clone());
    let ss_hi = c.ssum(&n, hi.clone());
    let ss_lvl = c.ssum(&n, lvl.clone());
    let nine_ss_lvl = c.mul(p9k.clone(), ss_lvl.clone());

    // hyp : ∀ S, LOW S ≤ HI S
    //   = fun S => masked-atom n k S (A_S) (Nat.ble |S| k)
    //               (fun he => Nat.le_of_ble_eq_true |S| k he)
    let hyp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let hcp = c.hcpoint_of(&n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let size = c.set_size(&n, &s);
        let bit = c.ble(size.clone(), k.clone());
        let coeff = c.a_coeff(&d, &n, &a, &s);

        // discharge : bit = true → |S| ≤ k
        //   = fun (he : Nat.ble |S| k = true) => Nat.le_of_ble_eq_true |S| k he
        let discharge = {
            let mut e = EnvDeclBuilder::child_of(&d);
            let ante = c.bit_eq_true(bit.clone());
            let (he_id, he) = e.fresh_local(ante.clone());
            let proof = Expr::apps(
                Expr::const_(Name::from_string("Nat.le_of_ble_eq_true"), vec![]),
                [size.clone(), k.clone(), he],
            );
            e.finish_child(e.mk_lam(he_id, BinderInfo::Default, ante, proof))
        };

        let body = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.lowband_term_le_noise_term_masked"),
                vec![],
            ),
            [n.clone(), k.clone(), s.clone(), coeff, bit, discharge],
        );
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    };

    // h_pw : subsetSum n LOW ≤ subsetSum n HI
    //   = subsetSum_le_of_pointwise n LOW HI hyp.
    let h_pw = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.subsetSum_le_of_pointwise"),
            vec![],
        ),
        [n.clone(), low.clone(), hi.clone(), hyp],
    );

    // h_smul : subsetSum n HI = 9^k · subsetSum n LVL.
    //   subsetSum_smul n (9^k) LVL : subsetSum n (fun S => 9^k · LVL S) = 9^k · subsetSum n LVL.
    //   The LHS integrand `fun S => 9^k · LVL S` is byte-for-byte HI.
    let h_smul = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.subsetSum_smul"), vec![]),
        [n.clone(), p9k.clone(), lvl.clone()],
    );

    // body : subsetSum n LOW ≤ 9^k · subsetSum n LVL
    //   Eq.subst (motive t => subsetSum n LOW ≤ t) at a := subsetSum n HI,
    //   b := 9^k · subsetSum n LVL, along h_smul, transporting h_pw.
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat());
        let body = c.le(ss_low.clone(), t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    let body = c.subst_rat(motive, ss_hi, nine_ss_lvl, h_smul, h_pw);

    let e = b.mk_lam(a_id, BinderInfo::Default, a_ty, body);
    let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    const LEMMAS: &[&str] = &[
        "BoolAnalysis.lowband_term_le_noise_term_masked",
        "BoolAnalysis.lowband_le_noise_sum",
    ];

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_bridgestruct_lr()
            .expect("init_boolean_analysis_kkl_bridgestruct_lr");
        env.init_boolean_analysis_kkl_bridgestruct_lr()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_bridgestruct_lr_all_constructive_theorems() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in LEMMAS {
            let nm = Name::from_string(name);
            let info = env
                .get_const(&nm)
                .unwrap_or_else(|| panic!("{name} registered"));
            assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be Theorem");
            let value = info.value.clone().expect("proof present");
            tc.check_type(&value, &info.type_)
                .unwrap_or_else(|e| panic!("{name} must kernel-check: {e:?}"));
            assert_eq!(
                env.proof_quality(&nm),
                Some(ProofQuality::Constructive),
                "{name} must be Constructive"
            );
            assert!(
                env.axiom_deps(&nm).expect("deps").is_empty(),
                "{name} closure must be empty (foundational-only)"
            );
        }
    }

    /// THE TARGET-REFUTATION GATE (sharp-KKL rule). `refute_conjecture` must NOT
    /// refute the level-restriction SUM. By-hand edge checks on the
    /// dictator/parity/constant battery:
    /// - constant `a ≡ 0` ⟹ all `A_S = 0`, so `0 ≤ 9^k·0`;
    /// - any `a` with `k` large enough that `|S| ≤ k` for all `S` ⟹
    ///   `W^{≤k}[a] = ‖a‖₂²` and the bound is `‖a‖₂² ≤ 9^k·‖T_{1/3}a‖₂²`, which
    ///   holds since each term has `1 ≤ 9^k·(1/9)^{|S|}` for `|S| ≤ k`;
    /// - dictator `a = χ_i` (single nonzero coefficient at `|S| = 1`) with `k ≥ 1`
    ///   ⟹ `1 ≤ 9^k·(1/9)` (tight at `k = 1`).
    ///
    /// Dropping the low-band mask is FALSE (a high `|S| > k` coefficient would
    /// contribute `A_S²` on the left but only `9^k·(1/9)^{|S|}·A_S² < A_S²` on the
    /// right), so the `ind (ble |S| k)` mask is structurally essential.
    #[test]
    fn test_lowband_le_noise_sum_not_refuted() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string("BoolAnalysis.lowband_le_noise_sum"))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "lowband_le_noise_sum is a TRUE inequality; it must NOT refute on the \
             dictator/parity/constant battery"
        );
    }

    /// REFUTE-CHECK the per-S masked atom too: it is the true conditional
    /// `(bit = true → |S| ≤ k) → ind bit · A² ≤ 9^k·(levelWt·A²)`.
    #[test]
    fn test_masked_term_not_refuted() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.lowband_term_le_noise_term_masked",
            ))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "the masked per-S atom is a TRUE conditional inequality; it must NOT refute"
        );
    }
}
