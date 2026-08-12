// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL dual-HC — the **PER-COORDINATE dual-HC** (the M2 wall, broken): the sharp,
//! `n`-free, unconditional-modulo-`Inf<1` bound `‖T_{1/3} D_i f‖₂² ≤ 4·Inf_i^{3/2}`
//! on the genuine `NNReal` carrier.
//!
//! ## Where this sits
//!
//! `boolean_analysis_kkl_dualhc_step4_assemble.rs` lands the UN-normalized SQUARED
//! shadow `dualhc_step4_sq_le : W² ≤ 16·(m³·8^n)` (axiom-free), with
//! `W := subsetSum n (fun y => tg y·tg y)`, `tg := noiseOp(1/3) n (D_i f)`,
//! `m := subsetSum n (fun x => (g x·g x)·(½·½))` (the support measure). The dual
//! `(4/3→2)` campaign abandoned the NORMALIZATION step (`dualfinal_bound.rs`
//! §10.9 residual (b): "the `Expect`-level `Rat`-division-by-`2^n` normalization …
//! NOT yet expressible axiom-free") as the M2 wall.
//!
//! ## What this module proves — the wall was bookkeeping
//!
//! Define the NORMALIZED squared 2-norm `W_norm := W · inv(8^n)` (the un-normalized
//! `W` divided by the operator measure `8^n`; mathematically `‖T_{1/3} D_i f‖₂²`,
//! since `noiseOp = 2^n·T` ⟹ `W = 8^n·‖T D_i f‖₂²`). Then
//!
//! ```text
//! BoolAnalysis.dualhc_per_coord :
//!   ∀ (n : Nat) (f : BoolFn n) (i : Fin n),
//!     Eq Rat (Rat.mul m (Rat.powNat 2 n))                 -- the influence-count
//!            (Rat.mul (Rat.mul (powNat 2 n)(powNat 2 n))  --   bridge m·2^n = (2^n)²·Inf
//!                     (Influence n f i)) →                --   (i.e. m = 2^n·Inf_i)
//!     Rat.le Rat.zero (Influence n f i) →
//!     Rat.lt (Influence n f i) Rat.one →
//!     NNReal.le (NNReal.ofRat W_norm hWnn)
//!               (NNReal.mul (NNReal.ofRat 4 _) (NNReal.pow32 (Influence n f i) h0))
//! ```
//!
//! i.e. `W_norm ≤ 4·Inf_i^{3/2}`. UNCONDITIONAL modulo `0≤Inf<1` and the influence
//! -count identity `m = 2^n·Inf_i` (the standard `support-count = 2^n·probability`
//! fact; the `dualhc_m_pow2_eq_4pow_influence` bridge — supplied here as a
//! hypothesis since it is not yet a landed leaf).
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Cancel the positive `64^n = 8^n·8^n` across the squared bound:
//!
//! 1. **eL** `(8^n·8^n)·(W_norm·W_norm) = W·W`. With `D := 8^n`, `Dinv := inv D`,
//!    `dwd : D·(W·Dinv) = W` (`mul_comm`/`mul_assoc` + `mul_inv_cancel D (D≠0)` +
//!    `one_mul`), regroup `(D·D)·((W·Dinv)·(W·Dinv)) = (D·(W·Dinv))·(D·(W·Dinv))`
//!    (commutative-monoid `(p·p)·(q·q)=(p·q)·(p·q)`), then `congr` both factors by
//!    `dwd`.
//! 2. **eR** `16·(m³·8^n) = (8^n·8^n)·((16·Inf)·(Inf·Inf))`. From `m = 2^n·Inf`
//!    (h_m, cancelling the positive `2^n`) and `8^n = (2^n)³` (`powNat_mul_base`
//!    twice on the def-eq base `8 ≡ 2·(2·2)`), `m³·8^n = 8^n·8^n·Inf³`; reassociate.
//! 3. **cancel** `le_of_mul_le_mul_left_pos (W_norm²) (cube16 Inf) (8^n·8^n) hpos`
//!    on `(8^n·8^n)·W_norm² ≤ (8^n·8^n)·cube16(Inf)` (the squared bound transported
//!    by eL/eR) ⟹ `W_norm² ≤ cube16(Inf) = 16·Inf³`.
//! 4. **connect** `NNReal.le_four_pow32_of_sq_le W_norm Inf hWnn h0 h1 (cancel)`
//!    ⟹ `ofRat W_norm ≤ 4·pow32 Inf = 4·Inf^{3/2}`.
//!
//! Every leaf is a landed `Constructive` empty-closure Theorem (`dualhc_step4_sq_le`,
//! `le_four_pow32_of_sq_le`, `le_of_mul_le_mul_left_pos`, `powNat_mul_base`,
//! `powNat_pos`, `mul_inv_cancel`, the `Rat` ring laws, `Eq`/`subst` built-ins), so
//! this assembly is `Constructive` with EMPTY admitted-axiom closure. No axiom added
//! or removed; the domain count stays 4.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the per-coordinate dual-HC. The `g`/`tg`/`W`/`m`/`pow8`
/// spellings byte-match `dualhc_step4_sq_le` so its instance is def-eq.
struct PerCoordConsts {
    nat: Expr,
    rat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_two: Expr,
    rat_inv: Expr,
    rat_one: Expr,
    rat_zero: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    rat_le: Expr,
    rat_lt: Expr,
    pow_nat: Expr,
    bool_fn: Expr,
    hcpoint: Expr,
    fin: Expr,
    hc_flip: Expr,
    pm: Expr,
    noise_op: Expr,
    subset_sum: Expr,
    influence: Expr,
    // Rat ring / order leaves.
    mul_assoc: Expr,
    mul_comm: Expr,
    mul_one: Expr,
    one_mul: Expr,
    mul_inv_cancel: Expr,
    ne_zero_of_pos: Expr,
    mul_pos: Expr,
    pow_pos: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    pow_mul_base: Expr,
    le_cancel: Expr,
    // measure-identity leaves (eR / h_meas discharge).
    m_pow2_inf: Expr,
    eight_cubed: Expr,
    mul_natcast: Expr,
    mmmc: Expr,
    // dual-HC + de-square leaves.
    sq_le: Expr,
    desq: Expr,
    nnreal: Expr,
    nnreal_mul: Expr,
    nnreal_of_rat: Expr,
    nnreal_pow32: Expr,
    nnreal_le: Expr,
    // Eq / logic.
    eq1: Expr,
    eq_symm1: Expr,
    eq_trans1: Expr,
    eq_subst1: Expr,
    congr_arg1: Expr,
}

impl PerCoordConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_two: k("Rat.two"),
            rat_inv: k("Rat.inv"),
            rat_one: k("Rat.one"),
            rat_zero: k("Rat.zero"),
            rat_mul: k("Rat.mul"),
            rat_sub: k("Rat.sub"),
            rat_le: k("Rat.le"),
            rat_lt: k("Rat.lt"),
            pow_nat: k("Rat.powNat"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            fin: k("Fin"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            pm: k("BoolAnalysis.pm"),
            noise_op: k("BoolAnalysis.noiseOp"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            influence: k("BoolAnalysis.Influence"),
            mul_assoc: k("Rat.mul_assoc"),
            mul_comm: k("Rat.mul_comm"),
            mul_one: k("Rat.mul_one"),
            one_mul: k("Rat.one_mul"),
            mul_inv_cancel: k("Rat.mul_inv_cancel"),
            ne_zero_of_pos: k("Rat.ne_zero_of_pos"),
            mul_pos: k("Rat.mul_pos"),
            pow_pos: k("Rat.powNat_pos"),
            #[cfg(test)]
            pow_mul_base: k("Rat.powNat_mul_base"),
            le_cancel: k("Rat.le_of_mul_le_mul_left_pos"),
            m_pow2_inf: k("BoolAnalysis.dualhc_m_pow2_eq_4pow_influence"),
            eight_cubed: k("Rat.powNat_eight_eq_two_cubed"),
            mul_natcast: k("Rat.mul_natCast"),
            mmmc: k("Rat.mul_mul_mul_comm"),
            sq_le: k("BoolAnalysis.dualhc_step4_sq_le"),
            desq: k("NNReal.le_four_pow32_of_sq_le"),
            nnreal: k("NNReal"),
            nnreal_mul: k("NNReal.mul"),
            nnreal_of_rat: k("NNReal.ofRat"),
            nnreal_pow32: k("NNReal.pow32"),
            nnreal_le: k("NNReal.le"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm1: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans1: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            eq_subst1: Expr::const_(Name::from_string("Eq.subst"), vec![l1.clone()]),
            congr_arg1: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    // ── Rat constructors ─────────────────────────────────────────────────────
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_le.clone(), [a, b])
    }
    fn lt(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_lt.clone(), [a, b])
    }
    fn inv(&self, a: Expr) -> Expr {
        Expr::app(self.rat_inv.clone(), a)
    }
    fn half(&self) -> Expr {
        Expr::app(self.rat_inv.clone(), self.rat_two.clone())
    }
    /// `Rat.mk (Int.ofNat k) 1` — a small `Rat` literal.
    fn lit(&self, k: usize) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let mut nat = self.nat_zero.clone();
        for _ in 0..k {
            nat = Expr::app(self.nat_succ.clone(), nat);
        }
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), nat), one],
        )
    }
    /// `Rat.powNat (lit k) n`.
    fn pow_of(&self, k: usize, n: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [self.lit(k), n.clone()])
    }
    fn rho_third(&self) -> Expr {
        let one_nat = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let mut three_nat = self.nat_zero.clone();
        for _ in 0..3 {
            three_nat = Expr::app(self.nat_succ.clone(), three_nat);
        }
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), one_nat), three_nat],
        )
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn flip(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    /// `D_i f` as a lambda — byte-match `AsmConsts::deriv_lam`.
    fn deriv_lam(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let fx = Expr::app(f.clone(), x.clone());
        let fflip = Expr::app(f.clone(), self.flip(n, &x, i));
        let body = self.sub(
            Expr::app(self.pm.clone(), fx),
            Expr::app(self.pm.clone(), fflip),
        );
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    fn op(&self, n: &Expr, g: &Expr) -> Expr {
        Expr::apps(
            self.noise_op.clone(),
            [self.rho_third(), n.clone(), g.clone()],
        )
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    fn lam_hcp<F: Fn(&Expr) -> Expr>(&self, parent: &EnvDeclBuilder, n: &Expr, f: F) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = d.fresh_local(hcp.clone());
        let body = f(&x);
        d.finish_child(d.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }

    // ── Eq.{1} plumbing ──────────────────────────────────────────────────────
    fn eq_rat(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), a, b])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm1.clone(), [self.rat.clone(), a, b, h])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans1.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn assoc(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(self.mul_assoc.clone(), [a, b, cc])
    }
    fn comm(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.mul_comm.clone(), [a, b])
    }
    fn mul_one_at(&self, a: Expr) -> Expr {
        Expr::app(self.mul_one.clone(), a)
    }
    fn one_mul_at(&self, a: Expr) -> Expr {
        Expr::app(self.one_mul.clone(), a)
    }
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn pow_mul_base_at(&self, a: Expr, b: Expr, n: &Expr) -> Expr {
        Expr::apps(self.pow_mul_base.clone(), [a, b, n.clone()])
    }
    /// `congrArg (fun z => left·z) h : left·a = left·b`.
    fn congr_l(&self, parent: &EnvDeclBuilder, left: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.congr_arg1.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `congrArg (fun z => z·right) h : a·right = b·right`.
    fn congr_r(&self, parent: &EnvDeclBuilder, right: &Expr, a: Expr, b: Expr, h: Expr) -> Expr {
        let f = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = d.fresh_local(self.rat.clone());
            let body = self.mul(z, right.clone());
            d.finish_child(d.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        Expr::apps(
            self.congr_arg1.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, f, h],
        )
    }
    /// `Eq.subst.{1} (motive : Rat → Prop) a b (h : a=b) (ha : motive a) : motive b`.
    fn subst_prop(&self, motive: Expr, a: Expr, b: Expr, h: Expr, ha: Expr) -> Expr {
        Expr::apps(
            self.eq_subst1.clone(),
            [self.rat.clone(), motive, a, b, h, ha],
        )
    }
}

impl Environment {
    /// Register `BoolAnalysis.dualhc_per_coord`. Idempotent; kernel-checked,
    /// `Constructive`, empty admitted-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_percoord(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_per_coord");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // pm, hcFlip, BoolFn, HCPoint, Influence
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_noise_op()?;
        self.register_rat_pow_nat()?;
        self.register_rat_pow_nat_mul_base()?; // powNat_mul_base, powNat_pos
        self.register_rat_mul_assoc_proof()?;
        self.register_rat_mul_comm_proof()?;
        {
            let qc = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&qc)?; // mul_one, one_mul, mul_assoc, mul_comm
        }
        self.register_rat_order_proofs()?; // mul_pos, zero_lt_one
        self.init_algebra_rat_inv_dyadic()?; // mul_inv_cancel, ne_zero_of_pos
        self.register_rat_le_of_mul_le_mul_left_pos()?; // the positive-left cancel
        self.register_dualhc_step4_sq_le()?; // the squared shadow
        self.init_algebra_nnreal_desquare()?; // le_four_pow32_of_sq_le
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = PerCoordConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_per_coord(&c, false),
            value: build_per_coord(&c, true),
        })
    }

    /// Register `BoolAnalysis.dualhc_per_coord_uncond` — the per-coordinate
    /// dual-HC `‖T_{1/3} D_i f‖₂² ≤ 4·Inf_i^{3/2}` with the measure hypothesis
    /// `h_meas` DISCHARGED internally (via `build_h_meas`, which routes through the
    /// proven `dualhc_m_pow2_eq_4pow_influence` + `powNat_eight_eq_two_cubed`).
    /// UNCONDITIONAL modulo `0 ≤ Inf < 1`:
    ///
    /// ```text
    /// ∀ (n : Nat) (f : BoolFn n) (i : Fin n),
    ///   Rat.le Rat.zero (Influence n f i) →
    ///   Rat.lt (Influence n f i) Rat.one →
    ///   NNReal.le (NNReal.ofRat W_norm) (NNReal.mul (NNReal.ofRat 4) (NNReal.pow32 Inf))
    /// ```
    ///
    /// Idempotent; kernel-checked, `Constructive`, empty admitted-axiom closure.
    pub fn init_boolean_analysis_kkl_dualhc_percoord_uncond(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.dualhc_per_coord_uncond");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_boolean_analysis_kkl_dualhc_percoord()?; // the h_meas-taking core
        self.init_boolean_analysis_kkl_dualhc_minfl()?; // the proven measure leaves
        self.register_rat_mul_mul_mul_comm_theorem()?; // mul_mul_mul_comm (eR shuffles)
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = PerCoordConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_per_coord_uncond(&c, false),
            value: build_per_coord_uncond(&c, true),
        })
    }

    /// Register `BoolAnalysis.kkl_deriv_two_norm_sum_le` — the AGGREGATE
    /// (sum-over-coordinates) of the per-coordinate dual-HC bound:
    ///
    /// ```text
    /// ∀ (n : Nat) (f : BoolFn n) (eps : Rat),
    ///   (∀ i, Rat.le Rat.zero (Influence n f i)) →
    ///   (∀ i, Rat.le (Influence n f i) eps) →
    ///   Rat.lt eps Rat.one →
    ///     NNReal.le
    ///       (NNReal.finSum n (fun i => NNReal.ofRat W_norm_i hWn_i))
    ///       (NNReal.mul (NNReal.ofRat 4 h4)
    ///                   (NNReal.mul (NNReal.sqrtRat eps)
    ///                               (NNReal.ofRat (TotalInfluence n f) hTot)))
    /// ```
    ///
    /// i.e. `Σ_i ‖T_{1/3} D_i f‖₂² ≤ 4·(√ε·I[f])`. Pure `NNReal` composition of the
    /// landed per-coordinate dual-HC (`dualhc_per_coord_uncond`, `≤ 4·Inf_i^{3/2}`)
    /// summed over `i` (`NNReal.finSum_le` + `finSum_smul`) and the half-power CHARGE
    /// (`kkl_sum_pow32_influence_le`, `Σ_i Inf_i^{3/2} ≤ √ε·I[f]`), scaled by the
    /// common factor 4 (`NNReal.mul_le_mul_left`). Idempotent; kernel-checked,
    /// `Constructive`, EMPTY admitted-axiom closure. No axiom added or removed.
    pub fn init_boolean_analysis_kkl_dualhc_aggregate(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_deriv_two_norm_sum_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis_kkl_dualhc_percoord_uncond()?; // the per-coord summand
        self.init_boolean_analysis_kkl_pow32_consumer()?; // the half-power charge
        self.init_algebra_nnreal_finsum_le()?; // NNReal.finSum_le
        self.init_algebra_nnreal_finsum_smul()?; // NNReal.finSum_smul
        self.init_algebra_nnreal_reverse_square_mono()?; // NNReal.mul_le_mul_left
        self.init_algebra_nnreal_le()?; // NNReal.le.trans (+ NNReal.le)
        self.init_boolean_analysis_order_toolkit_b1c()?; // Rat.lt_of_le_of_lt
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = PerCoordConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_aggregate(&c, false),
            value: build_aggregate(&c, true),
        })
    }
}

// The assembly term builder lives in a sibling include to keep this file under
// the 500-line convention.
include!("boolean_analysis_kkl_dualhc_percoord_build.rs");
// The AGGREGATE (sum-over-coordinates) bound is a sibling include so it can share
// `PerCoordConsts` and the per-coordinate nonneg witnesses byte-for-byte.
include!("boolean_analysis_kkl_dualhc_aggregate.rs");
// RUNG 4c — reflect the NNReal aggregate back into Rat. Sibling include so it can
// reuse `PerCoordConsts::lfn`/`w_norm_and_nonneg`/`h_total_nonneg` byte-for-byte.
include!("boolean_analysis_kkl_aggregate_reflect.rs");
// Friedgut STEP (c) — the i∉J-MASKED dual-HC aggregate. Sibling include so it can
// reuse `PerCoordConsts` + `w_norm_and_nonneg` + the aggregate/reflect NNReal
// helpers byte-for-byte (the masked summand `ind(m i)·W_norm_i` is built over the
// SAME `W_norm_i` payload).
include!("boolean_analysis_kkl_dualhc_masked.rs");

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_percoord()
            .expect("init_boolean_analysis_kkl_dualhc_percoord");
        env.init_boolean_analysis_kkl_dualhc_percoord()
            .expect("idempotent");
        env
    }

    fn assert_constructive(env: &Environment, name: &str) {
        let nm = Name::from_string(name);
        let info = env.get_const(&nm).expect("registered");
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
    fn test_dualhc_per_coord_is_constructive_theorem() {
        assert_constructive(&env(), "BoolAnalysis.dualhc_per_coord");
    }

    #[test]
    fn test_dualhc_per_coord_uncond_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_percoord_uncond()
            .expect("init_boolean_analysis_kkl_dualhc_percoord_uncond");
        env.init_boolean_analysis_kkl_dualhc_percoord_uncond()
            .expect("idempotent");
        assert_constructive(&env, "BoolAnalysis.dualhc_per_coord_uncond");
    }

    #[test]
    fn test_kkl_deriv_two_norm_sum_le_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_aggregate()
            .expect("init_boolean_analysis_kkl_dualhc_aggregate");
        env.init_boolean_analysis_kkl_dualhc_aggregate()
            .expect("idempotent");
        assert_constructive(&env, "BoolAnalysis.kkl_deriv_two_norm_sum_le");
    }

    #[test]
    fn test_kkl_wnorm_sum_le_rat_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_kkl_wnorm_sum_le_rat()
            .expect("register_kkl_wnorm_sum_le_rat");
        env.register_kkl_wnorm_sum_le_rat().expect("idempotent");
        assert_constructive(&env, "BoolAnalysis.kkl_wnorm_sum_le_rat");
    }

    #[test]
    fn test_kkl_wnorm_le_d_inf_masked_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_masked()
            .expect("init_boolean_analysis_kkl_dualhc_masked");
        env.init_boolean_analysis_kkl_dualhc_masked()
            .expect("idempotent");
        assert_constructive(&env, "BoolAnalysis.kkl_wnorm_le_d_inf_masked");
    }

    #[test]
    fn test_kkl_wnorm_sum_le_rat_masked_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_dualhc_masked()
            .expect("init_boolean_analysis_kkl_dualhc_masked");
        assert_constructive(&env, "BoolAnalysis.kkl_wnorm_sum_le_rat_masked");
    }
}
