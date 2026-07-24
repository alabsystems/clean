// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL endgame — the CONDITIONAL assembly that isolates the single remaining
//! Hölder-gated gap (the dual `(4/3→2)` hypercontractivity bound).
//!
//! ## What this module proves
//!
//! Every brick of the classic KKL finish EXCEPT the dual-HC bound is a landed,
//! kernel-checked, `Constructive`, empty-closure Theorem in this tree:
//!
//!   * RUNG A — `BoolAnalysis.subsetSum_low_band_extract`
//!     (`boolean_analysis_kkl_lowband_extract.rs`).
//!   * RUNG B — `BoolAnalysis.kkl_derivative_lowband_link`
//!     (`boolean_analysis_kkl_rungb.rs`):
//!     `4·M_{1..k}[f] ≤ Σ_i W^{≤k}[D_i f]`.
//!   * the sharp, `n`-FREE charge — `BoolAnalysis.kkl_sum_rpow32_influence_le`
//!     (`boolean_analysis_kkl_nnrpow.rs`):
//!     `Σ_i r_i ≤ s·I[f]` where `IsRpow32 (Inf_i) (r_i)` (`r_i = Inf_i^{3/2}`),
//!     `0≤Inf_i≤ε`, `s·s=ε`, `0≤s`.
//!   * `BoolAnalysis.variance_low_band_influence`
//!     (`boolean_analysis_kkl_lowband.rs`):
//!     `(k+1)·(Var − M_{1..k}) ≤ I[f]`.
//!
//! The ONLY unbuilt input is the per-coordinate / summed dual-HC bound
//!
//! ```text
//!   Σ_i W^{≤k}[D_i f]  ≤  B · Σ_i r_i        (B = 9^k·4 in the textbook constant)
//! ```
//!
//! which is `‖T_{1/3} D_i f‖₂² ≤ 4·Inf_i^{3/2}` (self-adjointness + the (4/3,4)
//! discrete Hölder over NNReal) summed and low-band-extracted. That bound is the
//! sole missing piece. This module takes it as an EXPLICIT HYPOTHESIS `h_dual`
//! and discharges the entire downstream assembly axiom-free, proving
//!
//! ```text
//! BoolAnalysis.kkl_lowband_mass_of_dual_hc :
//!   ∀ (n k : Nat) (f : BoolFn n) (eps s B : Rat) (r : Fin n → Rat),
//!     (∀ i, 0 ≤ Influence n f i) → (∀ i, Influence n f i ≤ eps)
//!       → 0 ≤ s → s·s = eps → (∀ i, IsRpow32 (Influence n f i) (r i)) → 0 ≤ B
//!       → (Σ_i W^{≤k}[D_i f]  ≤  B · Σ_i r_i)
//!       → 4·M_{1..k}[f] ≤ (B·s) · TotalInfluence n f
//! ```
//!
//! i.e. **conditional on the dual-HC bound, the low-band mass is charged to a
//! constant multiple of the total influence**, with NO `n` factor (the sharp
//! KKL feature the root-free route could not reach). Combined with
//! `variance_low_band_influence` (`(k+1)·(Var − M_{1..k}) ≤ I[f]`), this is the
//! exact pair that closes `I[f] ≥ c·k·Var` once `B·s ≤ 1/4` (the constant
//! pinch the carrier's `√ε` supplies); that final numeric pinch + the helper
//! Definition + `kkl_inequality` are the only steps past `h_dual`.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! 1. RUNG B `kkl_derivative_lowband_link n k f` : `4·M_{1..k} ≤ Σ_i W^{≤k}[D_i f]`.
//! 2. `h_dual` : `Σ_i W^{≤k}[D_i f] ≤ B·Σ_i r_i`.
//! 3. `Rat.le_trans` (1,2) : `4·M_{1..k} ≤ B·Σ_i r_i`.
//! 4. charge `kkl_sum_rpow32_influence_le n f eps s r …` : `Σ_i r_i ≤ s·I[f]`.
//! 5. `Rat.mul_le_mul_of_nonneg_left B (Σ_i r_i) (s·I[f]) (4) (0≤B)` :
//!    `B·Σ_i r_i ≤ B·(s·I[f])`.
//! 6. `Rat.le_trans` (3,5) : `4·M_{1..k} ≤ B·(s·I[f])`.
//! 7. `Rat.mul_assoc B s I[f] : (B·s)·I[f] = B·(s·I[f])`; `Eq.subst` transports
//!    (6) along its `symm` to land `4·M_{1..k} ≤ (B·s)·I[f]`.
//!
//! Every leaf (`kkl_derivative_lowband_link`, `kkl_sum_rpow32_influence_le`,
//! `Rat.le_trans`, `Rat.mul_le_mul_of_nonneg_left`, `Rat.mul_assoc`,
//! `Eq.subst`/`Eq.symm`) is `Constructive` with empty closure, so this assembly
//! is too. NO axiom is added or removed; the soundness-certificate golden TCB is
//! unchanged. NOT wired into the always-on `init_boolean_analysis` aggregate (it
//! is reachable via `init_boolean_analysis_kkl_assembly`); the helper is gated so
//! it never grows the live census. Idempotent.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared atoms for the conditional KKL assembly. The `W^{≤k}` / `M_{1..k}`
/// term builders are byte-for-byte the on-branch RUNG-B spellings
/// (`boolean_analysis_kkl_rungb.rs`) so the consumed theorem types match by
/// def-eq, and the charge atoms mirror `boolean_analysis_kkl_nnrpow.rs`.
struct AssemblyConsts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    fin: Expr,
    ind: Expr,
    fourier: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    fin_sum: Expr,
    nat_ble: Expr,
    bool_and: Expr,
    bool_not: Expr,
    is_rpow32: Expr,
    influence: Expr,
    total_influence: Expr,
}

impl AssemblyConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            fin: k("Fin"),
            ind: k("BoolAnalysis.ind"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            fin_sum: k("Fin.sum"),
            nat_ble: k("Nat.ble"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            is_rpow32: k("BoolAnalysis.IsRpow32"),
            influence: k("BoolAnalysis.Influence"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
        }
    }

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
    fn fin_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.rat.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
    }
    fn le0(&self, a: Expr) -> Expr {
        self.le(self.order.rat_zero.clone(), a)
    }
    fn eq(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_eq(a, b)
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    /// `f̂(S) · f̂(S)`.
    fn fsq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
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
    fn ble1(&self, m: Expr) -> Expr {
        self.ble(self.one_nat(), m)
    }
    fn ble_succ_k(&self, k: &Expr, m: Expr) -> Expr {
        self.ble(self.succ(k.clone()), m)
    }
    fn band(&self, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.bool_and.clone(), [b, c])
    }
    fn bnot(&self, b: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), b)
    }
    /// `four := Rat.mk (Int.ofNat 4) 1` (byte-identical to `RungBConsts.four`).
    fn four(&self) -> Expr {
        let four_nat = self.succ(self.succ(self.succ(self.succ(self.nat_zero.clone()))));
        Expr::apps(
            self.rat_mk.clone(),
            [Expr::app(self.int_of_nat.clone(), four_nat), self.one_nat()],
        )
    }
    fn is_rpow32_of(&self, x: &Expr, r: &Expr) -> Expr {
        Expr::apps(self.is_rpow32.clone(), [x.clone(), r.clone()])
    }
    fn influence_of(&self, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.influence.clone(), [n.clone(), f.clone(), i.clone()])
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }

    /// `M_{1..k}[f] := subsetSum n (fun S => ind (and (ble 1 |S|)
    /// (not (ble (k+1) |S|))) · (f̂·f̂))` — byte-identical to `RungBConsts.m_lo_fn`
    /// (lifted to a `subsetSum`).
    fn m_lo(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let g = {
            let mut d = EnvDeclBuilder::child_of(parent);
            let hcp = self.hcpoint_of(n);
            let (s_id, s) = d.fresh_local(hcp.clone());
            let ss = self.set_size_nat_of(n, &s);
            let bb = self.band(self.ble1(ss.clone()), self.bnot(self.ble_succ_k(k, ss)));
            let body = self.mul(self.ind_of(bb), self.fsq(n, f, &s));
            d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
        };
        self.subset_sum_of(n, g)
    }

    /// `Σ_i W^{≤k}[D_i f] := Fin.sum n (fun i => subsetSum n (fun S =>
    /// ind (S i) · (ind (not (ble (k+1) |S|)) · (four · (f̂·f̂)))))` — the EXACT
    /// RHS of `kkl_derivative_lowband_link` (`RungBConsts.coord_w_band_fn`).
    fn sum_w_band(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let summand = {
            let mut ch = EnvDeclBuilder::child_of(parent);
            let fin_n = self.fin_of(n);
            let (i_id, i) = ch.fresh_local(fin_n.clone());
            let g = {
                let mut d = EnvDeclBuilder::child_of(&ch);
                let hcp = self.hcpoint_of(n);
                let (s_id, s) = d.fresh_local(hcp.clone());
                let s_i = Expr::app(s.clone(), i.clone());
                let ss = self.set_size_nat_of(n, &s);
                let b2 = self.bnot(self.ble_succ_k(k, ss));
                let w_band_s = self.mul(self.ind_of(b2), self.mul(self.four(), self.fsq(n, f, &s)));
                let body = self.mul(self.ind_of(s_i), w_band_s);
                d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
            };
            let body = self.subset_sum_of(n, g);
            ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
        };
        self.fin_sum_of(n, summand)
    }

    /// `Σ_i r_i := Fin.sum n r`.
    fn sum_r(&self, n: &Expr, r: &Expr) -> Expr {
        self.fin_sum_of(n, r.clone())
    }

    fn le_trans_of(&self, a: Expr, b: Expr, cc: Expr, h_ab: Expr, h_bc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
            [a, b, cc, h_ab, h_bc],
        )
    }
    /// `Rat.mul_le_mul_of_nonneg_left a b c h_bc h_0a : a·b ≤ a·c`.
    fn mul_le_left_of(&self, a: Expr, b: Expr, cc: Expr, h_bc: Expr, h_0a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
            [a, b, cc, h_bc, h_0a],
        )
    }
    /// `Rat.mul_assoc a b c : (a·b)·c = a·(b·c)`.
    fn mul_assoc_of(&self, a: Expr, b: Expr, cc: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]),
            [a, b, cc],
        )
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        self.order.symm(a, b, h)
    }
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_motive_a: Expr) -> Expr {
        self.order.subst(motive, a, b, h_eq, h_motive_a)
    }
}

impl Environment {
    /// Register the conditional KKL assembly. Idempotent; kernel-checked,
    /// `Constructive`, empty domain-axiom closure.
    pub fn init_boolean_analysis_kkl_assembly(&mut self) -> Result<(), EnvError> {
        self.register_kkl_lowband_mass_of_dual_hc()?;
        Ok(())
    }

    /// `BoolAnalysis.kkl_lowband_mass_of_dual_hc` — see the module docs.
    ///
    /// `[dual-HC summed bound] → 4·M_{1..k}[f] ≤ (B·s)·I[f]`. The conditional
    /// that isolates the single remaining Hölder-gated gap. Kernel-checked,
    /// `Constructive`, empty closure. Idempotent.
    pub fn register_kkl_lowband_mass_of_dual_hc(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_lowband_mass_of_dual_hc");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // Influence, TotalInfluence, ind, FourierCoefficient
        self.init_rat()?;
        self.init_rat_field_inst()?; // Rat.mul_assoc
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_left
        self.register_rat_order_proofs()?; // Rat.le_trans
        self.register_set_size_nat()?;
        self.register_subset_sum()?;
        self.init_boolean_analysis_kkl_rungb()?; // kkl_derivative_lowband_link
        self.init_boolean_analysis_kkl_nnrpow()?; // kkl_sum_rpow32_influence_le, IsRpow32

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = AssemblyConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_assembly(&c, false),
            value: build_assembly(&c, true),
        })
    }
}

/// Build the type (`for_value = false`, all binders `Pi`) or the proof value
/// (`for_value = true`, all binders `Lam` and the conclusion replaced by the
/// proof term).
fn build_assembly(c: &AssemblyConsts, for_value: bool) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());
    let (eps_id, eps) = b.fresh_local(c.rat());
    let (s_id, s) = b.fresh_local(c.rat());
    let (bb_id, bbig) = b.fresh_local(c.rat());
    let r_ty = c.fin_to_rat(&n);
    let (r_id, r) = b.fresh_local(r_ty.clone());

    // Hypotheses.
    let nn_hyp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let body = c.le0(c.influence_of(&n, &f, &i));
        d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };
    let le_hyp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let body = c.le(c.influence_of(&n, &f, &i), eps.clone());
        d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };
    let h0s = c.le0(s.clone());
    let hse = c.eq(c.mul(s.clone(), s.clone()), eps.clone());
    let rp_hyp = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let infl = c.influence_of(&n, &f, &i);
        let ri = Expr::app(r.clone(), i);
        let body = c.is_rpow32_of(&infl, &ri);
        d.finish_child(d.mk_pi(i_id, BinderInfo::Default, fin_n, body))
    };
    let h0b = c.le0(bbig.clone());

    let sum_w = c.sum_w_band(&b, &n, &k, &f);
    let sum_r = c.sum_r(&n, &r);
    let b_sum_r = c.mul(bbig.clone(), sum_r.clone()); // B·Σ_i r_i
    let dual_hyp = c.le(sum_w.clone(), b_sum_r.clone()); // Σ_i W ≤ B·Σ_i r_i

    let four_m_lo = c.mul(c.four(), c.m_lo(&b, &n, &k, &f)); // 4·M_{1..k}
    let ti = c.total_influence_of(&n, &f);
    let b_s = c.mul(bbig.clone(), s.clone()); // B·s
    let concl = c.le(four_m_lo.clone(), c.mul(b_s.clone(), ti.clone())); // 4·M ≤ (B·s)·I[f]

    // Bind the hypotheses as locals (their values are used in the proof).
    let (hnn_id, hnn_v) = b.fresh_local(nn_hyp.clone());
    let (hle_id, hle_v) = b.fresh_local(le_hyp.clone());
    let (h0s_id, h0s_v) = b.fresh_local(h0s.clone());
    let (hse_id, hse_v) = b.fresh_local(hse.clone());
    let (hrp_id, hrp_v) = b.fresh_local(rp_hyp.clone());
    let (h0b_id, h0b_v) = b.fresh_local(h0b.clone());
    let (hdual_id, hdual_v) = b.fresh_local(dual_hyp.clone());

    let tail = if for_value {
        // (1) RUNG B: 4·M_{1..k} ≤ Σ_i W^{≤k}[D_i f].
        let rungb = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.kkl_derivative_lowband_link"),
                vec![],
            ),
            [n.clone(), k.clone(), f.clone()],
        );
        // (3) le_trans (rungb, h_dual): 4·M ≤ B·Σ_i r_i.
        let step3 = c.le_trans_of(
            four_m_lo.clone(),
            sum_w.clone(),
            b_sum_r.clone(),
            rungb,
            hdual_v.clone(),
        );
        // (4) charge: Σ_i r_i ≤ s·I[f].
        let charge = Expr::apps(
            Expr::const_(
                Name::from_string("BoolAnalysis.kkl_sum_rpow32_influence_le"),
                vec![],
            ),
            [
                n.clone(),
                f.clone(),
                eps.clone(),
                s.clone(),
                r.clone(),
                hnn_v,
                hle_v,
                h0s_v,
                hse_v,
                hrp_v,
            ],
        );
        let s_ti = c.mul(s.clone(), ti.clone()); // s·I[f]
                                                 // (5) mul_le_left B (Σ r) (s·I[f]) charge h0b : B·Σ r ≤ B·(s·I[f]).
        let step5 = c.mul_le_left_of(bbig.clone(), sum_r.clone(), s_ti.clone(), charge, h0b_v);
        let b_s_ti = c.mul(bbig.clone(), s_ti.clone()); // B·(s·I[f])
                                                        // (6) le_trans (step3, step5): 4·M ≤ B·(s·I[f]).
        let step6 = c.le_trans_of(
            four_m_lo.clone(),
            b_sum_r.clone(),
            b_s_ti.clone(),
            step3,
            step5,
        );
        // (7) mul_assoc B s I[f] : (B·s)·I[f] = B·(s·I[f]); symm gives the reverse.
        let assoc = c.mul_assoc_of(bbig.clone(), s.clone(), ti.clone());
        let bs_ti = c.mul(b_s.clone(), ti.clone()); // (B·s)·I[f]
        let assoc_sym = c.symm(bs_ti.clone(), b_s_ti.clone(), assoc);
        // motive t => 4·M ≤ t.
        let motive = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (t_id, t) = d.fresh_local(c.rat());
            let body = c.le(four_m_lo.clone(), t);
            d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
        };
        // Eq.subst motive (B·(s·I[f])) ((B·s)·I[f]) assoc_sym step6 : 4·M ≤ (B·s)·I[f].
        c.subst(motive, b_s_ti, bs_ti, assoc_sym, step6)
    } else {
        concl
    };

    let bind = |b: &EnvDeclBuilder, id, ty: Expr, body: Expr| -> Expr {
        if for_value {
            b.mk_lam(id, BinderInfo::Default, ty, body)
        } else {
            b.mk_pi(id, BinderInfo::Default, ty, body)
        }
    };
    let e = bind(&b, hdual_id, dual_hyp, tail);
    let e = bind(&b, h0b_id, h0b, e);
    let e = bind(&b, hrp_id, rp_hyp, e);
    let e = bind(&b, hse_id, hse, e);
    let e = bind(&b, h0s_id, h0s, e);
    let e = bind(&b, hle_id, le_hyp, e);
    let e = bind(&b, hnn_id, nn_hyp, e);
    let e = bind(&b, r_id, r_ty, e);
    let e = bind(&b, bb_id, c.rat(), e);
    let e = bind(&b, s_id, c.rat(), e);
    let e = bind(&b, eps_id, c.rat(), e);
    let e = bind(&b, f_id, bool_fn_n, e);
    let e = bind(&b, k_id, c.nat.clone(), e);
    let e = bind(&b, n_id, c.nat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_assembly()
            .expect("init_boolean_analysis_kkl_assembly");
        env.init_boolean_analysis_kkl_assembly()
            .expect("idempotent");
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
    fn test_kkl_lowband_mass_of_dual_hc_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.kkl_lowband_mass_of_dual_hc");
    }

    /// REFUTE GATE. The conditional `[dual-HC] → 4·M ≤ (B·s)·I[f]` is a true
    /// implication; `refute_conjecture` must NOT refute it on the dictator /
    /// parity / constant battery.
    #[test]
    fn test_kkl_lowband_mass_of_dual_hc_not_refuted() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.kkl_lowband_mass_of_dual_hc",
            ))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "the conditional dual-HC→low-band-mass assembly is a true implication; \
             it must NOT refute"
        );
    }
}
