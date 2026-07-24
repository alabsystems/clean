// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL hypercontractive BRIDGE — the LEVEL-RESTRICTION SUM, COMPOSED OVER
//! COORDINATES (axiom-free, M2-independent).
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
//! The per-coordinate step (A) is the LANDED sibling
//! [`BoolAnalysis.lowband_le_noise_sum`] (`bridgestruct_lr.rs`),
//! `W^{≤k}[a] ≤ 9^k·‖T_{1/3} a‖₂²`, stated for ANY coefficient function
//! `a : HCPoint n → Rat`. This module owns the **coordinate-SUM granularity** of
//! that step: summing (A) over an arbitrary family of coefficient functions
//! `a : Fin n → (HCPoint n → Rat)` and factoring the shared scalar `9^k` out of
//! the resulting `Fin.sum`. It is INDEPENDENT of the (separately in-flight) dual
//! `(4/3→2)` bound (B): it is PURE `Fin.sum` order/scalar combinatorics, lifting
//! the landed per-coordinate atom over `i`.
//!
//! ## The overlay definitions (stated, NOT new constants — inlined in the type)
//!
//! For a coefficient function `a : HCPoint n → Rat`, write (byte-for-byte the
//! `bridgestruct_lr` / `noise_spectral_level` inner sum)
//!
//! ```text
//!   A_S(a) := subsetSum n (fun x => a x · chi n S x).
//! ```
//!
//! The two per-coordinate bands the bridge talks about:
//!
//! ```text
//!   W^{≤k}[a]      := subsetSum n (fun S => ind (Nat.ble (setSizeNat n S) k) · (A_S · A_S))
//!   ‖T_{1/3} a‖₂²  := subsetSum n (fun S => levelWt (1/3) n S · (A_S · A_S))
//! ```
//!
//! ## Deliverable
//!
//! ```text
//! BoolAnalysis.lowband_bridge_composed :
//!   ∀ (n k : Nat) (a : Fin n → (HCPoint n → Rat)),
//!     Rat.le (Fin.sum n (fun i => W^{≤k}[a i]))
//!            (Rat.mul (powNat (ofNat 9) k)
//!                     (Fin.sum n (fun i => ‖T_{1/3} (a i)‖₂²)))
//! ```
//!
//! i.e. `Σ_i W^{≤k}[a_i] ≤ 9^k · Σ_i ‖T_{1/3} a_i‖₂²`. Specialized to the family
//! `a i := D_i f` (the discrete derivative), this is the LR half of the §9.6
//! bridge `M_{1..k} ≤ 9^k · Σ_i ‖T_{1/3}(D_i f)‖₂²` — the only thing then standing
//! between it and the bridge is the per-coordinate dual HC step (B)
//! `‖T_{1/3}(a_i)‖₂² ≤ 4·Inf_i^{3/2}` (the M2 obligation) and the spectral
//! double-count `M_{1..k} = Σ_i W^{≤k}[D_i f]` (a separate Parseval-per-coordinate
//! identity, NOT charged here). This brick asserts NO hypercontractive inequality
//! of its own.
//!
//! ## Proof route (constructive, empty admitted-axiom closure)
//!
//! 1. **Per-`i` atom** — `lowband_le_noise_sum n k (a i) : LOW_i ≤ 9^k·LVL_i`
//!    (= `HI_i`), the landed level-restriction SUM specialized at `a i`.
//! 2. **Lift over `i`** — `Fin.sum_le n LOW HI per : Fin.sum n LOW ≤ Fin.sum n HI`.
//! 3. **Pull `9^k` out** — `Fin.sum_smul n (9^k) LVL :
//!    Fin.sum n (fun i => 9^k·LVL_i) = 9^k·Fin.sum n LVL`; the LHS integrand
//!    `fun i => 9^k·LVL_i` is byte-for-byte `HI`. `Eq.subst` (motive
//!    `t ↦ Fin.sum n LOW ≤ t`) transports (2) along it.
//!
//! Every leaf (`lowband_le_noise_sum`, `Fin.sum_le`, `Fin.sum_smul`, the Eq
//! built-ins) is `Constructive` with empty closure, so the deliverable is too. No
//! `sorry`/`add_decl_unchecked`/`add_decl_structural`. No axiom is added or
//! removed. Gated behind `cfg(any(test, feature = "math-overlays"))`, matching its
//! sibling `boolean_analysis_kkl_bridgestruct_lr`.

#![allow(clippy::too_many_arguments)]

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared atoms for the coordinate-summed level-restriction bound. Spellings are
/// byte-identical to the on-branch `BridgeStructConsts` (`bridgestruct_lr.rs`) so
/// every per-`i` band is def-eq to `lowband_le_noise_sum`'s endpoints.
struct ComposeConsts {
    order: OrderConsts,
    nat: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
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
    fin: Expr,
    fin_sum: Expr,
}

impl ComposeConsts {
    fn new() -> Self {
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            order: OrderConsts::new(),
            nat: k("Nat"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
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
            fin: k("Fin"),
            fin_sum: k("Fin.sum"),
        }
    }

    fn rat(&self) -> Expr {
        self.order.rat.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn le(&self, a: Expr, b: Expr) -> Expr {
        self.order.rat_le(a, b)
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
    /// `Rat.powNat b e`.
    fn pow(&self, b: &Expr, e: &Expr) -> Expr {
        Expr::apps(self.pow_nat.clone(), [b.clone(), e.clone()])
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat())
    }
    /// `Fin n`.
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    /// `Fin n → (HCPoint n → Rat)` — the family-of-coefficients carrier.
    fn fin_to_coeff(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.fin_of(n), self.hcpoint_to_rat(n))
    }
    /// `Fin.sum n h`.
    fn fsum(&self, n: &Expr, h: Expr) -> Expr {
        Expr::apps(self.fin_sum.clone(), [n.clone(), h])
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

    /// The un-normalized Fourier coefficient `A_a(S) := subsetSum n (fun x =>
    /// a x · chi n S x)` — byte-for-byte the `bridgestruct_lr` `a_coeff`.
    fn a_coeff(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr, s: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(a.clone(), x.clone()), self.chi_of(n, s, &x));
        let g = b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g)
    }

    /// `W^{≤k}[a] := subsetSum n (fun S => ind (Nat.ble |S| k) · (A_S · A_S))` —
    /// byte-for-byte `bridgestruct_lr::low_fn` evaluated at `a`.
    fn low_band(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, a: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let bit = self.ble(self.set_size(n, &s), k.clone());
        let coeff = self.a_coeff(&d, n, a, &s);
        let body = self.mul(self.ind_of(bit), self.mul(coeff.clone(), coeff));
        let g = d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g)
    }

    /// `‖T_{1/3} a‖₂² := subsetSum n (fun S => levelWt (1/3) n S · (A_S · A_S))` —
    /// byte-for-byte `bridgestruct_lr::lvl_fn` evaluated at `a`.
    fn noise_band(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let lvl = self.level_wt_of(&self.rho_third(), n, &s);
        let coeff = self.a_coeff(&d, n, a, &s);
        let body = self.mul(lvl, self.mul(coeff.clone(), coeff));
        let g = d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body));
        self.ssum(n, g)
    }

    /// `fun i => W^{≤k}[a i]` — the `Fin.sum` LOW integrand.
    fn low_fam(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, a: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let a_i = Expr::app(a.clone(), i);
        let body = self.low_band(&d, n, k, &a_i);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `fun i => ‖T_{1/3}(a i)‖₂²` — the `Fin.sum` LVL integrand.
    fn lvl_fam(&self, parent: &EnvDeclBuilder, n: &Expr, a: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let a_i = Expr::app(a.clone(), i);
        let body = self.noise_band(&d, n, &a_i);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }

    /// `fun i => 9^k · ‖T_{1/3}(a i)‖₂²` — the `Fin.sum` HI integrand, the
    /// scalar-folded shape `Fin.sum_smul` produces (`fun i => c · f i`).
    fn hi_fam(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, a: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let a_i = Expr::app(a.clone(), i);
        let body = self.mul(self.pow(&self.nine(), k), self.noise_band(&d, n, &a_i));
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
}

impl Environment {
    /// Register the coordinate-summed level-restriction bound. Idempotent.
    pub fn init_boolean_analysis_kkl_bridgestruct_compose(&mut self) -> Result<(), EnvError> {
        self.register_lowband_bridge_composed()?;
        Ok(())
    }

    /// `BoolAnalysis.lowband_bridge_composed` — the coordinate-summed
    /// level-restriction bound `Σ_i W^{≤k}[a_i] ≤ 9^k · Σ_i ‖T_{1/3} a_i‖₂²`.
    /// Constructive, empty admitted-axiom closure. Idempotent.
    pub fn register_lowband_bridge_composed(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.lowband_bridge_composed");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // ind, chi, levelWt, setSizeNat
        self.init_fin_sum()?; // Fin.sum, Fin.sum_le, Fin.sum_smul (kernel-checked theorems)
        self.init_boolean_analysis_kkl_bridgestruct_lr()?; // lowband_le_noise_sum
        self.register_subset_sum()?;
        self.register_level_wt()?;
        self.register_set_size_nat()?;
        self.register_rat_pow_nat()?;
        self.register_rat_ofnat()?;

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = ComposeConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_compose_type(&c),
            value: build_compose_value(&c),
        })
    }
}

fn build_compose_type(c: &ComposeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let a_ty = c.fin_to_coeff(&n);
    let (a_id, a) = b.fresh_local(a_ty.clone());

    let lhs = c.fsum(&n, c.low_fam(&b, &n, &k, &a));
    let rhs = c.mul(c.pow(&c.nine(), &k), c.fsum(&n, c.lvl_fam(&b, &n, &a)));
    let concl = c.le(lhs, rhs);

    let e = b.mk_pi(a_id, BinderInfo::Default, a_ty, concl);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn build_compose_value(c: &ComposeConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let a_ty = c.fin_to_coeff(&n);
    let (a_id, a) = b.fresh_local(a_ty.clone());

    let p9k = c.pow(&c.nine(), &k);
    let low = c.low_fam(&b, &n, &k, &a);
    let hi = c.hi_fam(&b, &n, &k, &a);
    let lvl = c.lvl_fam(&b, &n, &a);

    let ss_low = c.fsum(&n, low.clone());
    let ss_hi = c.fsum(&n, hi.clone());
    let ss_lvl = c.fsum(&n, lvl.clone());
    let nine_ss_lvl = c.mul(p9k.clone(), ss_lvl.clone());

    let lowband_le_noise_sum = Expr::const_(
        Name::from_string("BoolAnalysis.lowband_le_noise_sum"),
        vec![],
    );
    let fin_sum_le = Expr::const_(Name::from_string("Fin.sum_le"), vec![]);
    let fin_sum_smul = Expr::const_(Name::from_string("Fin.sum_smul"), vec![]);

    // per : ∀ i, W^{≤k}[a i] ≤ 9^k·‖T_{1/3}(a i)‖₂²
    //   = fun i => lowband_le_noise_sum n k (a i).
    let per = {
        let mut d = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = d.fresh_local(fin_n.clone());
        let a_i = Expr::app(a.clone(), i);
        let body = Expr::apps(lowband_le_noise_sum, [n.clone(), k.clone(), a_i]);
        d.finish_child(d.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };

    // h_sumle : Fin.sum n LOW ≤ Fin.sum n HI   (Fin.sum_le n LOW HI per).
    let h_sumle = Expr::apps(fin_sum_le, [n.clone(), low.clone(), hi.clone(), per]);

    // h_smul : Fin.sum n (fun i => 9^k·LVL i) = 9^k · Fin.sum n LVL.
    //   The LHS integrand `fun i => 9^k·LVL i` is byte-for-byte HI.
    let h_smul = Expr::apps(fin_sum_smul, [n.clone(), p9k.clone(), lvl.clone()]);

    // body : Fin.sum n LOW ≤ 9^k · Fin.sum n LVL
    //   Eq.subst (motive t => Fin.sum n LOW ≤ t) at a := Fin.sum n HI,
    //   b := 9^k · Fin.sum n LVL, along h_smul, transporting h_sumle.
    let motive = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat());
        let body = c.le(ss_low.clone(), t);
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
    };
    let body = c.order.subst(motive, ss_hi, nine_ss_lvl, h_smul, h_sumle);

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

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_bridgestruct_compose()
            .expect("init_boolean_analysis_kkl_bridgestruct_compose");
        env.init_boolean_analysis_kkl_bridgestruct_compose()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_lowband_bridge_composed_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.lowband_bridge_composed");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("lowband_bridge_composed must kernel-check");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "lowband_bridge_composed must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "lowband_bridge_composed closure must be empty (foundational-only)"
        );
    }
}
