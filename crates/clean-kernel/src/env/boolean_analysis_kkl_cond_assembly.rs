// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL conditional-bound assembly — the **half-variance influence floor**
//! (axiom-free, M2-independent).
//!
//! # Where this sits in the §9.6 conditional edge-isoperimetric argument
//!
//! The landed low-band influence rung
//! [`BoolAnalysis.variance_low_band_influence`] (`boolean_analysis_kkl_lowband`)
//! is the UNCONDITIONAL floor
//!
//! ```text
//!   (k+1)·(Var − M_{1..k})  ≤  I[f],            where  M_{1..k} = Σ_{1≤|S|≤k} f̂(S)².
//! ```
//!
//! The O'Donnell §9.6 / Thm 9.28 conclusion is reached by feeding it the
//! hypercontractive low-band charge: once the small-influence hypothesis forces
//! the low band to be at most HALF the variance, `M_{1..k} ≤ ½·Var`, the floor
//! collapses to `(k+1)·(½·Var) ≤ I[f]`. This module owns exactly that COLLAPSE —
//! the purely-order step that turns the bound on the low band into the influence
//! floor. It is INDEPENDENT of the (separately in-flight) hypercontractive charge
//! that supplies `M_{1..k} ≤ ½·Var`: that bound is taken as a HYPOTHESIS here, so
//! no hypercontractive inequality is asserted.
//!
//! ## Deliverable
//!
//! ```text
//! BoolAnalysis.cond_assembly_half_var :
//!   ∀ (n k : Nat) (f : BoolFn n),
//!     Rat.le M_{1..k} (Rat.div (Variance n f) Rat.two)              -- M_{1..k} ≤ ½·Var
//!       → Rat.le (Rat.mul (natCast (Nat.succ k)) (Rat.div (Variance n f) Rat.two))
//!                (TotalInfluence n f)                                -- (k+1)·(½·Var) ≤ I[f]
//! ```
//!
//! where `M_{1..k} := subsetSum n (fun S =>
//!   ind (Bool.and (Nat.ble 1 |S|) (Bool.not (Nat.ble (Nat.succ k) |S|))) · (f̂·f̂))`
//! is byte-identical to the `variance_low_band_influence` low band, and `½·Var`
//! is `Rat.div (Variance n f) Rat.two` (the `Rat.add_halves` half).
//!
//! ## Proof route (constructive, empty admitted-axiom closure)
//!
//! Write `V := Variance n f`, `H := Rat.div V Rat.two` (`= ½V`), `M := M_{1..k}`,
//! `I := TotalInfluence n f`, `c := natCast (Nat.succ k)`. From `hM : M ≤ H`:
//!
//! 1. **`V − H = H`** — `Rat.add_halves V : H + H = V`; with
//!    `Rat.sub_add_cancel H V : (V − H) + H = V` and `add_right_cancel (V−H) H H`
//!    (after `Eq.symm`/`Eq.trans` chaining `(V−H)+H = V = H+H`) lands `V − H = H`.
//! 2. **`V − H ≤ V − M`** — `Rat.sub_le_sub V V H M (Rat.le_refl V) hM`
//!    (anti-mono in the subtrahend: `M ≤ H ⟹ V − H ≤ V − M`).
//! 3. **`H ≤ V − M`** — `Eq.subst` (motive `t ↦ t ≤ V − M`) transports (2) along
//!    (1) (`V − H ↦ H`).
//! 4. **`c·H ≤ c·(V − M)`** — `Rat.mul_le_mul_of_nonneg_left c H (V−M) (3) h_cnn`
//!    (the lemma takes `b ≤ c` FIRST, then `0 ≤ a`), with
//!    `h_cnn : 0 ≤ c` := `BoolAnalysis.natCast_nonneg (Nat.succ k)`.
//! 5. **`c·H ≤ I`** — `Rat.le_trans (c·H) (c·(V−M)) I (4)
//!    (variance_low_band_influence n k f)`.
//!
//! Every leaf (`variance_low_band_influence`, `Rat.add_halves`,
//! `Rat.sub_add_cancel`, `Rat.add_right_cancel`, `Rat.sub_le_sub`, `Rat.le_refl`,
//! `Rat.mul_le_mul_of_nonneg_left`, `BoolAnalysis.natCast_nonneg`, `Rat.le_trans`,
//! the Eq built-ins) is `Constructive` with empty closure, so this rung is too. No
//! `sorry`/`add_decl_unchecked`/`add_decl_structural`. No axiom is added or
//! removed. Gated behind `cfg(any(test, feature = "math-overlays"))`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the half-variance collapse. Band/`natCast` spellings are
/// byte-identical to `boolean_analysis_kkl_lowband`'s `LowBandConsts` so the low
/// band and the scalar stay def-eq to `variance_low_band_influence`.
struct CondConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    rat_add: Expr,
    rat_div: Expr,
    rat_two: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    ind: Expr,
    fourier: Expr,
    variance: Expr,
    total_influence: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    nat_ble: Expr,
    bool_and: Expr,
    bool_not: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    u1: Level,
}

impl CondConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            nat_succ: k("Nat.succ"),
            nat_zero: k("Nat.zero"),
            rat_mul: k("Rat.mul"),
            rat_sub: k("Rat.sub"),
            rat_add: k("Rat.add"),
            rat_div: k("Rat.div"),
            rat_two: k("Rat.two"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            bool_fn: k("BoolAnalysis.BoolFn"),
            ind: k("BoolAnalysis.ind"),
            fourier: k("BoolAnalysis.FourierCoefficient"),
            variance: k("BoolAnalysis.Variance"),
            total_influence: k("BoolAnalysis.TotalInfluence"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            nat_ble: k("Nat.ble"),
            bool_and: k("Bool.and"),
            bool_not: k("Bool.not"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            u1: l1,
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn sub(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, b])
    }
    fn add(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_add.clone(), [a, b])
    }
    /// `Rat.div a b`.
    fn div(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_div.clone(), [a, b])
    }
    /// `½·a := Rat.div a Rat.two`.
    fn half(&self, a: Expr) -> Expr {
        self.div(a, self.rat_two.clone())
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
    fn ss_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn variance_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.variance.clone(), [n.clone(), f.clone()])
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `Nat.ble a b`.
    fn ble(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [a, b])
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn one_nat(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    /// `Nat.ble (succ zero) m` — the `|S| ≥ 1` bit.
    fn ble1(&self, m: Expr) -> Expr {
        self.ble(self.one_nat(), m)
    }
    /// `Nat.ble (succ k) m` — the `|S| ≥ k+1` (= `|S| > k`) bit.
    fn ble_succ_k(&self, k: &Expr, m: Expr) -> Expr {
        self.ble(self.succ(k.clone()), m)
    }
    fn band(&self, b: Expr, c: Expr) -> Expr {
        Expr::apps(self.bool_and.clone(), [b, c])
    }
    fn bnot(&self, b: Expr) -> Expr {
        Expr::app(self.bool_not.clone(), b)
    }
    /// `natCast m := Rat.mk (Int.ofNat m) 1` — byte-identical to the
    /// `LowBandConsts.natcast` spelling `variance_low_band_influence` uses.
    fn natcast(&self, m: &Expr) -> Expr {
        Expr::apps(
            self.rat_mk.clone(),
            [
                Expr::app(self.int_of_nat.clone(), m.clone()),
                self.one_nat(),
            ],
        )
    }
    fn rat_le(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(Expr::const_(Name::from_string("Rat.le"), vec![]), [l, r])
    }
    /// `Eq.symm.{1} Rat a b h : b = a`.
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    /// `Eq.trans.{1} Rat a b c h1 h2 : a = c`.
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h_a : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.u1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }

    /// `fun S => ind (and (ble 1 |S|) (not (ble (k+1) |S|))) · (f̂·f̂)` —
    /// byte-identical to `LowBandConsts.m_lo_fn` (the `M_{1..k}` integrand).
    fn m_lo_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let ss = self.ss_nat_of(n, &s);
        let band = self.band(self.ble1(ss.clone()), self.bnot(self.ble_succ_k(k, ss)));
        let body = self.mul(self.ind_of(band), self.fsq(n, f, &s));
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

impl Environment {
    /// Register the half-variance influence-floor collapse. Idempotent.
    pub fn init_boolean_analysis_kkl_cond_assembly(&mut self) -> Result<(), EnvError> {
        self.register_cond_assembly_half_var()?;
        Ok(())
    }

    /// `BoolAnalysis.cond_assembly_half_var :
    ///   ∀ (n k : Nat) (f : BoolFn n),
    ///     Rat.le M_{1..k} (½·Variance n f)
    ///       → Rat.le ((k+1)·(½·Variance n f)) (TotalInfluence n f)`.
    ///
    /// The §9.6 conditional collapse `(M_{1..k} ≤ ½·Var) ⟹ (k+1)·(½·Var) ≤ I[f]`.
    /// See module docs for the proof. Constructive, empty closure. Idempotent.
    pub fn register_cond_assembly_half_var(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.cond_assembly_half_var");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // Variance, TotalInfluence, FourierCoefficient
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_set_size_nat()?;
        self.init_boolean_analysis_kkl_lowband()?; // variance_low_band_influence
        self.init_algebra_rat_halves()?; // Rat.two, Rat.add_halves
        self.init_boolean_analysis_order_toolkit()?; // Rat.mul_le_mul_of_nonneg_left
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.init_boolean_analysis_kkl_levellower()?; // BoolAnalysis.natCast_nonneg
        self.register_rat_order_proofs()?; // Rat.le_refl
        self.init_nn_verify_interval_arith_proofs()?; // Rat.sub_le_sub
        self.init_boolean_analysis_order_toolkit_b1b()?; // Rat.sub_add_cancel
        self.init_rat()?; // Rat.add_right_cancel (idempotent; ensures presence)

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = CondConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_cond_type(&c),
            value: build_cond_value(&c),
        })
    }
}

fn build_cond_type(c: &CondConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());

    let var = c.variance_of(&n, &f);
    let half_var = c.half(var.clone());
    let m_lo = c.subset_sum_of(&n, c.m_lo_fn(&b, &n, &k, &f));
    let ti = c.total_influence_of(&n, &f);

    // hyp : M_{1..k} ≤ ½·Var
    let hyp = c.rat_le(m_lo, half_var.clone());
    // concl : (k+1)·(½·Var) ≤ I[f]
    let concl = c.rat_le(c.mul(c.natcast(&c.succ(k.clone())), half_var), ti);

    let (h_id, _) = b.fresh_local(hyp.clone());
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e))
}

fn build_cond_value(c: &CondConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());

    let var = c.variance_of(&n, &f);
    let half = c.half(var.clone()); // H = ½V
    let m_lo = c.subset_sum_of(&n, c.m_lo_fn(&b, &n, &k, &f)); // M
    let ti = c.total_influence_of(&n, &f); // I
    let succ_k = c.succ(k.clone());
    let cscalar = c.natcast(&succ_k); // c = natCast (k+1)
    let v_sub_m = c.sub(var.clone(), m_lo.clone()); // V − M
    let v_sub_h = c.sub(var.clone(), half.clone()); // V − H

    let hyp = c.rat_le(m_lo.clone(), half.clone()); // M ≤ H
    let (h_id, h) = b.fresh_local(hyp.clone());

    // ── Step 1: V − H = H ───────────────────────────────────────────────────
    // add_halves V : H + H = V.
    let h_add = Expr::apps(
        Expr::const_(Name::from_string("Rat.add_halves"), vec![]),
        [var.clone()],
    );
    let h_plus_h = c.add(half.clone(), half.clone());
    // sub_add_cancel H V : (V − H) + H = V.
    let h_subaddcancel = Expr::apps(
        Expr::const_(Name::from_string("Rat.sub_add_cancel"), vec![]),
        [half.clone(), var.clone()],
    );
    // V = H + H  (symm h_add).
    let h_v_eq_hh = c.symm(h_plus_h.clone(), var.clone(), h_add);
    // (V − H) + H = H + H  (trans (V−H)+H = V = H+H).
    let vsubh_plus_h = c.add(v_sub_h.clone(), half.clone());
    let h_chain = c.trans(
        vsubh_plus_h.clone(),
        var.clone(),
        h_plus_h.clone(),
        h_subaddcancel,
        h_v_eq_hh,
    );
    // add_right_cancel (V−H) H H h_chain : V − H = H.
    //   Rat.add_right_cancel : ∀ x y z, (x + y = z + y) → x = z.
    let h_vsubh_eq_h = Expr::apps(
        Expr::const_(Name::from_string("Rat.add_right_cancel"), vec![]),
        [v_sub_h.clone(), half.clone(), half.clone(), h_chain],
    );

    // ── Step 2: V − H ≤ V − M ───────────────────────────────────────────────
    // le_refl V : V ≤ V.
    let h_v_le_v = Expr::apps(
        Expr::const_(Name::from_string("Rat.le_refl"), vec![]),
        [var.clone()],
    );
    // sub_le_sub V V H M (V≤V) (M≤H) : V − H ≤ V − M.
    //   Rat.sub_le_sub : ∀ a b c d, a≤b → d≤c → a−c ≤ b−d.  (a=V,b=V,c=H,d=M)
    let h_sub_le = Expr::apps(
        Expr::const_(Name::from_string("Rat.sub_le_sub"), vec![]),
        [
            var.clone(),
            var.clone(),
            half.clone(),
            m_lo.clone(),
            h_v_le_v,
            h.clone(),
        ],
    );

    // ── Step 3: H ≤ V − M ───────────────────────────────────────────────────
    // Eq.subst (motive t => t ≤ V − M) at a := V−H, b := H along h_vsubh_eq_h.
    let motive_le = {
        let mut m = EnvDeclBuilder::child_of(&b);
        let (t_id, t) = m.fresh_local(c.rat.clone());
        let body = c.rat_le(t, v_sub_m.clone());
        m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
    };
    let h_half_le = c.subst(
        motive_le,
        v_sub_h.clone(),
        half.clone(),
        h_vsubh_eq_h,
        h_sub_le,
    );

    // ── Step 4: c·H ≤ c·(V − M) ─────────────────────────────────────────────
    // natCast_nonneg (k+1) : 0 ≤ c.
    let h_cnn = Expr::apps(
        Expr::const_(Name::from_string("BoolAnalysis.natCast_nonneg"), vec![]),
        [succ_k.clone()],
    );
    // mul_le_mul_of_nonneg_left c H (V−M) (H≤V−M) (0≤c) : c·H ≤ c·(V−M).
    //   Type: ∀ a b c, (b≤c) → (0≤a) → (a·b ≤ a·c)  (h_bc FIRST, then h_a).
    let h_mul = Expr::apps(
        Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]),
        [
            cscalar.clone(),
            half.clone(),
            v_sub_m.clone(),
            h_half_le,
            h_cnn,
        ],
    );

    // ── Step 5: c·H ≤ I ─────────────────────────────────────────────────────
    // variance_low_band_influence n k f : c·(V − M) ≤ I.
    let h_vlbi = Expr::apps(
        Expr::const_(
            Name::from_string("BoolAnalysis.variance_low_band_influence"),
            vec![],
        ),
        [n.clone(), k.clone(), f.clone()],
    );
    // le_trans (c·H) (c·(V−M)) I h_mul h_vlbi : c·H ≤ I.
    let body = Expr::apps(
        Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
        [
            c.mul(cscalar.clone(), half.clone()),
            c.mul(cscalar, v_sub_m),
            ti,
            h_mul,
            h_vlbi,
        ],
    );

    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
    let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
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
        env.init_boolean_analysis_kkl_cond_assembly()
            .expect("init_boolean_analysis_kkl_cond_assembly");
        env.init_boolean_analysis_kkl_cond_assembly()
            .expect("idempotent");
        env
    }

    #[test]
    fn test_cond_assembly_half_var_is_constructive_theorem() {
        let env = env();
        let nm = Name::from_string("BoolAnalysis.cond_assembly_half_var");
        let info = env.get_const(&nm).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("cond_assembly_half_var must kernel-check");
        assert_eq!(
            env.proof_quality(&nm),
            Some(ProofQuality::Constructive),
            "cond_assembly_half_var must be Constructive"
        );
        assert!(
            env.axiom_deps(&nm).expect("deps").is_empty(),
            "cond_assembly_half_var closure must be empty (foundational-only)"
        );
    }
}
