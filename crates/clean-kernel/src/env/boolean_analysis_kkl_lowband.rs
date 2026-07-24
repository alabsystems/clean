// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL conditional-bound glue — the **low-band influence bound**.
//!
//! The sharp-KKL roadmap (`designs/2026-06-13-sharp-kkl-max-influence-roadmap.md`,
//! warning header) replaced the FALSE `deriv_level_mass_lower` (R4) / `hc_dual_sharp`
//! (R6) with the **conditional edge-isoperimetric bound**
//! `max_i Inf_i ≤ 2^{-k} → I[f] ≥ c·k·Var` (O'Donnell §9.6 / Thm 9.28). That argument
//! splits the variance into LOW-degree (`1 ≤ |S| ≤ k`) and HIGH-degree (`|S| > k`)
//! Fourier mass; the high mass is charged to the influences via `kkl_threshold_mass_le`
//! (`(k+1)·M_{>k} ≤ I[f]`), and the low mass is the part the small-influence hypothesis
//! controls. The level-split identity itself is the LANDED keystone
//! `variance_high_mass_complement` (`Var − M_{>k} = M_{1..k}`).
//!
//! ## What this proves
//!
//! ```text
//! BoolAnalysis.variance_low_band_influence :
//!   ∀ (n k : Nat) (f : BoolFn n),
//!     Rat.le
//!       (Rat.mul (natCast (Nat.succ k))
//!                (Rat.sub (Variance n f)
//!                         (subsetSum n (fun S =>
//!                             ind (Bool.and (Nat.ble 1 (setSizeNat n S))
//!                                           (Bool.not (Nat.ble (Nat.succ k) (setSizeNat n S))))
//!                                 · (f̂ S · f̂ S)))))
//!       (TotalInfluence n f)
//! ```
//!
//! i.e. `(k+1)·(Var − M_{1..k}) ≤ I[f]`, where (writing `w S := f̂(S)²`)
//!   * `M_{1..k} := Σ_{1 ≤ |S| ≤ k} w S` is the non-empty low-degree Fourier mass.
//!
//! This is the **high-band charge, re-expressed in terms of the LOW band** — the exact
//! consumer shape the conditional edge-isoperimetric bound needs. The genuinely-missing
//! hypercontractive content is now isolated to a single forward step: once the low band
//! is shown small under the small-influence hypothesis (`M_{1..k} ≤ ε·Var`, the
//! O'Donnell §9.6 per-coordinate hypercontractive charge), this bound becomes
//! `(k+1)·(1−ε)·Var ≤ I[f]`, the KKL conclusion. It asserts NO hypercontractive
//! inequality itself — it is a sound, UNCONDITIONAL rearrangement of the landed
//! `(k+1)·M_{>k} ≤ I[f]` through the landed level-split identity, refute-checked against
//! the dictator/parity/constant battery. (Unconditional safety: on the dictator
//! `χ_i`, `Var = 1`, `M_{1..k} = 1` for `k ≥ 1` so the LHS is `(k+1)·0 = 0 ≤ I[f] = 1`;
//! at `k = 0`, `M_{1..0} = 0` so the LHS is `1·Var = Var ≤ I[f]` — the Poincaré bound.)
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! 1. `kkl_threshold_mass_le n f (Nat.succ k)` (LANDED): `(k+1)·M_{>k} ≤ I[f]`, where
//!    `M_{>k} = subsetSum n (fun S => ind(ble (k+1) |S|)·w)` is byte-for-byte the
//!    keystone's high-band integrand.
//! 2. `variance_high_mass_complement n k f` (LANDED): `Var − M_{>k} = M_{1..k}`.
//! 3. `Rat.eq_sub_of_sub_eq Var M_{>k} M_{1..k}` (this module) turns (2) into
//!    `M_{>k} = Var − M_{1..k}` — a pure abelian-group rearrangement
//!    (`add_right_cancel` + `sub_add_cancel` + `add_comm`).
//! 4. `Eq.subst` (motive `fun t => (k+1)·t ≤ I[f]`) transports (1) along (3) to land
//!    `(k+1)·(Var − M_{1..k}) ≤ I[f]`.
//!
//! Every leaf (`kkl_threshold_mass_le`, `variance_high_mass_complement`,
//! `Rat.add_right_cancel`, `Rat.sub_add_cancel`, `Rat.add_comm`, Eq/congr built-ins) is
//! `Constructive` with empty closure, so this rung is too. No axiom is added or removed.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the low-band influence rung. Spellings are byte-identical to
/// the on-branch `MassSplitConsts` / `LevelLowerConsts` carriers so all terms stay
/// def-eq to the keystone and threshold-mass rungs they reuse.
struct LowBandConsts {
    nat: Expr,
    rat: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    rat_add: Expr,
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

impl LowBandConsts {
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
    /// `LevelLowerConsts.natcast` spelling that `kkl_threshold_mass_le` uses.
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
    /// `@Eq Rat l r`.
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![self.u1.clone()]),
            [self.rat.clone(), l, r],
        )
    }
    /// `Eq.trans.{1} Rat a b c h1 h2 : a = c`.
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.trans"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, cc, h1, h2],
        )
    }
    /// `Eq.symm.{1} Rat a b h : b = a`.
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![self.u1.clone()]),
            [self.rat.clone(), a, b, h],
        )
    }
    /// `@Eq.subst.{1} Rat motive a b h_eq h_a : motive b`.
    fn subst(&self, motive: Expr, a: Expr, b: Expr, h_eq: Expr, h_a: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq.subst"), vec![self.u1.clone()]),
            [self.rat.clone(), motive, a, b, h_eq, h_a],
        )
    }
    /// `@congrArg.{1,1} Rat Rat x y g h : g x = g y` (for `g : Rat → Rat`).
    fn congr_rat(&self, x: Expr, y: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("congrArg"),
                vec![self.u1.clone(), self.u1.clone()],
            ),
            [self.rat.clone(), self.rat.clone(), x, y, g, h],
        )
    }

    // ── the band integrands (byte-identical to the keystone's m_lo_fn / m_hi_fn) ──

    /// `fun S => ind (and (ble 1 |S|) (not (ble (k+1) |S|))) · (f̂·f̂)` —
    /// the `M_{1..k}` band integrand (the genuine `1 ≤ |S| ≤ k` set).
    fn m_lo_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let ss = self.ss_nat_of(n, &s);
        let band = self.band(self.ble1(ss.clone()), self.bnot(self.ble_succ_k(k, ss)));
        let body = self.mul(self.ind_of(band), self.fsq(n, f, &s));
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun S => ind (ble (k+1) |S|) · (f̂·f̂)` — the `M_{>k}` integrand
    /// (byte-identical to the keystone's `m_hi_fn` and `kkl_threshold_mass_le`'s
    /// mask at `kNat := succ k`).
    fn m_hi_fn(&self, parent: &EnvDeclBuilder, n: &Expr, k: &Expr, f: &Expr) -> Expr {
        let mut d = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = d.fresh_local(hcp.clone());
        let bit = self.ble_succ_k(k, self.ss_nat_of(n, &s));
        let body = self.mul(self.ind_of(bit), self.fsq(n, f, &s));
        d.finish_child(d.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

impl Environment {
    /// Register the low-band influence chain. Idempotent.
    pub fn init_boolean_analysis_kkl_lowband(&mut self) -> Result<(), EnvError> {
        self.register_rat_eq_sub_of_sub_eq()?;
        self.register_variance_low_band_influence()?;
        Ok(())
    }

    /// `Rat.eq_sub_of_sub_eq : ∀ (a b c : Rat),
    ///   Rat.sub a b = c → b = Rat.sub a c`.
    ///
    /// The abelian-group rearrangement `a − b = c ⟹ b = a − c`. Proof, by
    /// `add_right_cancel` on the common addend `c` (it suffices that
    /// `b + c = (a − c) + c`):
    /// - RHS: `sub_add_cancel c a : (a − c) + c = a`.
    /// - LHS: from `h : a − b = c`, `congrArg (·+b) (symm h) : c + b = (a−b) + b`,
    ///   chained with `sub_add_cancel b a : (a−b)+b = a` gives `c + b = a`;
    ///   `add_comm b c : b + c = c + b` then `Eq.trans` to `b + c = a`.
    /// - So `b + c = a = (a − c) + c`, and `add_right_cancel b c (a−c) : b = a−c`.
    ///
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_rat_eq_sub_of_sub_eq(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("Rat.eq_sub_of_sub_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_rat()?; // Rat.add, Rat.neg, Rat.sub, Rat.add_right_cancel, congrArg
        self.init_boolean_analysis_order_toolkit_b1b()?; // Rat.sub_add_cancel
        self.register_rat_add_comm_proof()?; // Rat.add_comm

        let c = LowBandConsts::new();
        let rat = c.rat.clone();
        let add_right_cancel = Expr::const_(Name::from_string("Rat.add_right_cancel"), vec![]);
        let sub_add_cancel = Expr::const_(Name::from_string("Rat.sub_add_cancel"), vec![]);
        let add_comm = Expr::const_(Name::from_string("Rat.add_comm"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (bv_id, bv) = b.fresh_local(rat.clone());
            let (cv_id, cv) = b.fresh_local(rat.clone());
            let hyp_ty = c.eq_rat(c.sub(a.clone(), bv.clone()), cv.clone());
            let concl = c.eq_rat(bv.clone(), c.sub(a.clone(), cv.clone()));
            let (h_id, _) = b.fresh_local(hyp_ty.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp_ty, concl);
            let e = b.mk_pi(cv_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(bv_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, rat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat.clone());
            let (bv_id, bv) = b.fresh_local(rat.clone());
            let (cv_id, cv) = b.fresh_local(rat.clone());
            let hyp_ty = c.eq_rat(c.sub(a.clone(), bv.clone()), cv.clone());
            let (h_id, h) = b.fresh_local(hyp_ty.clone());

            let sub_ab = c.sub(a.clone(), bv.clone()); // a − b
            let sub_ac = c.sub(a.clone(), cv.clone()); // a − c

            // g_plus_b := fun (t : Rat) => t + b   (the rewrite lift for the LHS chain)
            let g_plus_b = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = d.fresh_local(rat.clone());
                let body = c.add(t, bv.clone());
                d.finish_child(d.mk_lam(t_id, BinderInfo::Default, rat.clone(), body))
            };

            // h_symm : c = a − b   (Eq.symm h)
            let h_symm = c.symm(sub_ab.clone(), cv.clone(), h.clone());
            // h_cb_eq : c + b = (a−b) + b   (congrArg (·+b) h_symm)
            let h_cb_eq = c.congr_rat(cv.clone(), sub_ab.clone(), g_plus_b, h_symm);
            // h_subab_b : (a−b) + b = a   (sub_add_cancel b a)
            let h_subab_b = Expr::apps(sub_add_cancel.clone(), [bv.clone(), a.clone()]);
            // h_cb_a : c + b = a   (trans h_cb_eq h_subab_b)
            let h_cb_a = c.trans(
                c.add(cv.clone(), bv.clone()),
                c.add(sub_ab.clone(), bv.clone()),
                a.clone(),
                h_cb_eq,
                h_subab_b,
            );
            // h_bc_cb : b + c = c + b   (add_comm b c)
            let h_bc_cb = Expr::apps(add_comm.clone(), [bv.clone(), cv.clone()]);
            // h_bc_a : b + c = a   (trans h_bc_cb h_cb_a)
            let h_bc_a = c.trans(
                c.add(bv.clone(), cv.clone()),
                c.add(cv.clone(), bv.clone()),
                a.clone(),
                h_bc_cb,
                h_cb_a,
            );

            // h_subac_c : (a−c) + c = a   (sub_add_cancel c a)
            let h_subac_c = Expr::apps(sub_add_cancel.clone(), [cv.clone(), a.clone()]);
            // h_a_subac : a = (a−c) + c   (symm h_subac_c)
            let h_a_subac = c.symm(c.add(sub_ac.clone(), cv.clone()), a.clone(), h_subac_c);
            // h_eq : b + c = (a−c) + c   (trans h_bc_a h_a_subac)
            let h_eq = c.trans(
                c.add(bv.clone(), cv.clone()),
                a.clone(),
                c.add(sub_ac.clone(), cv.clone()),
                h_bc_a,
                h_a_subac,
            );

            // body : b = a − c   (add_right_cancel b c (a−c) h_eq)
            //   Rat.add_right_cancel : ∀ x y z, (x + y = z + y) → x = z.
            let body = Expr::apps(
                add_right_cancel.clone(),
                [bv.clone(), cv.clone(), sub_ac.clone(), h_eq],
            );

            let e = b.mk_lam(h_id, BinderInfo::Default, hyp_ty, body);
            let e = b.mk_lam(cv_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_lam(bv_id, BinderInfo::Default, rat.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Default, rat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
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

    /// `BoolAnalysis.variance_low_band_influence :
    ///   ∀ (n k : Nat) (f : BoolFn n),
    ///     Rat.le (Rat.mul (natCast (Nat.succ k)) (Rat.sub (Variance n f) M_{1..k}))
    ///            (TotalInfluence n f)`,
    /// where `M_{1..k} := subsetSum n (fun S =>
    ///   ind(and (ble 1 |S|) (not (ble (k+1) |S|)))·(f̂·f̂))`.
    ///
    /// `(k+1)·(Var − M_{1..k}) ≤ I[f]` — the landed high-band charge
    /// `(k+1)·M_{>k} ≤ I[f]` re-expressed through the landed level-split identity
    /// `Var − M_{>k} = M_{1..k}`. See module docs for the proof.
    ///
    /// Kernel-checked, `Constructive`, empty closure. Idempotent.
    pub fn register_variance_low_band_influence(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.variance_low_band_influence");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // Variance, TotalInfluence, FourierCoefficient
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_rat()?;
        self.register_subset_sum()?;
        self.register_set_size_nat()?;
        self.register_kkl_threshold_mass_le()?;
        self.register_variance_high_mass_complement()?;
        self.register_rat_eq_sub_of_sub_eq()?;

        let c = LowBandConsts::new();
        let nat = c.nat.clone();
        let threshold_mass_le = Expr::const_(
            Name::from_string("BoolAnalysis.kkl_threshold_mass_le"),
            vec![],
        );
        let high_complement = Expr::const_(
            Name::from_string("BoolAnalysis.variance_high_mass_complement"),
            vec![],
        );
        let eq_sub_of_sub_eq = Expr::const_(Name::from_string("Rat.eq_sub_of_sub_eq"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let var = c.variance_of(&n, &f);
            let m_lo = c.subset_sum_of(&n, c.m_lo_fn(&b, &n, &k, &f));
            let lhs = c.mul(c.natcast(&c.succ(k.clone())), c.sub(var, m_lo));
            let concl = c.rat_le(lhs, c.total_influence_of(&n, &f));
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, concl);
            let e = b.mk_pi(k_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(nat.clone());
            let (k_id, k) = b.fresh_local(nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let var = c.variance_of(&n, &f);
            let succ_k = c.succ(k.clone());
            let natcast_succ_k = c.natcast(&succ_k);
            let m_hi = c.subset_sum_of(&n, c.m_hi_fn(&b, &n, &k, &f));
            let m_lo = c.subset_sum_of(&n, c.m_lo_fn(&b, &n, &k, &f));
            let ti = c.total_influence_of(&n, &f);

            // h_thr : (k+1)·M_{>k} ≤ I[f]   (kkl_threshold_mass_le n f (succ k)).
            //   `kkl_threshold_mass_le`'s mask at `kNat := succ k` is byte-for-byte
            //   `m_hi_fn`, so its LHS is `natCast (succ k) · M_{>k}`.
            let h_thr = Expr::apps(
                threshold_mass_le.clone(),
                [n.clone(), f.clone(), succ_k.clone()],
            );

            // h_split : Var − M_{>k} = M_{1..k}   (variance_high_mass_complement n k f).
            let h_split = Expr::apps(high_complement.clone(), [n.clone(), k.clone(), f.clone()]);
            // h_rearr : M_{>k} = Var − M_{1..k}
            //   (eq_sub_of_sub_eq Var M_{>k} M_{1..k} h_split).
            let h_rearr = Expr::apps(
                eq_sub_of_sub_eq.clone(),
                [var.clone(), m_hi.clone(), m_lo.clone(), h_split],
            );

            // motive : fun (t : Rat) => natCast (succ k) · t ≤ I[f]
            let motive = {
                let mut d = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = d.fresh_local(c.rat.clone());
                let body = c.rat_le(c.mul(natcast_succ_k.clone(), t), ti.clone());
                d.finish_child(d.mk_lam(t_id, BinderInfo::Default, c.rat.clone(), body))
            };
            // body : natCast (succ k) · (Var − M_{1..k}) ≤ I[f]
            //   Eq.subst motive M_{>k} (Var − M_{1..k}) h_rearr h_thr.
            let body = c.subst(
                motive,
                m_hi.clone(),
                c.sub(var.clone(), m_lo.clone()),
                h_rearr,
                h_thr,
            );

            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(k_id, BinderInfo::Default, nat.clone(), e);
            let e = b.mk_lam(n_id, BinderInfo::Default, nat.clone(), e);
            b.finish(e)
        };

        // KKL-finish idempotency: a heavy init dep may now register this
        // declaration transitively; re-check before the final add_decl.
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

    fn env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_lowband()
            .expect("init_boolean_analysis_kkl_lowband");
        env.init_boolean_analysis_kkl_lowband().expect("idempotent");
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
            "{name} closure must be empty"
        );
    }

    #[test]
    fn test_rat_eq_sub_of_sub_eq_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "Rat.eq_sub_of_sub_eq");
    }

    #[test]
    fn test_variance_low_band_influence_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.variance_low_band_influence");
    }

    /// THE TARGET-REFUTATION GATE (sharp-KKL rule). `refute_conjecture` must NOT
    /// refute `variance_low_band_influence` — it is a sound, unconditional
    /// rearrangement of the landed high-band charge through the landed level-split
    /// identity — when probed over the canonical Boolean-function battery
    /// (constants + the dictators, the functions that killed the false
    /// `deriv_level_mass_lower`). A refutation would mean the statement is FALSE
    /// and must not be built.
    #[test]
    fn test_variance_low_band_influence_not_refuted() {
        use super::super::carrier_refutation::refute_conjecture;
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let info = env
            .get_const(&Name::from_string(
                "BoolAnalysis.variance_low_band_influence",
            ))
            .expect("registered");
        assert_eq!(
            refute_conjecture(&tc, &info.type_),
            None,
            "the low-band influence bound is a true inequality; it must NOT refute \
             on the dictator/constant battery"
        );
    }
}
