// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL endgame — the level-`k` lower-bound chain toward `hc_dual_level_lower`.
//!
//! This module assembles, against the frozen interface of
//! `designs/2026-06-12-kkl-levelsplit-4norm-spectral-inversion.md` (§2 item 3),
//! the bricks that turn `kkl_threshold_influence` (the consumer-shaped HIGH
//! half) into the `hc_dual_level_lower` shape. Every lemma here is
//! kernel-checked, `ProofQuality::Constructive`, with an empty admitted-axiom
//! closure.
//!
//! ```text
//! BoolAnalysis.kkl_threshold_mass_le :                            -- (1)
//!   ∀ (n) (f : BoolFn n) (kNat : Nat),
//!     Rat.le
//!       (Rat.mul (natCast kNat)
//!                (subsetSum n (fun S => ind (Nat.ble kNat (setSizeNat n S))
//!                                       · (f̂ S · f̂ S))))
//!       (TotalInfluence n f)
//! ```
//!
//! i.e. `k · M_k ≤ I[f]` where `M_k := Σ_{|S|≥k} f̂(S)²` is the masked
//! level-`≥k` Fourier mass. This is `kkl_threshold_influence` with the leading
//! scalar `natCast kNat` pulled OUT of the `subsetSum` via `subsetSum_smul`,
//! landing the exact LHS the `hc_dual_level_lower` chain consumes. The
//! remaining genuinely-missing rung is the hypercontractive level-`≥k` LOWER
//! bound `Variance n f ≤ M_k` (the masked mass still captures a constant
//! fraction of the variance when `2^k ≤ n`); chaining that with this brick and
//! `total_influence_spectral` yields `hc_dual_level_lower`. See the module
//! docs at the foot of this file for the precise frozen residual signature.
//!
//! ## Proof of (1) — `kkl_threshold_mass_le` (constructive, empty closure)
//!
//! `kkl_threshold_influence n f kNat` is, after δ, the bound
//! `subsetSum n (fun S => natCast kNat · (ind(…)·f̂²)) ≤ TotalInfluence n f`,
//! i.e. the scalar `natCast kNat` is folded INSIDE the `subsetSum` integrand.
//! `subsetSum_smul n (natCast kNat) M_fn` is the scalar-homogeneity identity
//! `subsetSum n (fun S => natCast kNat · M_fn S) = natCast kNat · subsetSum n M_fn`
//! with `M_fn S := ind(Nat.ble kNat (setSizeNat n S))·(f̂ S·f̂ S)`. Transporting
//! the `≤` along this `Eq` with `Eq.subst` (motive `t ↦ t ≤ TotalInfluence`,
//! at `a := subsetSum n (scaled)`, `b := natCast kNat · subsetSum n M_fn`)
//! lands the pulled-out form. Every dependency (`kkl_threshold_influence`,
//! `subsetSum_smul`, `Eq.subst`) is `Constructive` with empty closure, so this
//! brick is too. No axiom is added or removed. Idempotent.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

/// Shared atoms for the level-`k` lower-bound chain.
struct LevelLowerConsts {
    order: OrderConsts,
    nat: Expr,
    bool_: Expr,
    bool_true: Expr,
    hcpoint: Expr,
    bool_fn: Expr,
    ind: Expr,
    set_size: Expr,
    set_size_nat: Expr,
    fourier: Expr,
    variance: Expr,
    total_influence: Expr,
    subset_sum: Expr,
    nat_ble: Expr,
    #[cfg(test)]
    #[allow(dead_code)]
    // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    nat_pow: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
}

impl LevelLowerConsts {
    fn new() -> Self {
        Self {
            order: OrderConsts::new(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            bool_true: Expr::const_(Name::from_string("Bool.true"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            bool_fn: Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            set_size: Expr::const_(Name::from_string("BoolAnalysis.setSize"), vec![]),
            set_size_nat: Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]),
            fourier: Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]),
            variance: Expr::const_(Name::from_string("BoolAnalysis.Variance"), vec![]),
            total_influence: Expr::const_(Name::from_string("BoolAnalysis.TotalInfluence"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            nat_ble: Expr::const_(Name::from_string("Nat.ble"), vec![]),
            #[cfg(test)]
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
        }
    }

    fn rat(&self) -> Expr {
        self.order.rat.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    /// `f̂(S) · f̂(S)`.
    fn fsq(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        let c = self.fourier_of(n, f, s);
        self.mul(c.clone(), c)
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    fn variance_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.variance.clone(), [n.clone(), f.clone()])
    }
    fn set_size_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size.clone(), [n.clone(), s.clone()])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    /// `Nat.ble k m`.
    fn ble(&self, k: Expr, m: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [k, m])
    }
    /// `Nat.pow 2 n`.
    #[cfg(test)]
    #[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
    fn pow2(&self, n: &Expr) -> Expr {
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        let two = Expr::app(self.nat_succ.clone(), one);
        Expr::apps(self.nat_pow.clone(), [two, n.clone()])
    }
    /// `@Eq.refl Bool Bool.true : Bool.true = Bool.true` — the proof that
    /// `Nat.ble 0 k` (which ι-reduces to `Bool.true`) equals `Bool.true`.
    fn eq_refl_true(&self) -> Expr {
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![crate::level::Level::succ(crate::level::Level::zero())],
        );
        Expr::apps(eq_refl, [self.bool_.clone(), self.bool_true.clone()])
    }
    /// The spectral total-influence integrand `fun S => setSize n S · (f̂·f̂)`
    /// — the RHS of `total_influence_spectral` / the `hc_dual_level_lower`
    /// conclusion.
    fn spectral_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let body = self.mul(self.set_size_of(n, &s), self.fsq(n, f, &s));
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `Rat.mk (Int.ofNat m) 1` — the `Nat → Rat` cast `natCast m`.
    fn natcast(&self, m: &Expr) -> Expr {
        let of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let one = Expr::app(self.nat_succ.clone(), self.nat_zero.clone());
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [Expr::app(of_nat, m.clone()), one],
        )
    }
    /// The masked level-`≥k` mass integrand `fun S => ind(ble k |S|)·(f̂·f̂)`.
    fn mask_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, knat: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let bit = self.ble(knat.clone(), self.set_size_nat_of(n, &s));
        let body = self.mul(self.ind_of(bit), self.fsq(n, f, &s));
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// The scaled integrand `fun S => natCast k · (ind(ble k |S|)·(f̂·f̂))` —
    /// matches `kkl_threshold_influence`'s LHS integrand byte-for-byte.
    fn scaled_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, knat: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let bit = self.ble(knat.clone(), self.set_size_nat_of(n, &s));
        let body = self.mul(
            self.natcast(knat),
            self.mul(self.ind_of(bit), self.fsq(n, f, &s)),
        );
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

impl Environment {
    /// Register the level-`k` lower-bound chain. Idempotent.
    pub fn init_boolean_analysis_kkl_levellower(&mut self) -> Result<(), EnvError> {
        self.register_kkl_threshold_mass_le()?;
        self.register_natcast_nonneg()?;
        self.register_hc_dual_level_lower_of_mass_bound()?;
        self.register_hc_dual_level_lower_k1()?;
        Ok(())
    }

    /// `BoolAnalysis.hc_dual_level_lower_k1`: the **unconditional `k = 1`
    /// instance** of `hc_dual_level_lower`, discharging the reduction lemma's
    /// hypothesis at `k = 1` via `variance_eq_nonempty_mass`.
    ///
    /// ```text
    /// ∀ (n) (f : BoolFn n),
    ///   Rat.le (Rat.mul (natCast 1) (Rat.mul (Variance n f) (natCast 1)))
    ///          (subsetSum n (fun S => Rat.mul (setSize n S) (f̂ S · f̂ S)))
    /// ```
    ///
    /// i.e. `1·(Var·1) ≤ Σ_S |S|·f̂(S)²` — the Poincaré inequality `Var ≤ I[f]`
    /// in the `hc_dual_level_lower` shape, proven UNCONDITIONALLY. This
    /// witnesses that `hc_dual_level_lower_of_mass_bound` is NOT vacuous: at
    /// `k = 1`, `M_1 = Σ_{|S|≥1} f̂² = Var` exactly (`variance_eq_nonempty_mass`),
    /// so the hypothesis `Var ≤ M_1` holds (with equality, via `Rat.le_refl`
    /// transported along `variance_eq_nonempty_mass`).
    ///
    /// **Honesty note.** The `k ≥ 2` instances (the genuine KKL `log n`
    /// amplification) remain the frozen residual: discharging `Var ≤ M_k` for
    /// `2^k ≤ n`, `k ≥ 2` needs the full hypercontractive level-split
    /// (`pow4_noisefn_spectral` + `hc24_at_third` + the `{0,±1}` 4-norm
    /// collapse + the `2^k ≤ n` dyadic pinch). This `k = 1` brick proves only
    /// the base instance; it does NOT close the full `hc_dual_level_lower`.
    pub fn register_hc_dual_level_lower_k1(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.hc_dual_level_lower_k1");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_hc_dual_level_lower_of_mass_bound()?;
        self.register_variance_eq_nonempty_mass()?;
        self.register_rat_order_proofs()?; // Rat.le_refl
        self.register_subset_sum()?;
        self.register_set_size()?;
        self.register_set_size_nat()?;

        let c = LevelLowerConsts::new();
        let one_nat = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let var = c.variance_of(&n, &f);
            let ti = c.subset_sum_of(&n, c.spectral_fn(&b, &n, &f));
            let lhs = c.mul(c.natcast(&one_nat), c.mul(var, c.natcast(&one_nat)));
            let concl = c.order.rat_le(lhs, ti);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, concl);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let reduction = Expr::const_(
            Name::from_string("BoolAnalysis.hc_dual_level_lower_of_mass_bound"),
            vec![],
        );
        let var_eq_mass = Expr::const_(
            Name::from_string("BoolAnalysis.variance_eq_nonempty_mass"),
            vec![],
        );
        let le_refl = Expr::const_(Name::from_string("Rat.le_refl"), vec![]);

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let var = c.variance_of(&n, &f);
            // M_1 := subsetSum n (fun S => ind(ble 1 |S|)·(f̂·f̂))
            let mass1 = c.subset_sum_of(&n, c.mask_fn(&b, &n, &f, &one_nat));

            // h_var_eq : Var = M_1   (variance_eq_nonempty_mass n f)
            let h_var_eq = Expr::apps(var_eq_mass.clone(), [n.clone(), f.clone()]);
            // h_refl : Var ≤ Var   (Rat.le_refl Var)
            let h_refl = Expr::app(le_refl.clone(), var.clone());
            // h_mass : Var ≤ M_1   via subst (motive t => Var ≤ t) Var M_1 h_var_eq h_refl
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat());
                let mbody = c.order.rat_le(var.clone(), t);
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), mbody))
            };
            let h_mass = c.order.subst(motive, var.clone(), mass1, h_var_eq, h_refl);

            // body := reduction n f 1 h_mass : 1·(Var·1) ≤ subsetSum n spectral
            let body = Expr::apps(
                reduction.clone(),
                [n.clone(), f.clone(), one_nat.clone(), h_mass],
            );

            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
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

    /// `BoolAnalysis.natCast_nonneg : ∀ (k : Nat), Rat.le Rat.zero (natCast k)`.
    ///
    /// The `Nat → Rat` cast is nonnegative. Proof: `Nat.cast_le_of_ble 0 k
    /// (Eq.refl Bool.true) : natCast 0 ≤ natCast k`, and `natCast 0 ≡ Rat.zero`
    /// definitionally (the `Fin.sum 0` base ι-reduces to `Rat.zero ≡ mk (ofNat
    /// 0) 1`), so the term inhabits `Rat.le Rat.zero (natCast k)` directly. The
    /// antecedent `Nat.ble 0 k = true` is `Eq.refl Bool.true` because `Nat.ble
    /// Nat.zero _` ι-reduces to `Bool.true` for every `k`. Constructive, empty
    /// closure.
    pub fn register_natcast_nonneg(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.natCast_nonneg");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_nat_cast_le_of_ble()?;

        let c = LevelLowerConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let concl = c.order.rat_le(c.order.rat_zero.clone(), c.natcast(&k));
            b.finish(b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl))
        };

        // value: fun (k : Nat) =>
        //   Nat.cast_le_of_ble 0 k (Eq.refl Bool.true) : natCast 0 ≤ natCast k
        //   (natCast 0 ≡ Rat.zero, so this is 0 ≤ natCast k).
        let cast_le_of_ble = Expr::const_(Name::from_string("Nat.cast_le_of_ble"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (k_id, k) = b.fresh_local(c.nat.clone());
            let body = Expr::apps(
                cast_le_of_ble.clone(),
                [c.nat_zero.clone(), k.clone(), c.eq_refl_true()],
            );
            b.finish(b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body))
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

    /// `BoolAnalysis.hc_dual_level_lower_of_mass_bound`: the reduction lemma
    /// that closes `hc_dual_level_lower` FROM the single genuinely-missing
    /// hypercontractive rung.
    ///
    /// ```text
    /// ∀ (n) (f : BoolFn n) (k : Nat),
    ///   Rat.le (Variance n f)
    ///          (subsetSum n (fun S => ind(Nat.ble k (setSizeNat n S))·(f̂·f̂)))   -- HYP: Var ≤ M_k
    ///   → Rat.le (Rat.mul (natCast 1) (Rat.mul (Variance n f) (natCast k)))      -- C·(Var·k)
    ///            (subsetSum n (fun S => Rat.mul (setSize n S) (f̂ S · f̂ S)))      -- = TotalInfluence
    /// ```
    ///
    /// with `C := natCast 1 = 1` (the design `C_NUM`). This isolates the entire
    /// remaining analytic content of `hc_dual_level_lower` into the single
    /// hypothesis `Variance n f ≤ M_k` — the **hypercontractive level-`≥k`
    /// lower bound** on the masked Fourier mass (the masked mass still captures
    /// the full variance, the `{0,±1}` 4-norm-collapse + `2^k ≤ n` dyadic
    /// pinch). Once that hypothesis is discharged unconditionally for `2^k ≤ n`
    /// (the frozen residual), `hc_dual_level_lower` follows by instantiation.
    ///
    /// ## Proof (constructive, empty closure)
    ///
    /// Let `M_k := subsetSum n (mask)`, `TI := subsetSum n (spectral)`.
    /// 1. `h_mass : Variance ≤ M_k`  (the hypothesis).
    /// 2. `h_kpos : 0 ≤ natCast k`  (`natCast_nonneg k`).
    /// 3. `mul_le_mul_of_nonneg_left (natCast k) Variance M_k h_mass h_kpos`
    ///    `: natCast k · Variance ≤ natCast k · M_k`.
    /// 4. `kkl_threshold_mass_le n f k : natCast k · M_k ≤ TI`.
    /// 5. `Rat.le_trans` of (3),(4): `natCast k · Variance ≤ TI`.
    /// 6. `1·(Variance·natCast k) ≡ natCast k · Variance`? — the LHS is
    ///    `natCast 1 · (Variance · natCast k)`; `natCast 1 ≡ Rat.one`
    ///    definitionally, so `Rat.one_mul (Variance · natCast k)` gives
    ///    `1·(Variance·k) = Variance·k`, and `Rat.mul_comm Variance (natCast k)`
    ///    gives `Variance·k = k·Variance`. Two `Eq.subst`s transport (5) along
    ///    these to land the stated LHS `≤ TI`.
    pub fn register_hc_dual_level_lower_of_mass_bound(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.hc_dual_level_lower_of_mass_bound");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_kkl_threshold_mass_le()?;
        self.register_natcast_nonneg()?;
        self.init_boolean_analysis_order_toolkit()?; // mul_le_mul_of_nonneg_left
        self.register_rat_le_trans_proof()?; // Rat.le_trans
        self.init_rat()?; // Rat.one_mul, Rat.mul_comm
        self.init_boolean_analysis_kkl_total_influence()?; // total_influence_spectral
        self.register_subset_sum()?;
        self.register_set_size()?;
        self.register_set_size_nat()?;

        let c = LevelLowerConsts::new();
        let one_nat = Expr::app(c.nat_succ.clone(), c.nat_zero.clone());

        // mask_fn := fun S => ind(ble k |S|)·(f̂·f̂)   (the M_k integrand)
        // spectral_fn := fun S => setSize n S·(f̂·f̂)   (the TI/RHS integrand)

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (k_id, knat) = b.fresh_local(c.nat.clone());

            let var = c.variance_of(&n, &f);
            let mass = c.subset_sum_of(&n, c.mask_fn(&b, &n, &f, &knat));
            let ti = c.subset_sum_of(&n, c.spectral_fn(&b, &n, &f));
            // hypothesis: Var ≤ M_k
            let hyp_ty = c.order.rat_le(var.clone(), mass);
            // conclusion: natCast 1 · (Var · natCast k) ≤ TI
            let lhs = c.mul(c.natcast(&one_nat), c.mul(var, c.natcast(&knat)));
            let concl = c.order.rat_le(lhs, ti);

            let (h_id, _) = b.fresh_local(hyp_ty.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, hyp_ty, concl);
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let mul_le_left = Expr::const_(Name::from_string("Rat.mul_le_mul_of_nonneg_left"), vec![]);
        let natcast_nonneg = Expr::const_(Name::from_string("BoolAnalysis.natCast_nonneg"), vec![]);
        let threshold_mass_le = Expr::const_(
            Name::from_string("BoolAnalysis.kkl_threshold_mass_le"),
            vec![],
        );
        let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);
        let one_mul = Expr::const_(Name::from_string("Rat.one_mul"), vec![]);
        let mul_comm = Expr::const_(Name::from_string("Rat.mul_comm"), vec![]);

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (k_id, knat) = b.fresh_local(c.nat.clone());

            let var = c.variance_of(&n, &f);
            let mask = c.mask_fn(&b, &n, &f, &knat);
            let mass = c.subset_sum_of(&n, mask);
            // `ti_real` is TotalInfluence n f (the RHS of kkl_threshold_mass_le);
            // `ti` is the spectral subsetSum (the stated conclusion RHS). They
            // are bridged by `total_influence_spectral` at the very end.
            let ti_real = c.total_influence_of(&n, &f);
            let ti = c.subset_sum_of(&n, c.spectral_fn(&b, &n, &f));
            let kcast = c.natcast(&knat);

            // hypothesis binder h_mass : Var ≤ M_k
            let hyp_ty = c.order.rat_le(var.clone(), mass.clone());
            let (hmass_id, hmass) = b.fresh_local(hyp_ty.clone());

            // h_kpos : 0 ≤ natCast k
            let h_kpos = Expr::app(natcast_nonneg.clone(), knat.clone());

            // h3 : natCast k · Var ≤ natCast k · M_k
            //   mul_le_mul_of_nonneg_left (natCast k) Var M_k h_mass h_kpos
            let h3 = Expr::apps(
                mul_le_left.clone(),
                [
                    kcast.clone(),
                    var.clone(),
                    mass.clone(),
                    hmass.clone(),
                    h_kpos,
                ],
            );

            // h4 : natCast k · M_k ≤ TotalInfluence   (kkl_threshold_mass_le n f k)
            let h4 = Expr::apps(
                threshold_mass_le.clone(),
                [n.clone(), f.clone(), knat.clone()],
            );

            // h5 : natCast k · Var ≤ TotalInfluence   (le_trans of h3, h4)
            let k_var = c.mul(kcast.clone(), var.clone());
            let k_mass = c.mul(kcast.clone(), mass.clone());
            let h5 = Expr::apps(
                le_trans.clone(),
                [k_var.clone(), k_mass, ti_real.clone(), h3, h4],
            );

            // Now transport the LHS:  natCast 1 · (Var · natCast k) → natCast k · Var.
            // var_k := Var · natCast k
            let var_k = c.mul(var.clone(), kcast.clone());
            // one_var_k := natCast 1 · (Var · natCast k)   (the stated LHS)
            let one_var_k = c.mul(c.natcast(&one_nat), var_k.clone());

            // h_comm : Var · natCast k = natCast k · Var   (Rat.mul_comm Var (natCast k))
            let h_comm = Expr::apps(mul_comm.clone(), [var.clone(), kcast.clone()]);
            // subst h5 (: k·Var ≤ TI) along (symm h_comm : k·Var = Var·k)?
            // Cleaner: transport h5 backwards. We want goal `one_var_k ≤ TI`.
            // Step A: from h5 : k·Var ≤ TI, get  var_k ≤ TI   via subst with
            //   motive (t => t ≤ TI), a := k·Var, b := var_k, h_eq := symm h_comm.
            let motive_le_ti = |x: &LevelLowerConsts, parent: &EnvDeclBuilder, ti: &Expr| -> Expr {
                let mut m = EnvDeclBuilder::child_of(parent);
                let (t_id, t) = m.fresh_local(x.rat());
                let body = x.order.rat_le(t, ti.clone());
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, x.rat(), body))
            };
            // symm h_comm : natCast k · Var = Var · natCast k
            let h_comm_symm =
                c.order
                    .symm(var_k.clone(), c.mul(kcast.clone(), var.clone()), h_comm);
            let h_var_k = c.order.subst(
                motive_le_ti(&c, &b, &ti_real),
                c.mul(kcast.clone(), var.clone()),
                var_k.clone(),
                h_comm_symm,
                h5,
            );

            // Step B: from var_k ≤ TI_real, get one_var_k ≤ TI_real via subst
            //   along symm (Rat.one_mul var_k) : var_k = 1·var_k (≡ natCast 1 · var_k).
            // h_one : 1·var_k = var_k    (Rat.one_mul var_k)
            let h_one = Expr::app(one_mul.clone(), var_k.clone());
            // subst (motive t => t ≤ TI_real) (a := var_k) (b := one_var_k)
            //       (symm h_one : var_k = 1·var_k ≡ var_k = one_var_k) (h_var_k)
            //   yields one_var_k ≤ TI_real.
            let h_one_symm = c.order.symm(one_var_k.clone(), var_k.clone(), h_one);
            let h_one_var_k = c.order.subst(
                motive_le_ti(&c, &b, &ti_real),
                var_k.clone(),
                one_var_k.clone(),
                h_one_symm,
                h_var_k,
            );

            // Step C: bridge TotalInfluence → spectral subsetSum.
            //   total_influence_spectral n f : TotalInfluence n f = subsetSum n (setSize·f̂²)
            // subst (motive t => one_var_k ≤ t) (a := TI_real) (b := ti)
            //       (total_influence_spectral n f) (h_one_var_k) : one_var_k ≤ ti.
            let tis = Expr::apps(
                Expr::const_(
                    Name::from_string("BoolAnalysis.total_influence_spectral"),
                    vec![],
                ),
                [n.clone(), f.clone()],
            );
            let motive_lhs_le = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat());
                let mbody = c.order.rat_le(one_var_k.clone(), t);
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), mbody))
            };
            let body = c
                .order
                .subst(motive_lhs_le, ti_real.clone(), ti.clone(), tis, h_one_var_k);

            let e = b.mk_lam(hmass_id, BinderInfo::Default, hyp_ty, body);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
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

    /// (1) `BoolAnalysis.kkl_threshold_mass_le :
    ///   ∀ (n) (f : BoolFn n) (kNat : Nat),
    ///     Rat.le (Rat.mul (natCast kNat)
    ///                     (subsetSum n (fun S => ind(ble kNat |S|)·(f̂·f̂))))
    ///            (TotalInfluence n f)`.
    ///
    /// The scalar-pulled-out form of `kkl_threshold_influence`: `k·M_k ≤ I[f]`
    /// with `M_k = Σ_{|S|≥k} f̂(S)²`. Lands the exact LHS the
    /// `hc_dual_level_lower` chain consumes (see module docs).
    pub fn register_kkl_threshold_mass_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.kkl_threshold_mass_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_kkl_threshold_influence()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_subset_sum()?;
        self.register_set_size_nat()?;

        let c = LevelLowerConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (k_id, knat) = b.fresh_local(c.nat.clone());

            let mass = c.subset_sum_of(&n, c.mask_fn(&b, &n, &f, &knat));
            let lhs = c.mul(c.natcast(&knat), mass);
            let concl = c.order.rat_le(lhs, c.total_influence_of(&n, &f));

            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let threshold_influence = Expr::const_(
            Name::from_string("BoolAnalysis.kkl_threshold_influence"),
            vec![],
        );
        let subset_sum_smul =
            Expr::const_(Name::from_string("BoolAnalysis.subsetSum_smul"), vec![]);

        // value: fun (n) (f) (kNat) =>
        //   let mask := fun S => ind(ble k |S|)·(f̂·f̂)
        //   a := subsetSum n (fun S => natCast k · mask S)     -- threshold LHS
        //   b := natCast k · subsetSum n mask                  -- pulled-out form
        //   h_eq : a = b   := subsetSum_smul n (natCast k) mask
        //   h_a  : a ≤ TI  := kkl_threshold_influence n f k
        //   subst (motive t => t ≤ TI) a b h_eq h_a : b ≤ TI
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (k_id, knat) = b.fresh_local(c.nat.clone());

            let mask = c.mask_fn(&b, &n, &f, &knat);
            let ti = c.total_influence_of(&n, &f);

            // a : the threshold-influence LHS (scalar folded inside)
            let a = c.subset_sum_of(&n, c.scaled_fn(&b, &n, &f, &knat));
            // b : the pulled-out form natCast k · subsetSum n mask
            let bb = c.mul(c.natcast(&knat), c.subset_sum_of(&n, mask.clone()));

            // h_eq : a = b  := subsetSum_smul n (natCast k) mask
            let h_eq = Expr::apps(
                subset_sum_smul.clone(),
                [n.clone(), c.natcast(&knat), mask.clone()],
            );

            // h_a : a ≤ TI  := kkl_threshold_influence n f kNat
            let h_a = Expr::apps(
                threshold_influence.clone(),
                [n.clone(), f.clone(), knat.clone()],
            );

            // motive t => t ≤ TI
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat());
                let body = c.order.rat_le(t, ti.clone());
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat(), body))
            };

            let body = c.order.subst(motive, a, bb, h_eq, h_a);

            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
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
        env.init_boolean_analysis_kkl_levellower()
            .expect("init_boolean_analysis_kkl_levellower");
        env.init_boolean_analysis_kkl_levellower()
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
            "{name} closure must be empty"
        );
    }

    #[test]
    fn test_kkl_threshold_mass_le_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.kkl_threshold_mass_le");
    }

    #[test]
    fn test_natcast_nonneg_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.natCast_nonneg");
    }

    #[test]
    fn test_hc_dual_level_lower_of_mass_bound_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.hc_dual_level_lower_of_mass_bound");
    }

    #[test]
    fn test_hc_dual_level_lower_k1_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.hc_dual_level_lower_k1");
    }
}
