// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Friedgut roadmap — RUNG 3: `high_degree_mass_le`, the level-Markov
//! inequality `(d+1)·M_{≥d+1}[f] ≤ I[f]` as a banked constructive brick.
//!
//! ## What this rung proves
//!
//! ```text
//! BoolAnalysis.high_degree_mass_le :
//!   ∀ (n d : Nat) (f : BoolFn n),
//!     Nat.le (Nat.pow 2 (d+1)) n →
//!       Rat.le
//!         (Rat.mul (natCast (d+1))
//!                  (subsetSum n (fun S =>
//!                     Rat.mul (ind (Nat.ble (d+1) (setSizeNat n S)))
//!                             (Rat.mul (FourierCoefficient n f S)
//!                                      (FourierCoefficient n f S)))))
//!         (TotalInfluence n f)
//! ```
//!
//! i.e. `(d+1)·M_{≥d+1}[f] ≤ I[f]`, where
//! `M_{≥d+1}[f] := Σ_{|S| ≥ d+1} f̂(S)²` is the high-degree (level-`≥ d+1`)
//! Fourier mass. This is the **level-Markov inequality** for the spectral
//! sample (O'Donnell, *Analysis of Boolean Functions*, the `Σ_S |S| f̂(S)² = I[f]`
//! identity combined with the trivial counting bound `(d+1)·[|S| ≥ d+1] ≤ |S|`):
//! a set surviving the `|S| ≥ d+1` mask contributes degree `|S| ≥ d+1` to the
//! total-influence sum, so the masked mass can be scaled by the factor `d+1`.
//! It is the first banked brick toward the full Friedgut junta assembly (see
//! `designs/2026-06-13-friedgut-junta-theorem-roadmap.md`, rung 3); this rung
//! does NOT retire the `kkl_inequality` / `friedgut_boolean` admitted axioms —
//! those need the remaining assembly — so it does not reduce the axiom census.
//!
//! ## The `2^(d+1) ≤ n` premise and the `n < d+1` regime (honest soundness note)
//!
//! The premise `Nat.le (Nat.pow 2 (d+1)) n` is inherited verbatim from the
//! `dyadic_level_mass_le` brick (its dyadic-admissible-level framing). The
//! inequality is in fact unconditionally true: when `n < d+1` every set
//! `S : HCPoint n` has `|S| ≤ n < d+1`, so the `|S| ≥ d+1` mask is identically
//! `false`, the high-degree mass `M_{≥d+1}[f]` is `0`, and the bound
//! `(d+1)·0 ≤ I[f]` holds trivially (since `I[f] ≥ 0`). Carrying the premise is
//! therefore a SOUND WEAKENING — the bound is genuinely true, never vacuously
//! satisfied by a stub carrier; it is just not stated in its tightest
//! premise-free form. This is the standard level-Markov form, documented here
//! honestly rather than masqueraded.
//!
//! ## Proof (constructive, empty admitted-axiom closure)
//!
//! Pure transport assembly of two already-landed constructive bricks — no new
//! proof content:
//!
//! 1. **`dyadic_level_mass_le n (d+1) w hw hk`** with the Fourier-square weight
//!    `w S := f̂(S)·f̂(S)` gives
//!    `(d+1)·Σ_S ind(|S| ≥ d+1)·w S  ≤  Σ_S |S|·w S`, once its non-negativity
//!    hypothesis `hw : ∀ S, 0 ≤ w S` is discharged by
//!    `fun S => Rat.sq_nonneg (f̂ S)` (`0 ≤ (f̂ S)·(f̂ S)`). The premise
//!    `hk : Nat.le (Nat.pow 2 (d+1)) n` is the theorem's own argument.
//! 2. **`total_influence_spectral n f`** is the identity
//!    `TotalInfluence n f = Σ_S |S|·(f̂ S·f̂ S)`. Its RHS `Σ_S |S|·(f̂ S·f̂ S)`
//!    is SYNTACTICALLY the RHS of (1) (the `dyadic_level_mass_le` spectral
//!    integrand `fun S => setSize n S · w S` at `w := f̂·f̂` is exactly the
//!    `total_influence_spectral` integrand `fun S => setSize n S · (f̂ S·f̂ S)`).
//! 3. **`Eq.subst`** (motive `t ↦ LHS ≤ t`) transports (1) backward along
//!    `Eq.symm (total_influence_spectral n f)`, rewriting the RHS
//!    `Σ_S |S|·w S` to `TotalInfluence n f`, yielding the stated bound.
//!
//! Every dependency (`dyadic_level_mass_le`, `total_influence_spectral`,
//! `Rat.sq_nonneg`, `Eq.subst`, `Eq.symm`) is `Constructive` with empty
//! admitted-axiom closure, so this rung is too. No axiom is added or removed.
//! Idempotent.

use super::boolean_analysis_order_toolkit::OrderConsts;
use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the high-degree level-Markov rung.
struct HighDegreeConsts {
    order: OrderConsts,
    nat: Expr,
    rat: Expr,
    bool_fn: Expr,
    hcpoint: Expr,
    ind: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    fourier: Expr,
    total_influence: Expr,
    nat_ble: Expr,
    nat_succ: Expr,
    nat_zero: Expr,
    nat_pow: Expr,
    nat_le: Expr,
    u1: Level,
}

impl HighDegreeConsts {
    fn new() -> Self {
        Self {
            order: OrderConsts::new(),
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_fn: Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            set_size_nat: Expr::const_(Name::from_string("BoolAnalysis.setSizeNat"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            fourier: Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]),
            total_influence: Expr::const_(Name::from_string("BoolAnalysis.TotalInfluence"), vec![]),
            nat_ble: Expr::const_(Name::from_string("Nat.ble"), vec![]),
            nat_succ: Expr::const_(Name::from_string("Nat.succ"), vec![]),
            nat_zero: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            nat_pow: Expr::const_(Name::from_string("Nat.pow"), vec![]),
            nat_le: Expr::const_(Name::from_string("Nat.le"), vec![]),
            u1: Level::succ(Level::zero()),
        }
    }

    fn rat_ty(&self) -> Expr {
        self.rat.clone()
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        self.order.mul(a, b)
    }
    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn ind_of(&self, bit: Expr) -> Expr {
        Expr::app(self.ind.clone(), bit)
    }
    fn set_size_nat_of(&self, n: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), s.clone()])
    }
    fn subset_sum_of(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    fn total_influence_of(&self, n: &Expr, f: &Expr) -> Expr {
        Expr::apps(self.total_influence.clone(), [n.clone(), f.clone()])
    }
    /// `Nat.ble k m`.
    fn ble(&self, k: Expr, m: Expr) -> Expr {
        Expr::apps(self.nat_ble.clone(), [k, m])
    }
    fn succ(&self, n: Expr) -> Expr {
        Expr::app(self.nat_succ.clone(), n)
    }
    fn one_nat(&self) -> Expr {
        self.succ(self.nat_zero.clone())
    }
    /// `Nat.pow 2 k`.
    fn pow2(&self, k: &Expr) -> Expr {
        let two = self.succ(self.one_nat());
        Expr::apps(self.nat_pow.clone(), [two, k.clone()])
    }
    fn nat_le_of(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.nat_le.clone(), [a, b])
    }
    /// `Rat.mk (Int.ofNat m) 1` — the `Nat → Rat` cast `natCast m`.
    ///
    /// Built EXACTLY as `dyadic_level_mass_le` builds its `natCast`, so the
    /// instantiation at `k := d+1` is syntactically identical to the brick's
    /// internal scalar.
    fn natcast(&self, m: &Expr) -> Expr {
        let of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [Expr::app(of_nat, m.clone()), self.one_nat()],
        )
    }
    /// `w S := f̂(S)·f̂(S)` — the Fourier-square weight (matches the
    /// `total_influence_spectral` weight and the `dyadic_level_mass_le` `w`).
    fn weight_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let coeff = self.fourier_of(n, f, &s);
        let body = self.mul(coeff.clone(), coeff);
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// The masked level-`≥k` integrand `fun S => ind (ble k |S|) · (f̂ S·f̂ S)`,
    /// built EXACTLY as `dyadic_level_mass_le::mask_fn` at `w := f̂·f̂`.
    fn mask_fn(&self, parent: &EnvDeclBuilder, n: &Expr, knat: &Expr, f: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let bit = self.ble(knat.clone(), self.set_size_nat_of(n, &s));
        let coeff = self.fourier_of(n, f, &s);
        let w_s = self.mul(coeff.clone(), coeff);
        let body = self.mul(self.ind_of(bit), w_s);
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// The `dyadic_level_mass_le` RHS integrand `fun S => setSize n S · (f̂ S·f̂ S)`
    /// — built via `total_influence_spectral`'s `size_fn` shape so the two
    /// `subsetSum` terms are syntactically equal.
    fn spectral_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let set_size = Expr::apps(
            Expr::const_(Name::from_string("BoolAnalysis.setSize"), vec![]),
            [n.clone(), s.clone()],
        );
        let coeff = self.fourier_of(n, f, &s);
        let w_s = self.mul(coeff.clone(), coeff);
        let body = self.mul(set_size, w_s);
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

impl Environment {
    /// Register the Friedgut rung-3 high-degree level-Markov brick. Idempotent.
    pub fn init_boolean_analysis_high_degree_mass(&mut self) -> Result<(), EnvError> {
        self.register_high_degree_mass_le()?;
        Ok(())
    }

    /// `BoolAnalysis.high_degree_mass_le :
    ///   ∀ (n d : Nat) (f : BoolFn n),
    ///     Nat.le (Nat.pow 2 (d+1)) n →
    ///       Rat.le ((d+1) · Σ_S ind(|S| ≥ d+1)·f̂(S)²) (TotalInfluence n f)`.
    ///
    /// The level-Markov inequality `(d+1)·M_{≥d+1}[f] ≤ I[f]`, assembled by
    /// transport from `dyadic_level_mass_le` (at `k := d+1`, `w := f̂·f̂`) and
    /// `total_influence_spectral`. See module docs for the honest `n < d+1`
    /// (mass-`0`) soundness note and the constructive proof sketch.
    pub fn register_high_degree_mass_le(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.high_degree_mass_le");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Bricks (each idempotent): the dyadic counting bound, the
        // total-influence spectral identity, and the square-nonneg order lemma.
        self.init_boolean_analysis_dyadic_level_sum()?; // dyadic_level_mass_le
        self.init_boolean_analysis_kkl_total_influence()?; // total_influence_spectral
        self.init_boolean_analysis_order_toolkit()?; // Rat.sq_nonneg

        let c = HighDegreeConsts::new();

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let knat = c.succ(d.clone()); // d+1
                                          // hk : Nat.le (Nat.pow 2 (d+1)) n
            let hk_ty = c.nat_le_of(c.pow2(&knat), n.clone());

            let mass = c.subset_sum_of(&n, c.mask_fn(&b, &n, &knat, &f));
            let lhs = c.mul(c.natcast(&knat), mass);
            let rhs = c.total_influence_of(&n, &f);
            let concl = c.order.rat_le(lhs, rhs);

            let (hk_id, _) = b.fresh_local(hk_ty.clone());
            let e = b.mk_pi(hk_id, BinderInfo::Default, hk_ty, concl);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(d_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let dyadic = Expr::const_(
            Name::from_string("BoolAnalysis.dyadic_level_mass_le"),
            vec![],
        );
        let ti_spectral = Expr::const_(
            Name::from_string("BoolAnalysis.total_influence_spectral"),
            vec![],
        );
        let sq_nonneg = Expr::const_(Name::from_string("Rat.sq_nonneg"), vec![]);

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());

            let knat = c.succ(d.clone()); // d+1
            let hk_ty = c.nat_le_of(c.pow2(&knat), n.clone());
            let (hk_id, hk) = b.fresh_local(hk_ty.clone());

            // w := fun S => f̂(S)·f̂(S)   (the dyadic `w`, the TI-spectral weight)
            let w = c.weight_fn(&b, &n, &f);

            // hw : ∀ S, 0 ≤ w S := fun S => Rat.sq_nonneg (f̂ S)
            let hw = {
                let mut ch = EnvDeclBuilder::child_of(&b);
                let hcp = c.hcpoint_of(&n);
                let (s_id, s) = ch.fresh_local(hcp.clone());
                let coeff = c.fourier_of(&n, &f, &s);
                let body = Expr::app(sq_nonneg.clone(), coeff);
                ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
            };

            // dyad : (d+1)·Σ_S ind(|S| ≥ d+1)·w S ≤ Σ_S |S|·w S
            //   := dyadic_level_mass_le n (d+1) w hw hk
            let dyad = Expr::apps(
                dyadic.clone(),
                [n.clone(), knat.clone(), w.clone(), hw, hk.clone()],
            );

            // The shared endpoints of the rewrite (over Rat):
            //   lhs   := (d+1)·Σ_S ind(|S| ≥ d+1)·(f̂ S·f̂ S)   (the goal LHS)
            //   a     := Σ_S |S|·(f̂ S·f̂ S)   (dyadic RHS = TI-spectral RHS)
            //   bb    := TotalInfluence n f   (the goal RHS)
            let lhs = c.mul(
                c.natcast(&knat),
                c.subset_sum_of(&n, c.mask_fn(&b, &n, &knat, &f)),
            );
            let big_a = c.subset_sum_of(&n, c.spectral_fn(&b, &n, &f));
            let big_b = c.total_influence_of(&n, &f);

            // h_ti : TotalInfluence n f = Σ_S |S|·(f̂ S·f̂ S)
            //   := total_influence_spectral n f
            let h_ti = Expr::apps(ti_spectral.clone(), [n.clone(), f.clone()]);
            // h_ti_symm : Σ_S |S|·(f̂ S·f̂ S) = TotalInfluence n f
            let h_ti_symm = c.order.symm(big_b.clone(), big_a.clone(), h_ti);

            // subst (motive t => lhs ≤ t) (a := big_a) (b := big_b) h_ti_symm dyad
            let motive = {
                let mut m = EnvDeclBuilder::child_of(&b);
                let (t_id, t) = m.fresh_local(c.rat_ty());
                let mbody = c.order.rat_le(lhs.clone(), t);
                m.finish_child(m.mk_lam(t_id, BinderInfo::Default, c.rat_ty(), mbody))
            };
            let body = c.order.subst(motive, big_a, big_b, h_ti_symm, dyad);

            let e = b.mk_lam(hk_id, BinderInfo::Default, hk_ty, body);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
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
        env.init_boolean_analysis_high_degree_mass()
            .expect("init_boolean_analysis_high_degree_mass");
        env.init_boolean_analysis_high_degree_mass()
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
    fn test_high_degree_mass_le_is_constructive_theorem() {
        let env = env();
        check_constructive(&env, "BoolAnalysis.high_degree_mass_le");
    }
}
