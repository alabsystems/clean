// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fourier analysis on the Boolean hypercube {-1,+1}^n.
//!
//! Registers kernel-level definitions and theorem axioms that complement the
//! existing KKL formalization in `boolean_analysis.rs`. Where that module
//! provides the core types (`BoolFn`, `FourierCoeff`, `FourierTransform`,
//! `Influence`, `TotalInfluence`, `Variance`) and the
//! main theorem surfaces (Parseval, influence/Fourier, total influence,
//! Bonami-Beckner, KKL), this module adds:
//!
//! **Definitions:**
//! - `fourier_coefficient` -- single coefficient accessor f^(S) for a given subset S
//! - `fourier_spectrum` -- the set/family of all Fourier coefficients
//! - `fourier_weight_at_level` -- W^k[f] = sum_{|S|=k} f^(S)^2
//!
//! **Theorems:**
//! - `noise_stability_fourier` -- S_rho[f] = sum_S rho^|S| f^(S)^2
//! - `fourier_weight_parseval` -- sum_k W^k[f] = E[f^2]
//! - `friedgut_boolean` -- Boolean f with I[f] <= K is eps-close to a 2^O(K/eps)-junta
//! - `fourier_coefficient_transform` -- f^(S) = FourierTransform(n, f, S)

use super::boolean_analysis::BoolAnalysisConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Fourier Boolean hypercube declarations.
    ///
    /// Depends on: `init_boolean_analysis()` (provides BoolFn, FourierCoeff, etc.)
    pub(crate) fn init_fourier_boolean(&mut self) -> Result<(), EnvError> {
        if self.fourier_boolean_init {
            return Ok(());
        }
        self.init_boolean_analysis()?;

        let c = BoolAnalysisConsts::new();

        // Definitions
        // `FourierCoefficient` is now a CHECKED reducible Definition registered
        // upstream by `init_boolean_analysis` (Stage-2 BoolFn redesign:
        // f̂(S) = E[(pm∘f)·χ_S] over indicator-subsets `S : HCPoint n`), so the
        // former bare-axiom registrar here is no longer needed.
        self.register_fourier_spectrum(&c)?;
        self.register_fourier_weight_at_level(&c)?;

        // Theorems (in fourier_boolean_theorems.rs)
        self.register_noise_stability_fourier_helper(&c)?;
        self.register_noise_stability_fourier(&c)?;
        self.register_fourier_weight_parseval_helper(&c)?;
        self.register_fourier_weight_parseval(&c)?;
        self.register_friedgut_boolean_helper(&c)?;
        self.register_friedgut_boolean(&c)?;
        self.register_fourier_coefficient_transform_helper(&c)?;
        self.register_fourier_coefficient_transform(&c)?;

        self.fourier_boolean_init = true;
        Ok(())
    }

    /// `FourierSpectrum (n : Nat) (f : BoolFn n) : FourierCoeff n`
    ///
    /// The family of all Fourier coefficients {f^(S) : S in P([n])}. By the
    /// module's own statement it is *equivalent to* `FourierTransform n f` —
    /// the spectrum simply IS the Fourier transform under a different name. We
    /// register it as a genuine `Declaration::Definition` carrying exactly that
    /// identity: `fun n f => FourierTransform n f`. This DISCHARGES the bare
    /// `FourierSpectrum` axiom (definitionally correct, not just type-correct).
    /// Both have type `(n) → (f : BoolFn n) → FourierCoeff n`, so the body is
    /// well-typed by construction. The closure still reaches the admitted
    /// `FourierTransform` (which genuinely needs the χ_S characters and a
    /// hypercube expectation that do not yet exist) — honest and unchanged.
    fn register_fourier_spectrum(&mut self, c: &BoolAnalysisConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.FourierSpectrum"))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let result = c.fourier_coeff_of(&n);
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, result);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        // value: fun (n : Nat) (f : BoolFn n) => FourierTransform n f
        let fourier_transform =
            Expr::const_(Name::from_string("BoolAnalysis.FourierTransform"), vec![]);
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let body = Expr::apps(fourier_transform.clone(), [n.clone(), f.clone()]);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.discharge_axiom_for_redefinition(&Name::from_string("BoolAnalysis.FourierSpectrum"));
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.FourierSpectrum"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }

    /// `FourierWeightAtLevel (n : Nat) (f : BoolFn n) (k : Nat) : Rat`
    ///
    /// Stage-2 BoolFn redesign: the Fourier weight at level `k`,
    /// `W^k[f] = Σ_{|S|=k} f̂(S)²` (O'Donnell §1.4), a genuine CHECKED reducible
    /// `Declaration::Definition`. Subsets are enumerated by their `Fin (2^n)`
    /// index (decoded to the indicator `S = hcDecode n j`), gated by a popcount
    /// test `|S| = k`:
    ///
    /// ```text
    /// FourierWeightAtLevel n f k :=
    ///   Fin.sum (Nat.pow 2 n) (fun (j : Fin (2^n)) =>
    ///     let S := hcDecode n j in
    ///     Rat.mul (ind (Nat.beq (Fin.sumNat n (fun i => indNat (S i))) k))   -- |S| = k ?
    ///             (Rat.mul (FourierCoefficient n f S) (FourierCoefficient n f S)))
    /// ```
    ///
    /// where `|S| = Fin.sumNat n (fun i => indNat (S i))` is the popcount of the
    /// indicator (true coordinates), `ind (Nat.beq |S| k)` is the `{0,1}`
    /// level-restriction gate, and the squared coefficient is `f̂(S)²`. Built over
    /// the Stage-1 `Fin.sum` / `Fin.sumNat` / `hcDecode` and the defined
    /// `FourierCoefficient` / `ind`. DISCHARGES the bare `FourierWeightAtLevel`
    /// axiom, shrinking the TCB by one.
    fn register_fourier_weight_at_level(&mut self, c: &BoolAnalysisConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("BoolAnalysis.FourierWeightAtLevel"))
            .is_some_and(|info| matches!(info.kind, crate::env::types::ConstantKind::Definition))
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, _) = b.fresh_local(bool_fn_n.clone());
            let (k_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), c.rat.clone());
            let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        let fin_sum = Expr::const_(Name::from_string("Fin.sum"), vec![]);
        let fin_sum_nat = Expr::const_(Name::from_string("Fin.sumNat"), vec![]);
        let nat_pow = Expr::const_(Name::from_string("Nat.pow"), vec![]);
        let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
        let hc_decode = Expr::const_(Name::from_string("BoolAnalysis.hcDecode"), vec![]);
        let ind = Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]);
        let fourier_coefficient =
            Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let bool_rec = Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        );
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ.clone(), nat_zero.clone());
        let two = Expr::app(nat_succ.clone(), nat_one.clone());
        let pow2 = |n: &Expr| Expr::apps(nat_pow.clone(), [two.clone(), n.clone()]);
        // `fun (_ : Bool) => Nat` — the Nat-valued motive for indNat.
        let nat_motive = || Expr::lam(BinderInfo::Default, c.bool_.clone(), c.nat.clone());

        let value = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let bool_fn_n = c.bool_fn_of(&n);
            let (f_id, f) = b.fresh_local(bool_fn_n.clone());
            let (k_id, k) = b.fresh_local(c.nat.clone());

            // summand: fun (j : Fin (2^n)) => gate · f̂(S)²  where S = hcDecode n j
            let summand = {
                let fin_pow = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), pow2(&n));
                let (j_id, j) = b.fresh_local(fin_pow.clone());
                let s = Expr::apps(hc_decode.clone(), [n.clone(), j]);

                // popcount = Fin.sumNat n (fun i => @Bool.rec (fun _=>Nat) 0 1 (S i))
                let popcount = {
                    let fin_n =
                        Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), n.clone());
                    let (i_id, i) = b.fresh_local(fin_n.clone());
                    let s_i = Expr::app(s.clone(), i);
                    let ind_nat = Expr::apps(
                        bool_rec.clone(),
                        [nat_motive(), nat_zero.clone(), nat_one.clone(), s_i],
                    );
                    let count_fn = b.mk_lam(i_id, BinderInfo::Default, fin_n, ind_nat);
                    Expr::apps(fin_sum_nat.clone(), [n.clone(), count_fn])
                };

                // gate = ind (Nat.beq popcount k)
                let same = Expr::apps(nat_beq.clone(), [popcount, k.clone()]);
                let gate = Expr::app(ind.clone(), same);

                // f̂(S)² = Rat.mul (FourierCoefficient n f S) (FourierCoefficient n f S)
                let coeff = Expr::apps(fourier_coefficient.clone(), [n.clone(), f.clone(), s]);
                let coeff_sq = Expr::apps(rat_mul.clone(), [coeff.clone(), coeff]);

                let term = Expr::apps(rat_mul.clone(), [gate, coeff_sq]);
                b.mk_lam(j_id, BinderInfo::Default, fin_pow, term)
            };

            let body = Expr::apps(fin_sum.clone(), [pow2(&n), summand]);
            let e = b.mk_lam(k_id, BinderInfo::Default, c.nat.clone(), body);
            let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
            let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };

        self.discharge_axiom_for_redefinition(&Name::from_string(
            "BoolAnalysis.FourierWeightAtLevel",
        ));
        self.add_decl(Declaration::Definition {
            name: Name::from_string("BoolAnalysis.FourierWeightAtLevel"),
            level_params: vec![],
            type_: ty,
            value,
            is_reducible: true,
        })
    }
}
