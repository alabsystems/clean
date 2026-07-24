// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KKL endgame — §5C step 1: the total-influence spectral identity.
//!
//! ```text
//! BoolAnalysis.total_influence_spectral : ∀ (n : Nat) (f : BoolFn n),
//!   TotalInfluence n f
//!     = subsetSum n (fun S => Rat.mul (setSize n S)
//!                                     (Rat.mul (FourierCoefficient n f S)
//!                                              (FourierCoefficient n f S)))
//! ```
//!
//! i.e. `I[f] = Σ_S |S|·f̂(S)²` — the textbook identity that total influence
//! equals the degree-weighted Fourier mass (O'Donnell, *Analysis of Boolean
//! Functions*, Thm. 2.27 / the "Σ_i Inf_i = Σ_S |S| f̂(S)²" identity). This is
//! the first analytic brick of the KKL `hc_dual_total` chain (see
//! `designs/2026-06-12-kkl-endgame-worked-chain.md`, §5C step 1).
//!
//! ## Proof (constructive, empty domain-axiom closure)
//!
//! `TotalInfluence n f` δ-unfolds (reducible Definition) to
//! `Fin.sum n (fun i => Influence n f i)`. With `w S := f̂(S)·f̂(S)`:
//!
//! 1. **`Fin.sum_congr`** rewrites each summand `Influence n f i` to
//!    `subsetSum n (fun S => ind(S i)·w S)` via `influence_fourier n f i` (whose
//!    type `influence_fourier_helper n f i` is reducibly the `Eq`
//!    `Influence n f i = subsetSum n (fun S => ind(S i)·(f̂ S·f̂ S))`). This turns
//!    `Σ_i Influence n f i` into `Σ_i subsetSum n (fun S => ind(S i)·w S)`.
//! 2. **`subsetSum_double_count n w`** (the K2a Fubini double-count) gives
//!    `Σ_i subsetSum n (fun S => ind(S i)·w S) = subsetSum n (fun S => setSize n S·w S)`.
//! 3. `Eq.trans` of (1) and (2) closes the goal; the LHS `Σ_i Influence n f i`
//!    is def-eq to `TotalInfluence n f` (reducible).
//!
//! Every dependency (`influence_fourier`, `subsetSum_double_count`,
//! `Fin.sum_congr`, `TotalInfluence`, `setSize`, `FourierCoefficient`) is
//! `Constructive` with empty closure, so `total_influence_spectral` is too.
//! No axiom is added or removed. Idempotent.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the total-influence spectral identity.
struct TiConsts {
    nat: Expr,
    rat: Expr,
    rat_mul: Expr,
    fin: Expr,
    fin_sum: Expr,
    fin_sum_congr: Expr,
    subset_sum: Expr,
    set_size: Expr,
    influence: Expr,
    total_influence: Expr,
    fourier: Expr,
    influence_fourier: Expr,
    double_count: Expr,
    ind: Expr,
    bool_fn: Expr,
    hcpoint: Expr,
    eq1: Expr,
    eq_trans: Expr,
}

impl TiConsts {
    fn new() -> Self {
        let u1 = Level::succ(Level::zero());
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            rat_mul: Expr::const_(Name::from_string("Rat.mul"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            fin_sum: Expr::const_(Name::from_string("Fin.sum"), vec![]),
            fin_sum_congr: Expr::const_(Name::from_string("Fin.sum_congr"), vec![]),
            subset_sum: Expr::const_(Name::from_string("BoolAnalysis.subsetSum"), vec![]),
            set_size: Expr::const_(Name::from_string("BoolAnalysis.setSize"), vec![]),
            influence: Expr::const_(Name::from_string("BoolAnalysis.Influence"), vec![]),
            total_influence: Expr::const_(Name::from_string("BoolAnalysis.TotalInfluence"), vec![]),
            fourier: Expr::const_(Name::from_string("BoolAnalysis.FourierCoefficient"), vec![]),
            influence_fourier: Expr::const_(
                Name::from_string("BoolAnalysis.influence_fourier"),
                vec![],
            ),
            double_count: Expr::const_(
                Name::from_string("BoolAnalysis.subsetSum_double_count"),
                vec![],
            ),
            ind: Expr::const_(Name::from_string("BoolAnalysis.ind"), vec![]),
            bool_fn: Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]),
            hcpoint: Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
            eq1: Expr::const_(Name::from_string("Eq"), vec![u1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![u1]),
        }
    }

    fn bool_fn_of(&self, n: &Expr) -> Expr {
        Expr::app(self.bool_fn.clone(), n.clone())
    }
    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn mul(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, b])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn fourier_of(&self, n: &Expr, f: &Expr, s: &Expr) -> Expr {
        Expr::apps(self.fourier.clone(), [n.clone(), f.clone(), s.clone()])
    }
    /// `w S := f̂(S)·f̂(S)` — the Fourier-square weight.
    fn weight_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let coeff = self.fourier_of(n, f, &s);
        let body = self.mul(coeff.clone(), coeff);
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (S : HCPoint n) => ind (S i) · (f̂ S · f̂ S)` — per-coordinate gate sum
    /// integrand (the `influence_fourier` RHS at coordinate `i`).
    fn coord_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr, i: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let s_i = Expr::app(s.clone(), i.clone());
        let gate = Expr::app(self.ind.clone(), s_i);
        let coeff = self.fourier_of(n, f, &s);
        let w = self.mul(coeff.clone(), coeff);
        let body = self.mul(gate, w);
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (S : HCPoint n) => setSize n S · (f̂ S · f̂ S)` — the RHS integrand.
    fn size_fn(&self, parent: &EnvDeclBuilder, n: &Expr, f: &Expr) -> Expr {
        let mut ch = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (s_id, s) = ch.fresh_local(hcp.clone());
        let size = Expr::apps(self.set_size.clone(), [n.clone(), s.clone()]);
        let coeff = self.fourier_of(n, f, &s);
        let w = self.mul(coeff.clone(), coeff);
        let body = self.mul(size, w);
        ch.finish_child(ch.mk_lam(s_id, BinderInfo::Default, hcp, body))
    }
}

impl Environment {
    /// Register `BoolAnalysis.total_influence_spectral`. Idempotent;
    /// kernel-checked, constructive, empty admitted-axiom closure.
    pub fn init_boolean_analysis_kkl_total_influence(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.total_influence_spectral");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // Deps: influence_fourier (with helper), the double-count, Fin.sum_congr,
        // TotalInfluence / setSize / FourierCoefficient carriers.
        // `init_boolean_analysis` registers Influence, TotalInfluence,
        // FourierCoefficient, ind, AND the influence_fourier theorem (+ helper).
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum_double_count()?;
        self.register_subset_sum()?;
        self.register_set_size()?;
        self.init_fin_sum()?; // Fin.sum_congr
                              // `init_boolean_analysis` may now register this theorem transitively (the
                              // KKL-finish proof chain is wired into the always-on init); re-check after
                              // the deps so the registration stays idempotent.
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = TiConsts::new();
        let ty = build_type(&c);
        let value = build_proof(&c);

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }
}

/// Type:
/// `∀ (n) (f : BoolFn n),
///    TotalInfluence n f
///      = subsetSum n (fun S => setSize n S · (f̂ S · f̂ S))`.
fn build_type(c: &TiConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());

    let lhs = Expr::apps(c.total_influence.clone(), [n.clone(), f.clone()]);
    let rhs = Expr::apps(c.subset_sum.clone(), [n.clone(), c.size_fn(&b, &n, &f)]);
    let body = c.eq_rat(lhs, rhs);

    let e = b.mk_pi(f_id, BinderInfo::Default, bool_fn_n, body);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Proof:
/// `Eq.trans (Fin.sum_congr n (fun i => Influence n f i) (fun i => subsetSum n (coord_fn i)) per_i)
///           (subsetSum_double_count n w)`.
///
/// The `Fin.sum n (fun i => Influence n f i)` LHS of step 1 is def-eq to
/// `TotalInfluence n f` (reducible). The double-count RHS is the goal RHS.
fn build_proof(c: &TiConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let bool_fn_n = c.bool_fn_of(&n);
    let (f_id, f) = b.fresh_local(bool_fn_n.clone());

    // The Fin.sum summands:
    //   lhs_fn i := Influence n f i
    //   mid_fn i := subsetSum n (coord_fn i)
    let lhs_fn = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let body = Expr::apps(c.influence.clone(), [n.clone(), f.clone(), i]);
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };
    let mid_fn = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let g = c.coord_fn(&ch, &n, &f, &i);
        let body = Expr::apps(c.subset_sum.clone(), [n.clone(), g]);
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };

    // per_i : ∀ i, Influence n f i = subsetSum n (coord_fn i)
    //   := fun i => influence_fourier n f i
    // (the result type `influence_fourier_helper n f i` is reducibly that Eq.)
    let per_i = {
        let mut ch = EnvDeclBuilder::child_of(&b);
        let fin_n = c.fin_of(&n);
        let (i_id, i) = ch.fresh_local(fin_n.clone());
        let body = Expr::apps(c.influence_fourier.clone(), [n.clone(), f.clone(), i]);
        ch.finish_child(ch.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    };

    // step1 : Fin.sum n lhs_fn = Fin.sum n mid_fn
    //   := Fin.sum_congr n lhs_fn mid_fn per_i
    let step1 = Expr::apps(
        c.fin_sum_congr.clone(),
        [n.clone(), lhs_fn.clone(), mid_fn.clone(), per_i],
    );

    // step2 : Fin.sum n mid_fn = subsetSum n (size_fn)
    //   := subsetSum_double_count n w
    // (Fin.sum n mid_fn = Σ_i subsetSum n (fun S => ind(S i)·w S) is the
    //  double-count LHS; size_fn is its RHS.)
    let w = c.weight_fn(&b, &n, &f);
    let step2 = Expr::apps(c.double_count.clone(), [n.clone(), w]);

    // Endpoints for Eq.trans (all over Rat):
    //   A := Fin.sum n lhs_fn   (≡ TotalInfluence n f, the goal LHS)
    //   B := Fin.sum n mid_fn
    //   C := subsetSum n (size_fn)   (the goal RHS)
    let big_a = Expr::apps(c.fin_sum.clone(), [n.clone(), lhs_fn]);
    let big_b = Expr::apps(c.fin_sum.clone(), [n.clone(), mid_fn]);
    let big_c = Expr::apps(c.subset_sum.clone(), [n.clone(), c.size_fn(&b, &n, &f)]);

    let body = Expr::apps(
        c.eq_trans.clone(),
        [c.rat.clone(), big_a, big_b, big_c, step1, step2],
    );

    let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, body);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_total_influence_spectral_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.init_boolean_analysis_kkl_total_influence()
            .expect("init_boolean_analysis_kkl_total_influence");
        env.init_boolean_analysis_kkl_total_influence()
            .expect("idempotent");
        let name = Name::from_string("BoolAnalysis.total_influence_spectral");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("total_influence_spectral proof must check against its type");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
    }
}
