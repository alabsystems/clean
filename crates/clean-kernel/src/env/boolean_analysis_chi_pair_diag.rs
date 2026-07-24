// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! 2-fold character orthogonality in DIAGONAL-VALUE form — the spectral-route
//! keystone the noise semigroup turns on.
//!
//! The on-branch `subsetSum_chi_quad_diag`
//! (`boolean_analysis_chi_quad_diag.rs`) lands the 4-fold diagonal value
//! `Σ_x (χ_{S1}·χ_{S2})·(χ_{S3}·χ_{S4}) = 2^n·ind((S1ΔS2)Δ(S3ΔS4) = ∅)`. The
//! NOISE SEMIGROUP (`noiseDensityW_compose`) only needs the simpler 2-fold
//! version
//!
//! ```text
//! BoolAnalysis.subsetSum_chi_pair_diag :
//!   ∀ (n : Nat) (S T : HCPoint n),
//!     subsetSum n (fun x => χ_S(x)·χ_T(x))
//!       = cube n · ind (Nat.beq (setSizeNat n (S Δ T)) 0)
//! ```
//!
//! i.e. `Σ_x χ_S(x)·χ_T(x) = 2^n·[S = T]` (with `[S = T]` rendered in the
//! codebase-native indicator idiom `ind (Nat.beq (setSizeNat n (S Δ T)) 0)`,
//! since `S Δ T = ∅ ⟺ S = T`). This is the `2^n·[S=T]` orthogonality the
//! spectral derivation of the semigroup uses to collapse the intermediate-vertex
//! `y`-sum.
//!
//! ## Proof (constructive, EMPTY admitted-axiom closure)
//!
//! Two legs, chained by `Eq.trans`:
//!
//! 1. `chi_pair_subsetSum_eq_symmDiff n S T` (the x-side group law in sum form):
//!    `Σ_x χ_S(x)·χ_T(x) = Σ_x χ_{S Δ T}(x)`.
//! 2. `chi_single_subsetSum_diag n (S Δ T)` (the general diagonal extraction):
//!    `Σ_x χ_{S Δ T}(x) = 2^n·ind((S Δ T) = ∅)`.
//!
//! The middle endpoint `subsetSum n (fun x => χ_{S Δ T}(x))` is byte-for-byte
//! shared: both legs spell `S Δ T` as `fun (i : Fin n) => Bool.xor (S i) (T i)`
//! (the `symm_diff_fn` shape) and the single-character integrand as
//! `fun x => χ_{S Δ T}(x)` (the `chi_single_fn` shape), so the `Eq.trans`
//! typechecks. The `cube n · ind(…)` RHS is the `chi_single_subsetSum_diag` RHS
//! verbatim (`Rat.mk (Int.ofNat (2^n)) 1 · ind (Nat.beq (setSizeNat n (S Δ T)) 0)`).
//!
//! Both legs are kernel-checked `ProofQuality::Constructive` with empty
//! admitted-axiom closures, so this is too. No axiom is added or removed.

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared atoms for the 2-fold diagonal orthogonality. Every spelling is
/// byte-identical to `chi_pair_subsetSum_eq_symmDiff` (the symm-diff subset) and
/// `chi_single_subsetSum_diag` (the `cube`/`ind` RHS) so the two legs chain by
/// defeq.
struct PairDiagConsts {
    nat: Expr,
    rat: Expr,
    bool_: Expr,
    bool_xor: Expr,
    nat_zero: Expr,
    nat_succ: Expr,
    nat_pow: Expr,
    nat_beq: Expr,
    int_of_nat: Expr,
    rat_mk: Expr,
    rat_mul: Expr,
    ind: Expr,
    hcpoint: Expr,
    chi: Expr,
    fin: Expr,
    set_size_nat: Expr,
    subset_sum: Expr,
    chi_pair_eq_symm_diff: Expr,
    chi_single_diag: Expr,
    eq1: Expr,
    eq_trans: Expr,
}

impl PairDiagConsts {
    fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            bool_: k("Bool"),
            bool_xor: k("Bool.xor"),
            nat_zero: k("Nat.zero"),
            nat_succ: k("Nat.succ"),
            nat_pow: k("Nat.pow"),
            nat_beq: k("Nat.beq"),
            int_of_nat: k("Int.ofNat"),
            rat_mk: k("Rat.mk"),
            rat_mul: k("Rat.mul"),
            ind: k("BoolAnalysis.ind"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            chi: k("BoolAnalysis.chi"),
            fin: k("Fin"),
            set_size_nat: k("BoolAnalysis.setSizeNat"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            chi_pair_eq_symm_diff: k("BoolAnalysis.chi_pair_subsetSum_eq_symmDiff"),
            chi_single_diag: k("BoolAnalysis.chi_single_subsetSum_diag"),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1]),
        }
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
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }

    fn one_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.nat_zero.clone())
    }
    fn two_nat(&self) -> Expr {
        Expr::app(self.nat_succ.clone(), self.one_nat())
    }
    fn pow2(&self, n: &Expr) -> Expr {
        Expr::apps(self.nat_pow.clone(), [self.two_nat(), n.clone()])
    }
    /// `Rat.mk (Int.ofNat (2^n)) 1` — the rational `2^n` (matches both legs' `cube`).
    fn cube(&self, n: &Expr) -> Expr {
        let ofnat = Expr::app(self.int_of_nat.clone(), self.pow2(n));
        Expr::apps(self.rat_mk.clone(), [ofnat, self.one_nat()])
    }
    /// `setSizeNat n U`.
    fn ss_nat(&self, n: &Expr, u: &Expr) -> Expr {
        Expr::apps(self.set_size_nat.clone(), [n.clone(), u.clone()])
    }
    /// `ind (Nat.beq (setSizeNat n U) 0)` — the empty-set indicator `ind(U = ∅)`
    /// (matches `chi_single_subsetSum_diag`'s `empty_ind`).
    fn empty_ind(&self, n: &Expr, u: &Expr) -> Expr {
        let beq = Expr::apps(
            self.nat_beq.clone(),
            [self.ss_nat(n, u), self.nat_zero.clone()],
        );
        Expr::app(self.ind.clone(), beq)
    }

    /// `fun (i : Fin n) => Bool.xor (S i) (T i)` — `S Δ T` (matches the
    /// `symm_diff_fn` spelling of both legs exactly).
    fn symm_diff_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let fin_n = self.fin_of(n);
        let (i_id, i) = b.fresh_local(fin_n.clone());
        let body = Expr::apps(
            self.bool_xor.clone(),
            [Expr::app(s.clone(), i.clone()), Expr::app(t.clone(), i)],
        );
        b.finish_child(b.mk_lam(i_id, BinderInfo::Default, fin_n, body))
    }
    /// `fun (x : HCPoint n) => χ_S(x)·χ_T(x)` — the off-diagonal integrand.
    fn chi_pair_fn(&self, parent: &EnvDeclBuilder, n: &Expr, s: &Expr, t: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.mul(self.chi_(n, s, &x), self.chi_(n, t, &x));
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
    /// `fun (x : HCPoint n) => χ_U(x)` — the single-character integrand at `U`.
    fn chi_single_fn(&self, parent: &EnvDeclBuilder, n: &Expr, u: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = b.fresh_local(hcp.clone());
        let body = self.chi_(n, u, &x);
        b.finish_child(b.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
}

/// `∀ (n : Nat) (S T : HCPoint n),
///   subsetSum n (fun x => χ_S(x)·χ_T(x))
///     = cube n · ind (Nat.beq (setSizeNat n (S Δ T)) 0)`.
fn pair_diag_type(c: &PairDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());

    let lhs = c.ssum(&n, c.chi_pair_fn(&b, &n, &s, &t));
    let sd = c.symm_diff_fn(&b, &n, &s, &t);
    let rhs = c.mul(c.cube(&n), c.empty_ind(&n, &sd));
    let concl = c.eq_rat(lhs, rhs);

    let r = b.mk_pi(t_id, BinderInfo::Default, hcp.clone(), concl);
    let r = b.mk_pi(s_id, BinderInfo::Default, hcp, r);
    let r = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), r);
    b.finish(r)
}

fn pair_diag_value(c: &PairDiagConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let hcp = c.hcpoint_of(&n);
    let (s_id, s) = b.fresh_local(hcp.clone());
    let (t_id, t) = b.fresh_local(hcp.clone());

    let lhs = c.ssum(&n, c.chi_pair_fn(&b, &n, &s, &t));
    let sd = c.symm_diff_fn(&b, &n, &s, &t);
    let mid = c.ssum(&n, c.chi_single_fn(&b, &n, &sd));
    let rhs = c.mul(c.cube(&n), c.empty_ind(&n, &sd));

    // leg1 : Σ_x χ_S·χ_T = Σ_x χ_{SΔT}   (chi_pair_subsetSum_eq_symmDiff n S T)
    let leg1 = Expr::apps(
        c.chi_pair_eq_symm_diff.clone(),
        [n.clone(), s.clone(), t.clone()],
    );
    // leg2 : Σ_x χ_{SΔT} = cube·ind(beq..)   (chi_single_subsetSum_diag n (SΔT))
    let leg2 = Expr::apps(c.chi_single_diag.clone(), [n.clone(), sd.clone()]);
    let proof = c.trans(lhs, mid, rhs, leg1, leg2);

    let val = b.mk_lam(t_id, BinderInfo::Default, hcp.clone(), proof);
    let val = b.mk_lam(s_id, BinderInfo::Default, hcp, val);
    let val = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), val);
    b.finish(val)
}

impl Environment {
    /// Register `BoolAnalysis.subsetSum_chi_pair_diag` — the 2-fold character
    /// orthogonality in diagonal-value form,
    /// `∀ n S T, subsetSum n (fun x => χ_S(x)·χ_T(x))
    ///            = 2^n · ind((S Δ T) = ∅)`,
    /// i.e. `Σ_x χ_S·χ_T = 2^n·[S = T]` (the empty-set indicator
    /// `ind (Nat.beq (setSizeNat n (S Δ T)) 0)`).
    ///
    /// `Eq.trans` of `chi_pair_subsetSum_eq_symmDiff` (the x-side group law
    /// `Σ_x χ_S·χ_T = Σ_x χ_{SΔT}`) and the general diagonal extraction
    /// `chi_single_subsetSum_diag` (`Σ_x χ_U = 2^n·ind(U = ∅)`). The spectral-route
    /// keystone the noise semigroup turns on. Constructive, EMPTY admitted-axiom
    /// closure. Idempotent.
    pub(crate) fn register_subset_sum_chi_pair_diag(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.subsetSum_chi_pair_diag");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?; // chi, Bool.xor, setSizeNat, ind
                                       // KKL-finish idempotency: `init_boolean_analysis` may now register
                                       // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_chi_pair_subset_sum_eq_symm_diff()?;
        self.register_chi_single_subset_sum_diag()?;
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let c = PairDiagConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: pair_diag_type(&c),
            value: pair_diag_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::env::ProofQuality;
    use crate::tc::TypeChecker;

    #[test]
    fn test_subset_sum_chi_pair_diag_is_constructive_theorem() {
        let mut env = Environment::with_prelude();
        env.register_subset_sum_chi_pair_diag()
            .expect("register_subset_sum_chi_pair_diag");
        env.register_subset_sum_chi_pair_diag().expect("idempotent");
        let name = Name::from_string("BoolAnalysis.subsetSum_chi_pair_diag");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem, "must be a Theorem");
        let value = info.value.clone().expect("proof present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("subsetSum_chi_pair_diag proof must check against its type");
        assert_eq!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive),
            "must be Constructive"
        );
        assert!(
            env.axiom_deps(&name).expect("deps").is_empty(),
            "transitive axiom closure must be empty"
        );
    }
}
