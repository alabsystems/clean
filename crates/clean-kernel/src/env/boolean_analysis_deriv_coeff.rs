// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `BoolAnalysis.deriv_coeff_eq` — the per-`S` derivative coefficient collapse
//! (`#4`), the FIRST consumer of the freshly-activated
//! `BoolAnalysis.subsetSum_flip_invariant` (kkl keystone leg):
//!
//! ```text
//! BoolAnalysis.deriv_coeff_eq :
//!   ∀ (n : Nat) (b : HCPoint n → Rat) (S : HCPoint n) (i : Fin n),
//!     @Eq Rat
//!       (Acoeff n (fun x => b x − b (hcFlip n x i)) S)      -- A(D_i b, S)
//!       (Rat.mul (Rat.mul 2 (ind (S i))) (Acoeff n b S))    -- (2·ind(S i))·A(b,S)
//! ```
//!
//! where `Acoeff n g S := subsetSum n (fun y => (g y)·(chi n S y))` is the
//! un-normalized `S`-Fourier coefficient of `g`, and `D_i b x := b x − b (hcFlip
//! n x i)` is the discrete derivative.
//!
//! Proof chain (`fs := flipSign (S i)`):
//! 1. `A(D_i b,S) = subsetSum (fun y => (b y − b(flip y))·χ_S y)`  [δ].
//! 2. pointwise `(b y − b(flip y))·χ = (b y)·χ − (b(flip y))·χ`  [mul_comm +
//!    Rat.mul_sub + mul_comm], lifted by `subsetSum_congr`.
//! 3. `subsetSum_sub`  →  `A(b,S) − subsetSum (fun y => (b(flip y))·χ_S y)`.
//! 4. `subsetSum (fun y => (b(flip y))·χ_S y) = fs·A(b,S)`:
//!    - `subsetSum_flip_invariant n g i` with `g z := (b z)·χ_S(flip z)` gives
//!      `subsetSum (fun y => g(flip y)) = subsetSum g`; `g(flip y) = (b(flip
//!      y))·χ_S(flip(flip y)) = (b(flip y))·χ_S y`  [hcFlip_involutive], so the
//!      LHS sum (`subsetSum_congr`) is the target;
//!    - `subsetSum g = subsetSum (fun z => (b z)·(fs·χ_S z))`  [chi_flip_spectral]
//!      `= subsetSum (fun z => fs·((b z)·χ_S z))`  [mul rearrange]
//!      `= fs·A(b,S)`  [subsetSum_smul].
//! 5. `A(b,S) − fs·A(b,S) = (1−fs)·A(b,S) = (2·ind(S i))·A(b,S)`
//!    [factor + `flip_coeff_absorb`].
//!
//! Constructive, empty admitted-axiom closure.  Squaring (`A(D_i b,S)^2 =
//! 4·ind(S i)·A(b,S)^2`) is the immediate `congrArg (·^2)` corollary
//! `deriv_coeff_sq_eq`.

#![allow(clippy::too_many_arguments)]

use super::decl_builder::EnvDeclBuilder;
use super::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// `Rat.mk (Int.ofNat k) 1` — the rational numeral `k`.
fn rat_numeral(k: u64) -> Expr {
    let c = |s: &str| Expr::const_(Name::from_string(s), vec![]);
    let mut nat = c("Nat.zero");
    for _ in 0..k {
        nat = Expr::app(c("Nat.succ"), nat);
    }
    Expr::apps(
        c("Rat.mk"),
        [
            Expr::app(c("Int.ofNat"), nat),
            Expr::app(c("Nat.succ"), c("Nat.zero")),
        ],
    )
}

pub(super) struct DerivCoeffConsts {
    nat: Expr,
    rat: Expr,
    hcpoint: Expr,
    fin: Expr,
    subset_sum: Expr,
    subset_sum_sub: Expr,
    subset_sum_congr: Expr,
    subset_sum_smul: Expr,
    subset_sum_flip_invariant: Expr,
    chi: Expr,
    ind: Expr,
    flip_sign: Expr,
    hc_flip: Expr,
    hc_flip_involutive: Expr,
    chi_flip_spectral: Expr,
    flip_coeff_absorb: Expr,
    rat_mul: Expr,
    rat_sub: Expr,
    rat_mul_sub: Expr,
    rat_mul_comm: Expr,
    rat_mul_assoc: Expr,
    rat_one: Expr,
    rat_two: Expr,
    eq1: Expr,
    eq_symm: Expr,
    eq_trans: Expr,
    congr_arg: Expr,
}

impl DerivCoeffConsts {
    pub(super) fn new() -> Self {
        let l1 = Level::succ(Level::zero());
        let k = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        Self {
            nat: k("Nat"),
            rat: k("Rat"),
            hcpoint: k("BoolAnalysis.HCPoint"),
            fin: k("Fin"),
            subset_sum: k("BoolAnalysis.subsetSum"),
            subset_sum_sub: k("BoolAnalysis.subsetSum_sub"),
            subset_sum_congr: k("BoolAnalysis.subsetSum_congr"),
            subset_sum_smul: k("BoolAnalysis.subsetSum_smul"),
            subset_sum_flip_invariant: k("BoolAnalysis.subsetSum_flip_invariant"),
            chi: k("BoolAnalysis.chi"),
            ind: k("BoolAnalysis.ind"),
            flip_sign: k("BoolAnalysis.flipSign"),
            hc_flip: k("BoolAnalysis.hcFlip"),
            hc_flip_involutive: k("BoolAnalysis.hcFlip_involutive"),
            chi_flip_spectral: k("BoolAnalysis.chi_flip_spectral"),
            flip_coeff_absorb: k("BoolAnalysis.flip_coeff_absorb"),
            rat_mul: k("Rat.mul"),
            rat_sub: k("Rat.sub"),
            rat_mul_sub: k("Rat.mul_sub"),
            rat_mul_comm: k("Rat.mul_comm"),
            rat_mul_assoc: k("Rat.mul_assoc"),
            rat_one: k("Rat.one"),
            rat_two: rat_numeral(2),
            eq1: Expr::const_(Name::from_string("Eq"), vec![l1.clone()]),
            eq_symm: Expr::const_(Name::from_string("Eq.symm"), vec![l1.clone()]),
            eq_trans: Expr::const_(Name::from_string("Eq.trans"), vec![l1.clone()]),
            congr_arg: Expr::const_(Name::from_string("congrArg"), vec![l1.clone(), l1]),
        }
    }

    fn hcpoint_of(&self, n: &Expr) -> Expr {
        Expr::app(self.hcpoint.clone(), n.clone())
    }
    fn hcpoint_to_rat(&self, n: &Expr) -> Expr {
        Expr::pi(BinderInfo::Default, self.hcpoint_of(n), self.rat.clone())
    }
    fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }
    fn mul(&self, a: Expr, bb: Expr) -> Expr {
        Expr::apps(self.rat_mul.clone(), [a, bb])
    }
    fn sub(&self, a: Expr, bb: Expr) -> Expr {
        Expr::apps(self.rat_sub.clone(), [a, bb])
    }
    fn ssum(&self, n: &Expr, g: Expr) -> Expr {
        Expr::apps(self.subset_sum.clone(), [n.clone(), g])
    }
    fn chi_(&self, n: &Expr, s: &Expr, x: &Expr) -> Expr {
        Expr::apps(self.chi.clone(), [n.clone(), s.clone(), x.clone()])
    }
    fn ind_(&self, b: Expr) -> Expr {
        Expr::app(self.ind.clone(), b)
    }
    fn flip_sign_(&self, b: Expr) -> Expr {
        Expr::app(self.flip_sign.clone(), b)
    }
    fn hc_flip_(&self, n: &Expr, x: &Expr, i: &Expr) -> Expr {
        Expr::apps(self.hc_flip.clone(), [n.clone(), x.clone(), i.clone()])
    }
    fn eq_rat(&self, l: Expr, r: Expr) -> Expr {
        Expr::apps(self.eq1.clone(), [self.rat.clone(), l, r])
    }
    fn trans(&self, a: Expr, b: Expr, cc: Expr, h1: Expr, h2: Expr) -> Expr {
        Expr::apps(self.eq_trans.clone(), [self.rat.clone(), a, b, cc, h1, h2])
    }
    fn symm(&self, a: Expr, b: Expr, h: Expr) -> Expr {
        Expr::apps(self.eq_symm.clone(), [self.rat.clone(), a, b, h])
    }
    fn congr(&self, a: Expr, b: Expr, g: Expr, h: Expr) -> Expr {
        Expr::apps(
            self.congr_arg.clone(),
            [self.rat.clone(), self.rat.clone(), a, b, g, h],
        )
    }
    fn mul_left_congr(
        &self,
        parent: &EnvDeclBuilder,
        left: &Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let g = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.mul(left.clone(), z);
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, bb, g, h)
    }
    fn sub_right_congr(
        &self,
        parent: &EnvDeclBuilder,
        leftc: &Expr,
        a: Expr,
        bb: Expr,
        h: Expr,
    ) -> Expr {
        let g = {
            let mut b = EnvDeclBuilder::child_of(parent);
            let (z_id, z) = b.fresh_local(self.rat.clone());
            let body = self.sub(leftc.clone(), z);
            b.finish_child(b.mk_lam(z_id, BinderInfo::Default, self.rat.clone(), body))
        };
        self.congr(a, bb, g, h)
    }

    /// `Acoeff n g S := subsetSum n (fun y => (g y)·(chi n S y))`.
    fn acoeff(&self, parent: &EnvDeclBuilder, n: &Expr, g: &Expr, s: &Expr) -> Expr {
        let mut yb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (y_id, y) = yb.fresh_local(hcp.clone());
        let body = self.mul(Expr::app(g.clone(), y.clone()), self.chi_(n, s, &y));
        let f = yb.finish_child(yb.mk_lam(y_id, BinderInfo::Default, hcp, body));
        self.ssum(n, f)
    }

    /// `D_i b := fun x => b x − b (hcFlip n x i)`.
    fn deriv(&self, parent: &EnvDeclBuilder, n: &Expr, b: &Expr, i: &Expr) -> Expr {
        let mut xb = EnvDeclBuilder::child_of(parent);
        let hcp = self.hcpoint_of(n);
        let (x_id, x) = xb.fresh_local(hcp.clone());
        let body = self.sub(
            Expr::app(b.clone(), x.clone()),
            Expr::app(b.clone(), self.hc_flip_(n, &x, i)),
        );
        xb.finish_child(xb.mk_lam(x_id, BinderInfo::Default, hcp, body))
    }
}

include!("boolean_analysis_deriv_coeff_build.rs");
include!("boolean_analysis_deriv_coeff_sq.rs");

impl Environment {
    /// Register `BoolAnalysis.deriv_coeff_eq` (`#4`, see module docs) — the
    /// per-`S` derivative coefficient collapse. Constructive, empty admitted-
    /// axiom closure. Idempotent. The first consumer of the activated
    /// `subsetSum_flip_invariant`.
    pub(crate) fn register_deriv_coeff_eq(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.deriv_coeff_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.init_boolean_analysis()?;
        // KKL-finish idempotency: `init_boolean_analysis` may now register
        // this declaration transitively, so re-check after the deps.
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.register_subset_sum()?;
        self.register_subset_sum_congr()?;
        self.register_subset_sum_sub_theorem()?;
        self.register_subset_sum_smul_theorem()?;
        self.register_subset_sum_flip_invariant()?; // the activated keystone leg
        self.register_chi_flip_spectral()?;
        self.register_flip_coeff_absorb()?;
        self.register_flip_sign()?;
        self.register_flip_involution_proof()?; // hcFlip_involutive
        self.init_rat_field_inst()?; // mul_comm, mul_assoc, mul_one, one
        self.init_nn_verify_rat_ordering()?; // Rat.mul_sub

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = DerivCoeffConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: deriv_coeff_type(&c),
            value: deriv_coeff_value(&c),
        })
    }

    /// Register `BoolAnalysis.deriv_coeff_sq_eq` — the SQUARE of `#4`:
    /// `A(D_i b,S)² = (4·ind(S i))·A(b,S)²`. Constructive, empty admitted-axiom
    /// closure. Idempotent. The `(2·ind·A)² = 4·ind²·A² = 4·ind·A²` corollary
    /// (`ind² = ind` via `ind_mul_self`, `2·2 = 4` by numeral reduction).
    pub(crate) fn register_deriv_coeff_sq_eq(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.deriv_coeff_sq_eq");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.init_eq()?;
        self.register_deriv_coeff_eq()?; // #4
        self.register_ind_mul_self()?; // ind·ind = ind
        self.register_rat_mul_mul_mul_comm_theorem()?; // (a·b)·(c·d) = (a·c)·(b·d)

        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let c = DerivCoeffConsts::new();
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: deriv_coeff_sq_type(&c),
            value: deriv_coeff_sq_value(&c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{ConstantKind, ProofQuality};
    use crate::tc::TypeChecker;

    #[test]
    fn test_deriv_coeff_eq_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_deriv_coeff_eq().expect("register");
        env.register_deriv_coeff_eq().expect("idempotent");

        let name = Name::from_string("BoolAnalysis.deriv_coeff_eq");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("deriv_coeff_eq must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
        // It transitively uses the activated keystone leg.
        let flip = Name::from_string("BoolAnalysis.subsetSum_flip_invariant");
        assert!(
            env.get_const(&flip).is_some(),
            "deriv_coeff_eq must pull in the activated subsetSum_flip_invariant"
        );
    }

    #[test]
    fn test_deriv_coeff_sq_eq_constructive_axiom_free() {
        let mut env = Environment::with_prelude();
        env.register_deriv_coeff_sq_eq().expect("register");
        env.register_deriv_coeff_sq_eq().expect("idempotent");

        let name = Name::from_string("BoolAnalysis.deriv_coeff_sq_eq");
        let info = env.get_const(&name).expect("registered");
        assert_eq!(info.kind, ConstantKind::Theorem);
        let value = info.value.clone().expect("value present");
        let tc = TypeChecker::with_mode(&env, env.mode());
        tc.check_type(&value, &info.type_)
            .expect("deriv_coeff_sq_eq must kernel-check");
        let deps = env.axiom_deps(&name).expect("deps");
        let names: Vec<String> = deps.iter().map(|x| x.to_string()).collect();
        assert!(names.is_empty(), "must be axiom-free, got {names:?}");
        assert!(matches!(
            env.proof_quality(&name),
            Some(ProofQuality::Constructive)
        ));
    }
}
