// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Bonami-Beckner campaign — B6 coefficient bounds.
//!
//! The two scalar `Rat`-order bounds the (2,4)-hypercontractivity B6 step
//! consumes once the noise/spectral sum has been split into its degree-graded
//! legs. Both are kernel-checked `Declaration::Theorem`s registered through the
//! CHECKED `add_decl` path:
//!
//! - `BoolAnalysis.hc_six_rho_sq_t_le_two_t`
//!     : `∀ ρ t, 3·ρ² ≤ 1 → 0 ≤ t → 6·ρ²·t ≤ 2·t`
//! - `BoolAnalysis.hc_rho_four_t_le_t`
//!     : `∀ ρ t, 3·ρ² ≤ 1 → 0 ≤ t → ρ⁴·t ≤ t`
//!
//! where `ρ² := ρ·ρ`, `ρ⁴ := ρ²·ρ²`, and the numerals are built from `Rat.one`
//! (`2 := 1+1`, `3 := 2+1`, `6 := 2·3`) — the live environment has no
//! `OfNat`-based `Rat` numeral constants, so coefficients are `Rat.one`-sums /
//! products, matching the B2 ring-identity convention.
//!
//! Every lemma is built entirely from the genuinely-`Constructive` `Rat` order
//! surface (`Rat.mul_le_mul_of_nonneg_left`, `Rat.mul_le_mul_of_nonneg_right`,
//! `Rat.sq_nonneg`, `Rat.le_trans`, `Rat.mul_assoc`, `Rat.mul_comm`,
//! `Rat.mul_one`, `Rat.one_mul`, `Rat.le_add_of_nonneg_right`, and the
//! `Rat.zero_lt_one` / `Rat.lt_iff_le_not_le` bridge to `0 ≤ 1`). Because every
//! dependency is itself `ProofQuality::Constructive` (empty domain-axiom
//! closure), so is every bound registered here.

use super::boolean_analysis_hc_bounds_proofs::{
    build_rho_four_proof, build_six_rho_sq_proof, rho_four_type, six_rho_sq_type, HcBoundsConsts,
};
use crate::env::{Declaration, EnvError, Environment};
use crate::name::Name;

impl Environment {
    /// Initialize the Bonami-Beckner B6 coefficient bounds.
    ///
    /// Registers the two scalar order bounds as kernel-checked
    /// `Declaration::Theorem`s. Idempotent (each registrar skips if the name
    /// is already present).
    ///
    /// Depends on `init_boolean_analysis_order_toolkit`, which transitively
    /// initializes the constructive `Rat` order surface these bounds build on
    /// (`Rat.mul_le_mul_of_nonneg_left/right`, `Rat.sq_nonneg`, `Rat.le_trans`,
    /// `Rat.lt_iff_le_not_le`, `Rat.zero_lt_one`, `Rat.le_add_of_nonneg_right`,
    /// `Rat.mul_assoc`, `Rat.mul_comm`, `Rat.mul_one`, `Rat.one_mul`, `Iff`,
    /// `And`, …).
    pub fn init_boolean_analysis_hc_bounds(&mut self) -> Result<(), EnvError> {
        self.init_boolean_analysis_order_toolkit()?;

        let c = HcBoundsConsts::new();
        self.register_hc_six_rho_sq_t_le_two_t(&c)?;
        self.register_hc_rho_four_t_le_t(&c)?;
        Ok(())
    }

    /// `BoolAnalysis.hc_six_rho_sq_t_le_two_t :
    ///    ∀ ρ t, Rat.le (3·(ρ·ρ)) 1 → Rat.le 0 t → Rat.le ((6·(ρ·ρ))·t) (2·t)`.
    fn register_hc_six_rho_sq_t_le_two_t(&mut self, c: &HcBoundsConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.hc_six_rho_sq_t_le_two_t");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = six_rho_sq_type(c);
        let value = build_six_rho_sq_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: ty,
            value,
        })
    }

    /// `BoolAnalysis.hc_rho_four_t_le_t :
    ///    ∀ ρ t, Rat.le (3·(ρ·ρ)) 1 → Rat.le 0 t → Rat.le (((ρ·ρ)·(ρ·ρ))·t) t`.
    fn register_hc_rho_four_t_le_t(&mut self, c: &HcBoundsConsts) -> Result<(), EnvError> {
        let name = Name::from_string("BoolAnalysis.hc_rho_four_t_le_t");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let ty = rho_four_type(c);
        let value = build_rho_four_proof(c);
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
    use crate::env::types::ConstantKind;
    use crate::env::{Environment, ProofQuality};
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    /// Bounds registered by this module (run 3, B6).
    const BOUNDS: &[&str] = &[
        "BoolAnalysis.hc_six_rho_sq_t_le_two_t",
        "BoolAnalysis.hc_rho_four_t_le_t",
    ];

    fn env() -> Environment {
        let mut env = Environment::new();
        env.init_boolean_analysis_hc_bounds()
            .expect("init_boolean_analysis_hc_bounds should succeed");
        env
    }

    /// Walk an expression; return true if any `sorry`/`sorryAx` const appears.
    fn contains_sorry(expr: &Expr) -> bool {
        let mut stack = vec![expr];
        while let Some(e) = stack.pop() {
            match e.kind() {
                ExprKind::Const(name, _) => {
                    let s = name.to_string();
                    if s == "sorry" || s == "sorryAx" {
                        return true;
                    }
                }
                ExprKind::App(f, a) => {
                    stack.push(f);
                    stack.push(a);
                }
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    stack.push(ty);
                    stack.push(body);
                }
                ExprKind::Let(_, ty, val, body, _) => {
                    stack.push(ty);
                    stack.push(val);
                    stack.push(body);
                }
                ExprKind::Proj(_, _, src) => stack.push(src),
                ExprKind::MData(_, body) => stack.push(body),
                _ => {}
            }
        }
        false
    }

    #[test]
    fn test_init_idempotent() {
        let mut env = Environment::new();
        env.init_boolean_analysis_hc_bounds().expect("first init");
        env.init_boolean_analysis_hc_bounds()
            .expect("second init should be a no-op");
    }

    #[test]
    fn test_all_registered_as_theorems() {
        let env = env();
        for name in BOUNDS {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{name} must be Declaration::Theorem, got {:?}",
                info.kind
            );
            assert!(info.value.is_some(), "{name} Theorem must retain a value");
        }
    }

    #[test]
    fn test_all_type_check() {
        let env = env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        for name in BOUNDS {
            let e = Expr::const_(Name::from_string(name), vec![]);
            let ty = tc
                .infer_type(&e)
                .unwrap_or_else(|err| panic!("{name} should kernel-type-check, got: {err:?}"));
            assert!(
                matches!(ty.kind(), ExprKind::Pi(..)),
                "{name} type should be a Pi, got {:?}",
                ty.kind()
            );
        }
    }

    #[test]
    fn test_all_sorry_free() {
        let env = env();
        for name in BOUNDS {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            let value = info.value.as_ref().expect("Theorem has value");
            assert!(
                !contains_sorry(value),
                "{name} proof value must not contain sorry/sorryAx"
            );
        }
    }

    /// Each bound has an empty domain-axiom closure and is therefore classified
    /// `ProofQuality::Constructive` — the order surface they build on is itself
    /// fully constructive over the quotient carrier.
    #[test]
    fn test_all_constructive_empty_axiom_closure() {
        let env = env();
        for name in BOUNDS {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("axiom_deps should work for {name}"));
            let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                dep_names.is_empty(),
                "{name} must have empty domain-axiom closure, got {dep_names:?}"
            );
            let q = env
                .proof_quality(&Name::from_string(name))
                .unwrap_or_else(|| panic!("proof_quality should report for {name}"));
            assert!(
                matches!(q, ProofQuality::Constructive),
                "{name} must be ProofQuality::Constructive, got {q:?}"
            );
        }
    }
}
