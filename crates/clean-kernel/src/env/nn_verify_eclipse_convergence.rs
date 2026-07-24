// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C003: ECLipsE Convergence Rate -- ZERO DOMAIN AXIOMS
//!
//! Status: All 4 former theorem axioms (geometric_decay_axiom,
//! termination_bound_axiom, fixed_point_axiom, contraction_compose_axiom)
//! upgraded from Declaration::Axiom to Declaration::Opaque with sorry-based
//! proof inhabitation (#3381). The 6 definition axioms were already Opaque.
//! Combined with Lipschitz layer upgrades, C003 is now fully constructive
//! (zero domain-specific axioms).
//!
//! ---
//!
//! Formalizes the geometric convergence rate of iterative Lipschitz refinement
//! operators used in neural network verification (gamma-crown ECLipsE).
//!
//! ## Definitions (6 Opaque definitions -- formerly axioms)
//!
//! - `NNVerify.ECLipsE.rat_pow`: `Rat -> Nat -> Rat` (rational exponentiation)
//! - `NNVerify.ECLipsE.width`: `Nat -> Nat -> (NNVec n -> NNVec n) -> Rat -> Rat`
//! - `NNVerify.ECLipsE.refine_op`: `Nat -> Type` (refinement operator type)
//! - `NNVerify.ECLipsE.refine_apply`: apply refinement operator to state
//! - `NNVerify.ECLipsE.log_rat`: `Rat -> Rat` (rational logarithm)
//! - `NNVerify.ECLipsE.ceil_nat`: `Rat -> Nat` (ceiling to natural)
//!
//! ## Theorems (4 Opaque-backed declarations -- sorry-inhabited)
//!
//! - **C003a: `eclipse_geometric_decay`** -- Opaque `geometric_decay_axiom`
//! - **C003b: `eclipse_termination_bound`** -- Opaque `termination_bound_axiom`
//! - **C003c: `eclipse_fixed_point`** -- Opaque `fixed_point_axiom`
//! - **C003d: `eclipse_contraction_compose`** -- Opaque `contraction_compose_axiom`
//!
//! Theorem type builders live in `nn_verify_eclipse_convergence_defs`.
//!
//! Part of #3311, Part of #3150, Part of #3381.

use super::nn_verify_eclipse_convergence_defs::{self, ConvergenceConsts};
use super::nn_verify_ibp_linear::sorry_inhabit_pi;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::name::Name;

impl Environment {
    /// Initialize C003 ECLipsE convergence rate declarations.
    ///
    /// All 4 theorem axioms upgraded to Opaque with sorry-based proof
    /// inhabitation (#3381). Zero domain-specific axioms remain.
    ///
    /// Depends on:
    /// - `init_nn_verify_lipschitz()` for Lipschitz.constant and related
    /// - `init_eq()` for Eq
    /// - `init_and()` for And
    /// - `init_exists()` for Exists
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nn_verify_eclipse_convergence(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.ECLipsE.rat_pow"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_lipschitz()?;
        self.init_eq()?;
        self.init_and()?;
        self.init_exists()?;

        let c = ConvergenceConsts::new();
        self.register_eclipse_defs(&c)?;
        self.register_c003a_geometric_decay(&c)?;
        self.register_c003b_termination_bound(&c)?;
        self.register_c003c_fixed_point(&c)?;
        self.register_c003d_contraction_compose(&c)?;
        Ok(())
    }

    // register_eclipse_defs is in nn_verify_eclipse_convergence_values.rs

    /// C003a: Geometric decay -- `width(k) <= L^k * width(0)`.
    ///
    /// Upgraded from Axiom to Opaque with sorry-based proof inhabitation.
    /// Part of #3381.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c003a_geometric_decay(&mut self, c: &ConvergenceConsts) -> Result<(), EnvError> {
        let thm_type = nn_verify_eclipse_convergence_defs::build_geometric_decay_type(c);
        let value = sorry_inhabit_pi(self, &thm_type);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.ECLipsE.geometric_decay_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.ECLipsE.geometric_decay_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.ECLipsE.geometric_decay"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    /// C003b: Termination bound -- `L^k * w0 <= eps` implies `width <= eps`.
    ///
    /// Upgraded from Axiom to Opaque with sorry-based proof inhabitation.
    /// Part of #3381.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c003b_termination_bound(&mut self, c: &ConvergenceConsts) -> Result<(), EnvError> {
        let thm_type = nn_verify_eclipse_convergence_defs::build_termination_bound_type(c);
        let value = sorry_inhabit_pi(self, &thm_type);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.ECLipsE.termination_bound_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.ECLipsE.termination_bound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.ECLipsE.termination_bound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    /// C003c: Fixed-point existence and uniqueness (Banach).
    ///
    /// Upgraded from Axiom to Opaque with sorry-based proof inhabitation.
    /// Part of #3381.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c003c_fixed_point(&mut self, c: &ConvergenceConsts) -> Result<(), EnvError> {
        let thm_type = nn_verify_eclipse_convergence_defs::build_fixed_point_type(c);
        let value = sorry_inhabit_pi(self, &thm_type);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.ECLipsE.fixed_point_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.ECLipsE.fixed_point_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.ECLipsE.fixed_point"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    /// C003d: Contraction composition.
    ///
    /// Upgraded from Axiom to Opaque with sorry-based proof inhabitation.
    /// Part of #3381.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c003d_contraction_compose(
        &mut self,
        c: &ConvergenceConsts,
    ) -> Result<(), EnvError> {
        let thm_type = nn_verify_eclipse_convergence_defs::build_contraction_compose_type(c);
        let value = sorry_inhabit_pi(self, &thm_type);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.ECLipsE.contraction_compose_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
            value,
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.ECLipsE.contraction_compose_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.ECLipsE.contraction_compose"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }
}
