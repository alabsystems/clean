// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for proof-guided neural architecture search (NAS).
//!
//! Formalizes how architecture choices (depth, width, skip connections) affect
//! verification tractability via abstract interpretation bound tightness.
//!
//! ## Phase 1: Search space and verifiability
//!
//! - `architecture_space` — the space of network architectures
//! - `verifiability_score` — how easy an architecture is to verify
//! - `pareto_front` — Pareto-optimal set of (accuracy, verifiability)
//! - `architecture_transform` — architecture modification operations
//!
//! ## Phase 2: Typed architecture representation
//!
//! - `Architecture` — describes a network architecture (Type)
//! - `LayerSpec` — single layer specification (Type)
//! - `ActivationKind` — activation function kind (Type)
//! - `ArchitectureMetric` — parameterized metric (Architecture -> Nat -> Type)
//! - `cert_objective` — certificate size for a given architecture
//! - `cert_tightness` — bound tightness for a given architecture
//! - `pareto_optimal` — Pareto optimality predicate
//!
//! ## Theorems
//!
//! Phase 1: wider_more_verifiable, depth_verifiability_tradeoff,
//!          pareto_dominance_sound, nas_search_monotone,
//!          skip_connections_improve_verifiability, certified_accuracy_bound
//!
//! Phase 2: deeper_larger_cert, wider_tighter_bounds, residual_cert_composition
//!
//! Type builders are in `nn_verify_proof_guided_nas_defs.rs`.
//!
//! Part of #3259.

#[cfg(test)]
use super::nn_verify_proof_guided_nas_defs as defs;
#[cfg(test)]
use super::nn_verify_proof_guided_nas_defs2 as defs2;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr, ExprKind};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Shared constants for proof-guided NAS formalization.
#[cfg(test)]
pub(super) struct ProofGuidedNasConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    pub(super) false_: Expr,
    pub(super) eq: Expr,
    pub(super) le_le: Expr,
    pub(super) lt_lt: Expr,
    pub(super) inst_le_nat: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) inst_lt_rat: Expr,
    pub(super) inst_lt_nat: Expr,
    pub(super) rat_zero: Expr,
    pub(super) nat_mul: Expr,
    pub(super) and: Expr,
    // Phase 1: search space
    pub(super) arch_space: Expr,
    pub(super) verifiability_score: Expr,
    pub(super) pareto_front: Expr,
    pub(super) arch_transform: Expr,
    pub(super) apply_transform: Expr,
    pub(super) verified_accuracy: Expr,
    pub(super) arch_depth: Expr,
    pub(super) arch_width: Expr,
    pub(super) standard_accuracy: Expr,
    pub(super) has_skip_connections: Expr,
    pub(super) without_skip: Expr,
    // Phase 2: typed architecture representation
    pub(super) architecture: Expr,
    pub(super) layer_spec: Expr,
    pub(super) activation_kind: Expr,
    pub(super) architecture_metric: Expr,
    pub(super) cert_objective: Expr,
    pub(super) cert_tightness: Expr,
    pub(super) pareto_optimal: Expr,
    pub(super) has_residual: Expr,
    pub(super) residual_sub_cert: Expr,
}

#[cfg(test)]
impl ProofGuidedNasConsts {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            false_: Expr::const_(Name::from_string("False"), vec![]),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            lt_lt: Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
            inst_le_nat: Expr::const_(Name::from_string("instLENat"), vec![]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            inst_lt_rat: Expr::const_(Name::from_string("instLTRat"), vec![]),
            inst_lt_nat: Expr::const_(Name::from_string("instLTNat"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            arch_space: Expr::const_(Name::from_string("NNVerify.architecture_space"), vec![]),
            verifiability_score: Expr::const_(
                Name::from_string("NNVerify.verifiability_score"),
                vec![],
            ),
            pareto_front: Expr::const_(Name::from_string("NNVerify.pareto_front"), vec![]),
            arch_transform: Expr::const_(
                Name::from_string("NNVerify.architecture_transform"),
                vec![],
            ),
            apply_transform: Expr::const_(Name::from_string("NNVerify.apply_transform"), vec![]),
            verified_accuracy: Expr::const_(
                Name::from_string("NNVerify.verified_accuracy"),
                vec![],
            ),
            arch_depth: Expr::const_(Name::from_string("NNVerify.arch_depth"), vec![]),
            arch_width: Expr::const_(Name::from_string("NNVerify.arch_width"), vec![]),
            standard_accuracy: Expr::const_(
                Name::from_string("NNVerify.standard_accuracy"),
                vec![],
            ),
            has_skip_connections: Expr::const_(
                Name::from_string("NNVerify.has_skip_connections"),
                vec![],
            ),
            without_skip: Expr::const_(Name::from_string("NNVerify.without_skip"), vec![]),
            // Phase 2
            architecture: Expr::const_(Name::from_string("NNVerify.Architecture"), vec![]),
            layer_spec: Expr::const_(Name::from_string("NNVerify.LayerSpec"), vec![]),
            activation_kind: Expr::const_(Name::from_string("NNVerify.ActivationKind"), vec![]),
            architecture_metric: Expr::const_(
                Name::from_string("NNVerify.ArchitectureMetric"),
                vec![],
            ),
            cert_objective: Expr::const_(Name::from_string("NNVerify.cert_objective"), vec![]),
            cert_tightness: Expr::const_(Name::from_string("NNVerify.cert_tightness"), vec![]),
            pareto_optimal: Expr::const_(Name::from_string("NNVerify.pareto_optimal"), vec![]),
            has_residual: Expr::const_(Name::from_string("NNVerify.has_residual"), vec![]),
            residual_sub_cert: Expr::const_(
                Name::from_string("NNVerify.residual_sub_cert"),
                vec![],
            ),
        }
    }

    /// Build `LE.le @Nat instLENat lhs rhs`.
    #[cfg(test)]
    pub(super) fn nat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.nat.clone()),
                    self.inst_le_nat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `LT.lt @Nat instLTNat lhs rhs`.
    #[cfg(test)]
    pub(super) fn nat_lt(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.lt_lt.clone(), self.nat.clone()),
                    self.inst_lt_nat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `Eq @Nat a b`.
    #[cfg(test)]
    pub(super) fn nat_eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.eq.clone(), self.nat.clone()), a),
            b,
        )
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
    #[cfg(test)]
    pub(super) fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.rat.clone()),
                    self.inst_le_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `LT.lt @Rat instLTRat lhs rhs`.
    #[cfg(test)]
    pub(super) fn rat_lt(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.lt_lt.clone(), self.rat.clone()),
                    self.inst_lt_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }
}

// =============================================================================
// Environment impl
// =============================================================================

#[cfg(test)]
impl Environment {
    /// Register an axiom+theorem pair: axiom `{name}_axiom` with the given type,
    /// then a theorem `{name}` whose proof references the axiom.
    #[cfg(test)]
    fn register_axiom_theorem_pair(&mut self, name: &str, thm_type: Expr) -> Result<(), EnvError> {
        let axiom_name = format!("{}_axiom", name);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(&axiom_name),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(Name::from_string(&axiom_name), vec![]);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    /// Initialize proof-guided NAS declarations.
    ///
    /// Depends on: `init_nat`, `init_rat`, `init_rat_arith`, `init_rat_ord`,
    /// `init_eq`, `init_true_false`, `init_and`.
    #[cfg(test)]
    pub(crate) fn init_nn_verify_proof_guided_nas(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.architecture_space"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nat()?;
        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        self.init_eq()?;
        self.init_true_false()?;
        self.init_and()?;

        let c = ProofGuidedNasConsts::new();

        // Phase 1: Search space definitions
        self.register_nas_def(
            "NNVerify.architecture_space",
            defs::build_architecture_space_type(&c),
        )?;
        self.register_nas_def("NNVerify.arch_depth", defs::build_arch_depth_type(&c))?;
        self.register_nas_def("NNVerify.arch_width", defs::build_arch_width_type(&c))?;
        self.register_nas_def(
            "NNVerify.verifiability_score",
            defs::build_verifiability_score_type(&c),
        )?;
        self.register_nas_def(
            "NNVerify.standard_accuracy",
            defs::build_standard_accuracy_type(&c),
        )?;
        self.register_nas_def("NNVerify.pareto_front", defs::build_pareto_front_type(&c))?;
        self.register_nas_def(
            "NNVerify.architecture_transform",
            defs::build_architecture_transform_type(&c),
        )?;
        self.register_nas_def(
            "NNVerify.apply_transform",
            defs::build_apply_transform_type(&c),
        )?;
        self.register_nas_def(
            "NNVerify.verified_accuracy",
            defs::build_verified_accuracy_type(&c),
        )?;
        self.register_nas_def(
            "NNVerify.has_skip_connections",
            defs::build_has_skip_connections_type(&c),
        )?;
        self.register_nas_without_skip()?;

        // Phase 2: Typed architecture representation
        self.register_nas_def("NNVerify.Architecture", defs2::build_architecture_type(&c))?;
        self.register_nas_def("NNVerify.LayerSpec", defs2::build_layer_spec_type(&c))?;
        self.register_nas_def(
            "NNVerify.ActivationKind",
            defs2::build_activation_kind_type(&c),
        )?;
        self.register_nas_def(
            "NNVerify.ArchitectureMetric",
            defs2::build_architecture_metric_type(&c),
        )?;
        self.register_nas_def(
            "NNVerify.cert_objective",
            defs2::build_cert_objective_type(&c),
        )?;
        self.register_nas_def(
            "NNVerify.cert_tightness",
            defs2::build_cert_tightness_fn_type(&c),
        )?;
        self.register_nas_def(
            "NNVerify.pareto_optimal",
            defs2::build_pareto_optimal_type(&c),
        )?;
        self.register_nas_def("NNVerify.has_residual", defs2::build_has_residual_type(&c))?;
        self.register_nas_def(
            "NNVerify.residual_sub_cert",
            defs2::build_residual_sub_cert_type(&c),
        )?;

        // Phase 1 theorems
        self.register_axiom_theorem_pair(
            "NNVerify.wider_more_verifiable",
            defs::build_wider_more_verifiable_type(&c),
        )?;
        self.register_axiom_theorem_pair(
            "NNVerify.depth_verifiability_tradeoff",
            defs::build_depth_verifiability_tradeoff_type(&c),
        )?;
        self.register_axiom_theorem_pair(
            "NNVerify.pareto_dominance_sound",
            defs::build_pareto_dominance_sound_type(&c),
        )?;
        self.register_axiom_theorem_pair(
            "NNVerify.nas_search_monotone",
            defs::build_nas_search_monotone_type(&c),
        )?;
        self.register_axiom_theorem_pair(
            "NNVerify.skip_connections_improve_verifiability",
            defs::build_skip_connections_improve_verifiability_type(&c),
        )?;
        self.register_axiom_theorem_pair(
            "NNVerify.certified_accuracy_bound",
            defs::build_certified_accuracy_bound_type(&c),
        )?;

        // Phase 2 theorems: architecture comparison
        self.register_axiom_theorem_pair(
            "NNVerify.deeper_larger_cert",
            defs2::build_deeper_larger_cert_type(&c),
        )?;
        self.register_axiom_theorem_pair(
            "NNVerify.wider_tighter_bounds",
            defs2::build_wider_tighter_bounds_type(&c),
        )?;
        self.register_axiom_theorem_pair(
            "NNVerify.residual_cert_composition",
            defs2::build_residual_cert_composition_type(&c),
        )?;

        Ok(())
    }

    // -- Definition helpers ---------------------------------------------------

    /// Register a single axiom definition.
    #[cfg(test)]
    fn register_nas_def(&mut self, name: &str, ty: Expr) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `without_skip : architecture_space -> architecture_space`
    #[cfg(test)]
    fn register_nas_without_skip(&mut self) -> Result<(), EnvError> {
        let arch = Expr::const_(Name::from_string("NNVerify.architecture_space"), vec![]);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.without_skip"),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, arch.clone(), arch),
        })
    }
}
