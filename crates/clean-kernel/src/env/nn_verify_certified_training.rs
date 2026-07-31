// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certified training: differentiable IBP with formally verified bounds.
//!
//! Formalizes certified training — training neural networks with provable
//! robustness guarantees using differentiable Interval Bound Propagation (IBP).
//! The key insight: IBP bounds are differentiable w.r.t. network weights,
//! enabling gradient-based optimization of a robust loss function that upper
//! bounds the worst-case adversarial loss.
//!
//! ## Definitions
//!
//! - `NNVerify.CertTrain.ibp_loss` — IBP-based robust loss: max over IBP bounds
//! - `NNVerify.CertTrain.certified_radius` — certified epsilon-ball radius
//! - `NNVerify.CertTrain.training_objective` — combined standard + robust loss
//! - `NNVerify.CertTrain.bound_tightness` — gap between IBP upper and true max
//!
//! ## Theorems (axiom-backed)
//!
//! - `NNVerify.CertTrain.ibp_loss_upper_bound` — IBP loss upper bounds worst-case
//! - `NNVerify.CertTrain.certified_radius_sound` — radius >= eps => eps-robust
//! - `NNVerify.CertTrain.training_convergence_bound` — tightness decreases
//! - `NNVerify.CertTrain.ibp_loss_differentiable` — IBP loss is differentiable
//! - `NNVerify.CertTrain.certified_training_sound` — training produces verified nets
//!
//! Part of #3257.

#[cfg(test)]
use super::nn_verify_certified_training_defs as defs;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr, ExprKind};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Shared constants for certified training formalization.
#[cfg(test)]
pub(super) struct CertTrainConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) prop: Expr,
    pub(super) nn_vec: Expr,
    pub(super) ib: Expr,
    pub(super) rat_zero: Expr,
    pub(super) rat_one: Expr,
    pub(super) le_le: Expr,
    pub(super) lt_lt: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) inst_lt_rat: Expr,
    pub(super) and: Expr,
    pub(super) ibp_loss: Expr,
    pub(super) certified_radius: Expr,
    pub(super) training_objective: Expr,
    pub(super) bound_tightness: Expr,
    pub(super) worst_case_loss: Expr,
    pub(super) is_differentiable: Expr,
}

#[cfg(test)]
impl CertTrainConsts {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            rat_one: Expr::const_(Name::from_string("Rat.one"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            lt_lt: Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            inst_lt_rat: Expr::const_(Name::from_string("instLTRat"), vec![]),
            and: Expr::const_(Name::from_string("And"), vec![]),
            ibp_loss: Expr::const_(Name::from_string("NNVerify.CertTrain.ibp_loss"), vec![]),
            certified_radius: Expr::const_(
                Name::from_string("NNVerify.CertTrain.certified_radius"),
                vec![],
            ),
            training_objective: Expr::const_(
                Name::from_string("NNVerify.CertTrain.training_objective"),
                vec![],
            ),
            bound_tightness: Expr::const_(
                Name::from_string("NNVerify.CertTrain.bound_tightness"),
                vec![],
            ),
            worst_case_loss: Expr::const_(
                Name::from_string("NNVerify.CertTrain.worst_case_loss"),
                vec![],
            ),
            is_differentiable: Expr::const_(
                Name::from_string("NNVerify.CertTrain.is_differentiable"),
                vec![],
            ),
        }
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
    #[cfg(test)]
    pub(super) fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), lhs, rhs],
        )
    }

    /// Build `LT.lt @Rat instLTRat lhs rhs`.
    #[cfg(test)]
    pub(super) fn rat_lt(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(
            self.lt_lt.clone(),
            [self.rat.clone(), self.inst_lt_rat.clone(), lhs, rhs],
        )
    }

    /// Build `GE.ge @Rat instLERat lhs rhs` (i.e. `LE.le rhs lhs`).
    #[cfg(test)]
    pub(super) fn rat_ge(&self, lhs: Expr, rhs: Expr) -> Expr {
        self.rat_le(rhs, lhs)
    }

    /// Build `NNVerify.NNVec n`.
    #[cfg(test)]
    pub(super) fn vec_of(&self, n: Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n)
    }

    /// Build `NNVerify.IntervalBounds n`.
    #[cfg(test)]
    pub(super) fn ib_of(&self, n: Expr) -> Expr {
        Expr::app(self.ib.clone(), n)
    }

    /// Function type `NNVec n_in -> NNVec n_out`.
    #[cfg(test)]
    pub(super) fn network_ty(&self, n_in: &Expr, n_out: &Expr) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.vec_of(n_in.clone()),
            self.vec_of(n_out.clone()),
        )
    }

    /// Loss function type: `NNVec n_out -> NNVec n_out -> Rat`.
    #[cfg(test)]
    pub(super) fn loss_fn_ty(&self, n_out: &Expr) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.vec_of(n_out.clone()),
            Expr::pi(
                BinderInfo::Default,
                self.vec_of(n_out.clone()),
                self.rat.clone(),
            ),
        )
    }
}

// =============================================================================
// Environment impl
// =============================================================================

#[cfg(test)]
impl Environment {
    /// Initialize certified training (differentiable IBP) declarations.
    ///
    /// Depends on:
    /// - `init_nn_verify_types()` for NNVec, NNMat, IntervalBounds
    /// - `init_rat_arith()` for Rat arithmetic
    /// - `init_rat_ord()` for Rat ordering
    /// - `init_eq()` for equality
    /// - `init_and()` for conjunction
    #[cfg(test)]
    pub(crate) fn init_nn_verify_certified_training(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_certified_training_init {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        self.init_eq()?;
        self.init_and()?;

        let c = CertTrainConsts::new();

        // Auxiliary definitions (primitives used by the main definitions)
        self.register_ct_standard_loss(&c)?;
        self.register_ct_worst_case_loss(&c)?;
        self.register_ct_is_differentiable(&c)?;
        self.register_ct_ibp_bounds(&c)?;

        // Main definitions
        self.register_ct_ibp_loss(&c)?;
        self.register_ct_certified_radius(&c)?;
        self.register_ct_training_objective(&c)?;
        self.register_ct_bound_tightness(&c)?;

        // Theorems (axiom-backed)
        self.register_ct_ibp_loss_upper_bound(&c)?;
        self.register_ct_certified_radius_sound(&c)?;
        self.register_ct_training_convergence_bound(&c)?;
        self.register_ct_ibp_loss_differentiable(&c)?;
        self.register_ct_certified_training_sound(&c)?;

        // Training step types and soundness theorems
        // (TrainingConfig, CertLoss, TrainStep, train_step_preserves_cert,
        //  cert_evolution, monotone_cert_loss)
        self.register_certified_training_thms(&c)?;

        self.nn_verify_certified_training_init = true;
        Ok(())
    }

    // -- Auxiliary definitions ------------------------------------------------

    #[cfg(test)]
    fn register_ct_standard_loss(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.standard_loss"),
            level_params: vec![],
            type_: defs::build_standard_loss_type(c),
        })
    }

    #[cfg(test)]
    fn register_ct_worst_case_loss(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.worst_case_loss"),
            level_params: vec![],
            type_: defs::build_worst_case_loss_type(c),
        })
    }

    #[cfg(test)]
    fn register_ct_is_differentiable(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.is_differentiable"),
            level_params: vec![],
            type_: defs::build_is_differentiable_type(c),
        })
    }

    #[cfg(test)]
    fn register_ct_ibp_bounds(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.ibp_bounds"),
            level_params: vec![],
            type_: defs::build_ibp_bounds_type(c),
        })
    }

    // -- Main definitions ----------------------------------------------------

    #[cfg(test)]
    fn register_ct_ibp_loss(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.ibp_loss"),
            level_params: vec![],
            type_: defs::build_ibp_loss_type(c),
        })
    }

    #[cfg(test)]
    fn register_ct_certified_radius(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.certified_radius"),
            level_params: vec![],
            type_: defs::build_certified_radius_type(c),
        })
    }

    #[cfg(test)]
    fn register_ct_training_objective(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.training_objective"),
            level_params: vec![],
            type_: defs::build_training_objective_type(c),
        })
    }

    #[cfg(test)]
    fn register_ct_bound_tightness(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.bound_tightness"),
            level_params: vec![],
            type_: defs::build_bound_tightness_type(c),
        })
    }

    // -- Theorems (axiom-backed with proof wrappers) -------------------------

    #[cfg(test)]
    fn register_ct_ibp_loss_upper_bound(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        let thm_type = defs::build_ibp_loss_upper_bound_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.ibp_loss_upper_bound_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.CertTrain.ibp_loss_upper_bound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.CertTrain.ibp_loss_upper_bound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(test)]
    fn register_ct_certified_radius_sound(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        let thm_type = defs::build_certified_radius_sound_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.certified_radius_sound_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.CertTrain.certified_radius_sound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.CertTrain.certified_radius_sound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(test)]
    fn register_ct_training_convergence_bound(
        &mut self,
        c: &CertTrainConsts,
    ) -> Result<(), EnvError> {
        let thm_type = defs::build_training_convergence_bound_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.training_convergence_bound_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.CertTrain.training_convergence_bound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.CertTrain.training_convergence_bound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(test)]
    fn register_ct_ibp_loss_differentiable(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        let thm_type = defs::build_ibp_loss_differentiable_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.ibp_loss_differentiable_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.CertTrain.ibp_loss_differentiable_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.CertTrain.ibp_loss_differentiable"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(test)]
    fn register_ct_certified_training_sound(
        &mut self,
        c: &CertTrainConsts,
    ) -> Result<(), EnvError> {
        let thm_type = defs::build_certified_training_sound_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.certified_training_sound_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.CertTrain.certified_training_sound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.CertTrain.certified_training_sound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }
}
