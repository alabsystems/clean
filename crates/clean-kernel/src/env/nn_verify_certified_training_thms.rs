// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Training step types and soundness theorems for certified training.
//!
//! Extends the certified training formalization with the types needed
//! to model actual training loop steps and prove that the certificate
//! is preserved across gradient updates.
//!
//! ## Types
//!
//! - `NNVerify.CertTrain.TrainingConfig` — configuration (learning rate, eps, batch size)
//! - `NNVerify.CertTrain.CertLoss` — certified loss (standard + IBP bound component)
//! - `NNVerify.CertTrain.TrainStep` — one training step: weights -> updated weights
//!
//! ## Definitions
//!
//! - `NNVerify.CertTrain.cert_evolution` — certificate tightness after k steps
//!
//! ## Theorems (axiom-backed)
//!
//! - `NNVerify.CertTrain.train_step_preserves_cert` —
//!     if IBP bounds are sound before a step, they remain sound after
//!     (with recomputed IBP bounds on the updated weights)
//! - `NNVerify.CertTrain.monotone_cert_loss` —
//!     under certified training, the certified loss is non-increasing
//!
//! Part of #3257.

use super::nn_verify_certified_training::CertTrainConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

// =============================================================================
// Type builders
// =============================================================================

/// `NNVerify.CertTrain.TrainingConfig : Type`
///
/// Opaque configuration type for one training run.
/// Semantically contains: learning rate (Rat), epsilon schedule, batch size (Nat).
pub(super) fn build_training_config_type() -> Expr {
    Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
}

/// `NNVerify.CertTrain.CertLoss : Nat -> Nat -> Type`
///
/// Certified loss for a network with n_in inputs and n_out outputs.
/// Combines standard cross-entropy loss with IBP-based robust loss bound.
pub(super) fn build_cert_loss_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_in_id, _) = b.fresh_local(c.nat.clone());
    let (n_out_id, _) = b.fresh_local(c.nat.clone());
    let type0 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), type0);
    let e = b.mk_pi(n_in_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.CertTrain.TrainStep`:
/// `(n_in n_out : Nat) -> (NNVec n_in -> NNVec n_out) ->
///  IntervalBounds n_in -> (NNVec n_in -> NNVec n_out)`
///
/// One training step: given a network and input bounds, produces the
/// updated network. The step implicitly includes gradient computation
/// on the certified loss and weight update.
pub(super) fn build_train_step_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_in_id, n_in) = b.fresh_local(c.nat.clone());
    let (n_out_id, n_out) = b.fresh_local(c.nat.clone());
    let net_ty = c.network_ty(&n_in, &n_out);
    let ib_in = c.ib_of(n_in);
    let (net_id, _) = b.fresh_local(net_ty.clone());
    let (ib_id, _) = b.fresh_local(ib_in.clone());

    // Return type: same network type (NNVec n_in -> NNVec n_out)
    let e = b.mk_pi(ib_id, BinderInfo::Default, ib_in, net_ty.clone());
    let e = b.mk_pi(net_id, BinderInfo::Default, net_ty, e);
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_in_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Definition builders
// =============================================================================

/// `NNVerify.CertTrain.cert_evolution`:
/// `(m n : Nat) -> (NNVec n_in -> NNVec n_out) ->
///  IntervalBounds n_in -> Nat -> Rat`
///
/// Tracks certificate tightness (IBP bound gap) after k training steps.
/// cert_evolution net B 0 = bound_tightness of initial network on B
/// cert_evolution net B (k+1) = bound_tightness after step k+1
pub(super) fn build_cert_evolution_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_in_id, n_in) = b.fresh_local(c.nat.clone());
    let (n_out_id, n_out) = b.fresh_local(c.nat.clone());
    let net_ty = c.network_ty(&n_in, &n_out);
    let (net_id, _) = b.fresh_local(net_ty.clone());
    let ib_in = c.ib_of(n_in);
    let (ib_id, _) = b.fresh_local(ib_in.clone());
    // k : Nat — number of training steps
    let (k_id, _) = b.fresh_local(c.nat.clone());

    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), c.rat.clone());
    let e = b.mk_pi(ib_id, BinderInfo::Default, ib_in, e);
    let e = b.mk_pi(net_id, BinderInfo::Default, net_ty, e);
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_in_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Theorem type builders
// =============================================================================

/// `NNVerify.CertTrain.train_step_preserves_cert`:
///
/// The key theorem: if IBP bounds are sound for the current weights,
/// then after one training step (with recomputed IBP bounds), the new
/// bounds are still sound.
///
/// ```text
/// forall (m n : Nat) (W : NNMat m n) (b : NNVec m)
///   (B : IntervalBounds n) (x : NNVec n),
///   contains B x ->
///   contains (ibp_bounds (train_step_net W b B))
///            ((train_step_net W b B) x)
/// ```
///
/// Where `train_step_net` produces the updated network, and
/// `ibp_bounds` recomputes the IBP bounds for the new network.
/// The soundness follows because IBP bounds are recomputed from
/// scratch on the updated weights — they are not incrementally
/// adjusted.
pub(super) fn build_train_step_preserves_cert_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let ib_contains = Expr::const_(
        Name::from_string("NNVerify.IntervalBounds.contains"),
        vec![],
    );
    let ibp_bounds = Expr::const_(Name::from_string("NNVerify.CertTrain.ibp_bounds"), vec![]);
    let train_step = Expr::const_(Name::from_string("NNVerify.CertTrain.TrainStep"), vec![]);

    let (n_in_id, n_in) = b.fresh_local(c.nat.clone());
    let (n_out_id, n_out) = b.fresh_local(c.nat.clone());
    let net_ty = c.network_ty(&n_in, &n_out);
    let (net_id, net) = b.fresh_local(net_ty.clone());
    let ib_in = c.ib_of(n_in.clone());
    let vec_n_in = c.vec_of(n_in.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_in.clone());
    let (x_id, x) = b.fresh_local(vec_n_in.clone());

    // Hypothesis: contains B x
    let hyp = Expr::apps(ib_contains.clone(), [n_in.clone(), bnd.clone(), x.clone()]);
    let (h_id, _) = b.fresh_local(hyp.clone());

    // step = TrainStep n_in n_out net B
    let step_net = Expr::apps(
        train_step,
        [n_in.clone(), n_out.clone(), net.clone(), bnd.clone()],
    );

    // new_bounds = ibp_bounds n_in n_out step_net B
    let new_bounds = Expr::apps(
        ibp_bounds,
        [n_in.clone(), n_out.clone(), step_net.clone(), bnd.clone()],
    );

    // step_net applied to x
    let step_output = Expr::app(step_net, x);

    // Conclusion: contains new_bounds step_output
    let concl = Expr::apps(ib_contains, [n_out, new_bounds, step_output]);

    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_n_in, e);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_in, e);
    let e = b.mk_pi(net_id, BinderInfo::Default, net_ty, e);
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_in_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// `NNVerify.CertTrain.monotone_cert_loss`:
///
/// Under certified training, the certified loss is non-increasing
/// across training steps.
///
/// ```text
/// forall (n_in n_out : Nat) (net : NNVec n_in -> NNVec n_out)
///   (B : IntervalBounds n_in) (k : Nat),
///   cert_evolution n_in n_out net B (k + 1)
///     <= cert_evolution n_in n_out net B k
/// ```
pub(super) fn build_monotone_cert_loss_type(c: &CertTrainConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let cert_evo = Expr::const_(
        Name::from_string("NNVerify.CertTrain.cert_evolution"),
        vec![],
    );
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);

    let (n_in_id, n_in) = b.fresh_local(c.nat.clone());
    let (n_out_id, n_out) = b.fresh_local(c.nat.clone());
    let net_ty = c.network_ty(&n_in, &n_out);
    let (net_id, net) = b.fresh_local(net_ty.clone());
    let ib_in = c.ib_of(n_in.clone());
    let (bnd_id, bnd) = b.fresh_local(ib_in.clone());
    let (k_id, k) = b.fresh_local(c.nat.clone());

    // cert_evolution n_in n_out net B (k + 1)
    let k_succ = Expr::app(nat_succ, k.clone());
    let evo_next = Expr::apps(
        cert_evo.clone(),
        [
            n_in.clone(),
            n_out.clone(),
            net.clone(),
            bnd.clone(),
            k_succ,
        ],
    );

    // cert_evolution n_in n_out net B k
    let evo_curr = Expr::apps(cert_evo, [n_in, n_out, net, bnd, k]);

    // Conclusion: evo_next <= evo_curr
    let concl = c.rat_le(evo_next, evo_curr);

    let e = b.mk_pi(k_id, BinderInfo::Default, c.nat.clone(), concl);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, ib_in, e);
    let e = b.mk_pi(net_id, BinderInfo::Default, net_ty, e);
    let e = b.mk_pi(n_out_id, BinderInfo::Default, c.nat.clone(), e);
    let e = b.mk_pi(n_in_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Environment impl
// =============================================================================

impl Environment {
    /// Register training step types and soundness theorems.
    ///
    /// Depends on: `init_nn_verify_certified_training()` for base definitions,
    /// `init_prod()` for the Prod return type.
    ///
    /// Called from `init_nn_verify_certified_training()` after base definitions
    /// are registered.
    #[cfg(any(test, feature = "math-overlays"))]
    pub(super) fn register_certified_training_thms(
        &mut self,
        c: &CertTrainConsts,
    ) -> Result<(), EnvError> {
        self.init_prod()?;
        self.init_nat()?;

        // Types
        self.register_ct_training_config()?;
        self.register_ct_cert_loss(c)?;
        self.register_ct_train_step(c)?;

        // Definitions
        self.register_ct_cert_evolution(c)?;

        // Theorems
        self.register_ct_train_step_preserves_cert(c)?;
        self.register_ct_monotone_cert_loss(c)?;

        Ok(())
    }

    // -- Types ---------------------------------------------------------------

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_ct_training_config(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.CertTrain.TrainingConfig"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.TrainingConfig"),
            level_params: vec![],
            type_: build_training_config_type(),
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_ct_cert_loss(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.CertTrain.CertLoss"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.CertLoss"),
            level_params: vec![],
            type_: build_cert_loss_type(c),
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_ct_train_step(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.CertTrain.TrainStep"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.TrainStep"),
            level_params: vec![],
            type_: build_train_step_type(c),
        })
    }

    // -- Definitions ---------------------------------------------------------

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_ct_cert_evolution(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.CertTrain.cert_evolution"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.cert_evolution"),
            level_params: vec![],
            type_: build_cert_evolution_type(c),
        })
    }

    // -- Theorems (axiom-backed) ---------------------------------------------

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_ct_train_step_preserves_cert(
        &mut self,
        c: &CertTrainConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "NNVerify.CertTrain.train_step_preserves_cert",
            ))
            .is_some()
        {
            return Ok(());
        }
        let thm_type = build_train_step_preserves_cert_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.train_step_preserves_cert_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.CertTrain.train_step_preserves_cert_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.CertTrain.train_step_preserves_cert"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_ct_monotone_cert_loss(&mut self, c: &CertTrainConsts) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.CertTrain.monotone_cert_loss"))
            .is_some()
        {
            return Ok(());
        }
        let thm_type = build_monotone_cert_loss_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.CertTrain.monotone_cert_loss_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.CertTrain.monotone_cert_loss_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.CertTrain.monotone_cert_loss"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }
}
