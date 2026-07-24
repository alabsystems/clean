// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C012 Type & Value Builders
//!
//! Status: no C012 domain axioms remain.
//! 5 functions are now Opaque definitions with well-typed placeholder values.
//! 2 predicates are now Definition declarations with Prop bodies.
//! Network is an Opaque type with Nat as placeholder.
//!
//! Reduced from 11 axioms.
//!
//! See: designs/2026-04-17-publication-quality-gamma-crown-proofs.md
//!
//! ---
//!
//! Separated from `nn_verify_relu_stability` for file-size compliance.
//! All `build_*` functions return well-formed `Expr` types/values for
//! kernel declaration registration.
//!
//! ## Theorem Statement
//!
//! For a ReLU network `net`, center `x0`, and perturbation radius `eps`,
//! if the ReLU activation pattern is stable on the ball `B(x0, eps)`,
//! then every ReLU is fixed on/off throughout the region. Under a fixed
//! pattern, the network is affine on that region, CROWN's ReLU
//! relaxation becomes exact, the relaxation gap is zero, and the full
//! verification problem reduces to a single LP.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for C012 theorem construction.
pub(super) struct C012Consts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) bool_: Expr,
    pub(super) network: Expr,
    pub(super) nn_vec: Expr,
    pub(super) ib: Expr,
    pub(super) fin: Expr,
    pub(super) prop: Expr,
    pub(super) eq: Expr,
    pub(super) rat_zero: Expr,
    pub(super) pre_activation: Expr,
    pub(super) activation_pattern: Expr,
    pub(super) stability_radius: Expr,
    pub(super) perturbation_ball: Expr,
    pub(super) crown_relaxation_gap: Expr,
    pub(super) pattern_stable: Expr,
    pub(super) single_lp_form: Expr,
    pub(super) crown_exact_under_stable_core: Expr,
}

impl C012Consts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            network: Expr::const_(Name::from_string("NNVerify.C012.Network"), vec![]),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            prop: Expr::sort(Level::zero()),
            eq: Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            pre_activation: Expr::const_(Name::from_string("NNVerify.C012.pre_activation"), vec![]),
            activation_pattern: Expr::const_(
                Name::from_string("NNVerify.C012.activation_pattern"),
                vec![],
            ),
            stability_radius: Expr::const_(
                Name::from_string("NNVerify.C012.stability_radius"),
                vec![],
            ),
            perturbation_ball: Expr::const_(
                Name::from_string("NNVerify.C012.perturbation_ball"),
                vec![],
            ),
            crown_relaxation_gap: Expr::const_(
                Name::from_string("NNVerify.C012.crown_relaxation_gap"),
                vec![],
            ),
            pattern_stable: Expr::const_(Name::from_string("NNVerify.C012.pattern_stable"), vec![]),
            single_lp_form: Expr::const_(Name::from_string("NNVerify.C012.single_lp_form"), vec![]),
            crown_exact_under_stable_core: Expr::const_(
                Name::from_string("NNVerify.C012.crown_exact_under_stable_core"),
                vec![],
            ),
        }
    }

    pub(super) fn vec_of(&self, n: &Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n.clone())
    }

    pub(super) fn ib_of(&self, n: &Expr) -> Expr {
        Expr::app(self.ib.clone(), n.clone())
    }

    pub(super) fn fin_of(&self, n: &Expr) -> Expr {
        Expr::app(self.fin.clone(), n.clone())
    }

    /// Build `Eq @ty lhs rhs`.
    pub(super) fn eq_of(&self, ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(Expr::app(Expr::app(self.eq.clone(), ty), lhs), rhs)
    }

    /// Build `Eq @Rat lhs rhs`.
    pub(super) fn rat_eq(&self, lhs: Expr, rhs: Expr) -> Expr {
        self.eq_of(self.rat.clone(), lhs, rhs)
    }

    /// Build `NNVerify.C012.pre_activation n net x`.
    pub(super) fn pre_activation_app(&self, n: &Expr, net: &Expr, x: &Expr) -> Expr {
        Expr::apps(
            self.pre_activation.clone(),
            [n.clone(), net.clone(), x.clone()],
        )
    }

    /// Build `NNVerify.C012.activation_pattern n z`.
    pub(super) fn activation_pattern_app(&self, n: &Expr, z: &Expr) -> Expr {
        Expr::apps(self.activation_pattern.clone(), [n.clone(), z.clone()])
    }

    /// Build `NNVerify.C012.stability_radius n net x0`.
    pub(super) fn stability_radius_app(&self, n: &Expr, net: &Expr, x0: &Expr) -> Expr {
        Expr::apps(
            self.stability_radius.clone(),
            [n.clone(), net.clone(), x0.clone()],
        )
    }

    /// Build `NNVerify.C012.perturbation_ball n x0 eps`.
    pub(super) fn perturbation_ball_app(&self, n: &Expr, x0: &Expr, eps: &Expr) -> Expr {
        Expr::apps(
            self.perturbation_ball.clone(),
            [n.clone(), x0.clone(), eps.clone()],
        )
    }

    /// Build `NNVerify.C012.crown_relaxation_gap n net B`.
    pub(super) fn crown_gap_app(&self, n: &Expr, net: &Expr, bnd: &Expr) -> Expr {
        Expr::apps(
            self.crown_relaxation_gap.clone(),
            [n.clone(), net.clone(), bnd.clone()],
        )
    }

    /// Build `NNVerify.C012.pattern_stable n net x0 eps`.
    pub(super) fn pattern_stable_app(&self, n: &Expr, net: &Expr, x0: &Expr, eps: &Expr) -> Expr {
        Expr::apps(
            self.pattern_stable.clone(),
            [n.clone(), net.clone(), x0.clone(), eps.clone()],
        )
    }

    /// Build `NNVerify.C012.single_lp_form n net x0 eps`.
    pub(super) fn single_lp_form_app(&self, n: &Expr, net: &Expr, x0: &Expr, eps: &Expr) -> Expr {
        Expr::apps(
            self.single_lp_form.clone(),
            [n.clone(), net.clone(), x0.clone(), eps.clone()],
        )
    }
}

// =============================================================================
// Type builders
// =============================================================================

/// Build type for `NNVerify.C012.pre_activation`:
/// ```text
/// (n : Nat) -> Network -> NNVec n -> NNVec n
/// ```
///
/// Maps an input point to the vector of ReLU pre-activation values whose
/// signs determine the activation pattern.
pub(super) fn build_pre_activation_type(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let (net_id, _) = b.fresh_local(c.network.clone());
    let (x_id, _) = b.fresh_local(vec_n.clone());
    let e = b.mk_pi(x_id, BinderInfo::Default, vec_n.clone(), vec_n);
    let e = b.mk_pi(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build type for `NNVerify.C012.activation_pattern`:
/// ```text
/// (n : Nat) -> NNVec n -> (Fin n -> Bool)
/// ```
///
/// Extracts the on/off ReLU pattern from a vector of pre-activation values.
pub(super) fn build_activation_pattern_type(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let fin_n = c.fin_of(&n);
    let (z_id, _) = b.fresh_local(vec_n.clone());
    let result = Expr::pi(BinderInfo::Default, fin_n, c.bool_.clone());
    let e = b.mk_pi(z_id, BinderInfo::Default, vec_n, result);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build type for `NNVerify.C012.stability_radius`:
/// ```text
/// (n : Nat) -> Network -> NNVec n -> Rat
/// ```
///
/// Intended semantics:
/// `min_i |pre_activation_i(x0)| / Lipschitz_i`, the largest radius that
/// preserves all ReLU signs around `x0`.
pub(super) fn build_stability_radius_type(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let (net_id, _) = b.fresh_local(c.network.clone());
    let (x0_id, _) = b.fresh_local(vec_n);
    let e = b.mk_pi(x0_id, BinderInfo::Default, c.vec_of(&n), c.rat.clone());
    let e = b.mk_pi(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build type for `NNVerify.C012.perturbation_ball`:
/// ```text
/// (n : Nat) -> NNVec n -> Rat -> IntervalBounds n
/// ```
///
/// Internal helper used to state theorems over the region `B(x0, eps)`.
/// Previously an axiom; now Opaque with a zero-IntervalBounds placeholder.
pub(super) fn build_perturbation_ball_type(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let ib_n = c.ib_of(&n);
    let (x0_id, _) = b.fresh_local(vec_n);
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), ib_n);
    let e = b.mk_pi(x0_id, BinderInfo::Default, c.vec_of(&n), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build type for `NNVerify.C012.crown_relaxation_gap`:
/// ```text
/// (n : Nat) -> Network -> IntervalBounds n -> Rat
/// ```
///
/// Measures the total slack introduced by CROWN's ReLU relaxations on
/// an input region.
pub(super) fn build_crown_relaxation_gap_type(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let ib_n = c.ib_of(&n);
    let (net_id, _) = b.fresh_local(c.network.clone());
    let (bnd_id, _) = b.fresh_local(ib_n);
    let e = b.mk_pi(bnd_id, BinderInfo::Default, c.ib_of(&n), c.rat.clone());
    let e = b.mk_pi(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build type for `NNVerify.C012.pattern_stable`:
/// ```text
/// (n : Nat) -> Network -> NNVec n -> Rat -> Prop
/// ```
///
/// Intended semantics: every point in `B(x0, eps)` has the same
/// `activation_pattern` as `x0`, equivalently `eps` is below the local
/// `stability_radius`.
pub(super) fn build_pattern_stable_type(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let (net_id, _) = b.fresh_local(c.network.clone());
    let (x0_id, _) = b.fresh_local(vec_n);
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
    let e = b.mk_pi(x0_id, BinderInfo::Default, c.vec_of(&n), e);
    let e = b.mk_pi(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build type for `NNVerify.C012.single_lp_form`:
/// ```text
/// (n : Nat) -> Network -> NNVec n -> Rat -> Prop
/// ```
///
/// Internal helper predicate meaning verification over `B(x0, eps)` has a
/// single-LP formulation because the ReLU pattern is fixed.
pub(super) fn build_single_lp_form_type(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let (net_id, _) = b.fresh_local(c.network.clone());
    let (x0_id, _) = b.fresh_local(vec_n);
    let (eps_id, _) = b.fresh_local(c.rat.clone());
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), c.prop.clone());
    let e = b.mk_pi(x0_id, BinderInfo::Default, c.vec_of(&n), e);
    let e = b.mk_pi(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the type for `NNVerify.C012.crown_exact_under_stable`:
/// ```text
/// forall (n : Nat) (net : Network) (x0 : NNVec n) (eps : Rat),
///   pattern_stable n net x0 eps ->
///   Eq @Rat
///     (crown_relaxation_gap n net (perturbation_ball n x0 eps))
///     Rat.zero
/// ```
///
/// Fixed ReLU pattern means CROWN introduces no relaxation error on
/// the perturbation ball.
pub(super) fn build_crown_exact_under_stable_type(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let (net_id, net) = b.fresh_local(c.network.clone());
    let (x0_id, x0) = b.fresh_local(vec_n);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let hyp = c.pattern_stable_app(&n, &net, &x0, &eps);
    let (h_id, _) = b.fresh_local(hyp.clone());

    let bnd = c.perturbation_ball_app(&n, &x0, &eps);
    let concl = c.rat_eq(c.crown_gap_app(&n, &net, &bnd), c.rat_zero.clone());

    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x0_id, BinderInfo::Default, c.vec_of(&n), e);
    let e = b.mk_pi(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the type for `NNVerify.C012.lp_reduction`:
/// ```text
/// forall (n : Nat) (net : Network) (x0 : NNVec n) (eps : Rat),
///   pattern_stable n net x0 eps ->
///   single_lp_form n net x0 eps ->
///   single_lp_form n net x0 eps
/// ```
///
/// Hypothesis-wrapped local form: without a faithful LP carrier, the
/// declaration explicitly requires the single-LP fact it returns.
pub(super) fn build_lp_reduction_type(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let (net_id, net) = b.fresh_local(c.network.clone());
    let (x0_id, x0) = b.fresh_local(vec_n);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    let hyp = c.pattern_stable_app(&n, &net, &x0, &eps);
    let (h_id, _) = b.fresh_local(hyp.clone());
    let concl = c.single_lp_form_app(&n, &net, &x0, &eps);
    let (h_lp_id, _) = b.fresh_local(concl.clone());

    let e = b.mk_pi(h_lp_id, BinderInfo::Default, concl.clone(), concl);
    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, e);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x0_id, BinderInfo::Default, c.vec_of(&n), e);
    let e = b.mk_pi(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Proof builders
// =============================================================================

/// Build the proof term for `NNVerify.C012.crown_exact_under_stable`.
///
/// The proof wraps `crown_exact_under_stable_core` in lambdas abstracting
/// over all parameters:
/// ```text
/// fun (n : Nat) (net : Network) (x0 : NNVec n) (eps : Rat)
///     (h : pattern_stable n net x0 eps) =>
///   crown_exact_under_stable_core n net x0 eps h
/// ```
pub(super) fn build_crown_exact_under_stable_proof(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let (net_id, net) = b.fresh_local(c.network.clone());
    let (x0_id, x0) = b.fresh_local(vec_n);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hyp = c.pattern_stable_app(&n, &net, &x0, &eps);
    let (h_id, h) = b.fresh_local(hyp.clone());

    let body = Expr::apps(
        c.crown_exact_under_stable_core.clone(),
        [n.clone(), net.clone(), x0.clone(), eps.clone(), h],
    );

    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(x0_id, BinderInfo::Default, c.vec_of(&n), e);
    let e = b.mk_lam(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

/// Build the proof term for hypothesis-wrapped
/// `NNVerify.C012.lp_reduction`.
///
/// The proof abstracts the local single-LP hypothesis and returns it:
/// ```text
/// fun (n : Nat) (net : Network) (x0 : NNVec n) (eps : Rat)
///     (_h : pattern_stable n net x0 eps)
///     (h_lp : single_lp_form n net x0 eps) =>
///   h_lp
/// ```
pub(super) fn build_lp_reduction_proof(c: &C012Consts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let vec_n = c.vec_of(&n);
    let (net_id, net) = b.fresh_local(c.network.clone());
    let (x0_id, x0) = b.fresh_local(vec_n);
    let (eps_id, eps) = b.fresh_local(c.rat.clone());
    let hyp = c.pattern_stable_app(&n, &net, &x0, &eps);
    let (h_id, _) = b.fresh_local(hyp.clone());
    let concl = c.single_lp_form_app(&n, &net, &x0, &eps);
    let (h_lp_id, h_lp) = b.fresh_local(concl.clone());

    let e = b.mk_lam(h_lp_id, BinderInfo::Default, concl, h_lp);
    let e = b.mk_lam(h_id, BinderInfo::Default, hyp, e);
    let e = b.mk_lam(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_lam(x0_id, BinderInfo::Default, c.vec_of(&n), e);
    let e = b.mk_lam(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_lam(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// NOTE: `build_lp_reduction_constructive_proof` was deleted in the #3579
// Branch A demasquerade of `NNVerify.C012.lp_reduction`. It previously
// produced the 5-binder lambda
// `fun (n : Nat) (net : Network) (x0 : NNVec n) (eps : Rat)
//      (_h : pattern_stable n net x0 eps) => True.intro`,
// which type-checked only because `single_lp_form` was a reducible
// `Declaration::Definition` whose body was `fun _ _ _ _ => True`. Per
// `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M2 + M4, the
// argument-discarding `True` carrier plus the `True.intro` inner proof
// was MASQUERADE: the theorem said nothing about LP reduction, it
// reduced to `True` and was closed by `True.intro`. The current
// `build_lp_reduction_proof` is the honest hypothesis-wrapped replacement:
// it requires an explicit local `single_lp_form` premise and returns that
// premise.
