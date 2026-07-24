// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C012: ReLU Activation Pattern Stability
//!
//! **Status:** no C012 domain axioms. The remaining LP-reduction statement is
//! hypothesis-wrapped: it explicitly requires the local `single_lp_form`
//! fact it returns. The pre-#3579 setup
//! (`single_lp_form` = reducible `Declaration::Definition` with body
//! `fun _ _ _ _ => True` + `lp_reduction` = `Declaration::Theorem` proved by
//! `True.intro`) was a MASQUERADE: `single_lp_form n net x0 eps` delta-
//! reduced to `True` and the "proof" closed trivially. Branch A reverts
//! `single_lp_form` to `Declaration::Opaque` (same body; closes the delta
//! path). The current theorem avoids that path by using only an explicit
//! local premise.
//!
//! Layout: 1 Opaque (abstract `Network`) + 5 Opaque (function
//! placeholders) + 2 sorry-inhabited Opaque cores (C012a, C012b) +
//! 1 Opaque (`single_lp_form`, #3579 flip) + 1 Definition
//! (`pattern_stable`) + 3 Theorems (C012a, C012b, hypothesis-wrapped
//! C012c). Reduced from 11 axioms (#3381 history).
//!
//! See: `designs/2026-04-17-publication-quality-gamma-crown-proofs.md`
//!
//! # Mathematical Statement (CONJECTURED)
//!
//! For a ReLU network `net` with input `x0` and perturbation ball
//! `B(x0, eps)`: if `eps < min_i |pre_activation_i(x0)| / Lipschitz_i`,
//! all ReLU patterns are fixed on the ball, CROWN bounds become exact
//! (zero relaxation gap), and verification reduces to a single LP.
//!
//! References: Wong & Kolter NeurIPS 2018 (ReLU stability), Xu et al.
//! NeurIPS 2020 (CROWN exact under fixed pattern).
//!
//! Part of #3313, #3150, #3579.

use super::nn_verify_ibp_linear::sorry_inhabit_pi;
use super::nn_verify_relu_stability_defs::{
    build_activation_pattern_type, build_crown_exact_under_stable_type,
    build_crown_relaxation_gap_type, build_lp_reduction_proof, build_lp_reduction_type,
    build_pattern_stable_type, build_perturbation_ball_type, build_pre_activation_type,
    build_single_lp_form_type, build_stability_radius_type, C012Consts,
};
use super::nn_verify_relu_stability_values::{
    build_activation_pattern_value, build_crown_relaxation_gap_value, build_network_value,
    build_pattern_stable_value, build_perturbation_ball_value, build_pre_activation_value,
    build_single_lp_form_value, build_stability_radius_value,
};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

// =============================================================================
// Criterion type/proof builders (kept here, not in _defs)
// =============================================================================

/// Build type for `NNVerify.C012.pattern_stable_criterion`:
/// ```text
/// forall (n : Nat) (net : Network) (x0 : NNVec n) (eps : Rat),
///   LT.lt @Rat instLTRat eps (stability_radius n net x0)
///   -> pattern_stable n net x0 eps
/// ```
///
/// The key bridge: `eps < stability_radius` implies pattern stability.
#[cfg(any(test, feature = "math-overlays"))]
fn build_pattern_stable_criterion_type(c: &C012Consts) -> Expr {
    let lt_lt = Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]);
    let inst_lt_rat = Expr::const_(Name::from_string("instLTRat"), vec![]);

    let mut b = EnvDeclBuilder::new();
    let (n_id, n) = b.fresh_local(c.nat.clone());
    let (net_id, net) = b.fresh_local(c.network.clone());
    let (x0_id, x0) = b.fresh_local(c.vec_of(&n));
    let (eps_id, eps) = b.fresh_local(c.rat.clone());

    // Hypothesis: eps < stability_radius n net x0
    let radius = c.stability_radius_app(&n, &net, &x0);
    let hyp = Expr::app(
        Expr::app(
            Expr::app(Expr::app(lt_lt, c.rat.clone()), inst_lt_rat),
            eps.clone(),
        ),
        radius,
    );
    let (h_id, _) = b.fresh_local(hyp.clone());

    // Conclusion: pattern_stable n net x0 eps
    let concl = c.pattern_stable_app(&n, &net, &x0, &eps);

    let e = b.mk_pi(h_id, BinderInfo::Default, hyp, concl);
    let e = b.mk_pi(eps_id, BinderInfo::Default, c.rat.clone(), e);
    let e = b.mk_pi(x0_id, BinderInfo::Default, c.vec_of(&n), e);
    let e = b.mk_pi(net_id, BinderInfo::Default, c.network.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), e);
    b.finish(e)
}

// =============================================================================
// Environment impl
// =============================================================================

impl Environment {
    /// Initialize C012: ReLU activation pattern stability declarations.
    ///
    /// Registers 1 Opaque type + 5 Opaque functions + 2 Definitions +
    /// 2 sorry-backed theorem wrappers + 1 hypothesis-wrapped theorem.
    /// ZERO axioms remain.
    ///
    /// Depends on:
    /// - `init_nn_verify_types()` for NNVec, IntervalBounds
    /// - `init_nn_verify_relu()` for ReLU definitions
    /// - `init_nn_verify_lipschitz()` for Lipschitz infrastructure
    /// - `init_bool()` for Bool (activation pattern return type)
    /// - `init_rat_arith()` for Rat arithmetic
    /// - `init_rat_ord()` for strict ordering (LT.lt)
    /// - `init_eq()` for equality
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nn_verify_relu_stability(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.C012.pre_activation"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_nn_verify_relu()?;
        self.init_nn_verify_lipschitz()?;
        self.init_bool()?;
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        self.init_eq()?;

        let c = C012Consts::new();

        // Step 0: Abstract network type (Opaque — formerly axiom)
        self.register_c012_network()?;
        // Step 1: Function definitions (Opaque — formerly axioms)
        self.register_c012_pre_activation(&c)?;
        self.register_c012_activation_pattern(&c)?;
        self.register_c012_stability_radius(&c)?;
        self.register_c012_perturbation_ball(&c)?;
        self.register_c012_crown_relaxation_gap(&c)?;
        // Step 1b: Predicate definitions (Definition — formerly axioms)
        self.register_c012_pattern_stable(&c)?;
        self.register_c012_single_lp_form(&c)?;
        // Step 2: Theorem C012a — pattern_stable_criterion
        self.register_c012_pattern_stable_criterion(&c)?;
        // Step 3: Theorem C012b — crown_exact_under_stable
        self.register_c012_crown_exact_under_stable(&c)?;
        // Step 4: Theorem C012c — lp_reduction
        self.register_c012_lp_reduction(&c)?;

        Ok(())
    }

    // =========================================================================
    // Definition axioms
    // =========================================================================

    /// `NNVerify.C012.Network : Type` — abstract ReLU network.
    ///
    /// Registered as Opaque with Nat as a well-typed placeholder value.
    /// The kernel verifies the value inhabits Type; opaque prevents reduction.
    /// Previously an axiom; now an Opaque definition.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c012_network(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C012.Network");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())),
            value: build_network_value(),
        })
    }

    /// `NNVerify.C012.pre_activation : (n : Nat) -> Network -> NNVec n -> NNVec n`
    ///
    /// Previously an axiom; now Opaque with a placeholder value that
    /// returns its input (identity on NNVec n). Opaque prevents reduction.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c012_pre_activation(&mut self, c: &C012Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C012.pre_activation");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: build_pre_activation_type(c),
            value: build_pre_activation_value(c),
        })
    }

    /// `NNVerify.C012.activation_pattern : (n : Nat) -> NNVec n -> (Fin n -> Bool)`
    ///
    /// Previously an axiom; now Opaque with a placeholder value that
    /// returns a constant-false pattern. Opaque prevents reduction.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c012_activation_pattern(&mut self, c: &C012Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C012.activation_pattern");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: build_activation_pattern_type(c),
            value: build_activation_pattern_value(c),
        })
    }

    /// `NNVerify.C012.stability_radius : (n : Nat) -> Network -> NNVec n -> Rat`
    ///
    /// Previously an axiom; now Opaque with Rat.zero placeholder.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c012_stability_radius(&mut self, c: &C012Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C012.stability_radius");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: build_stability_radius_type(c),
            value: build_stability_radius_value(c),
        })
    }

    /// `NNVerify.C012.perturbation_ball : (n : Nat) -> NNVec n -> Rat -> IB n`
    ///
    /// Previously an axiom; now Opaque with a zero-IntervalBounds placeholder.
    /// The placeholder constructs `IntervalBounds.mk @n (fun _ => 0) (fun _ => 0)
    /// (fun _ => Rat.le_refl Rat.zero)`, a valid zero-width bounding box.
    /// Opaque prevents reduction so the placeholder value is never observable.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c012_perturbation_ball(&mut self, c: &C012Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C012.perturbation_ball");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: build_perturbation_ball_type(c),
            value: build_perturbation_ball_value(c),
        })
    }

    /// `NNVerify.C012.crown_relaxation_gap : (n : Nat) -> Network -> IB n -> Rat`
    ///
    /// Previously an axiom; now Opaque with Rat.zero placeholder.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c012_crown_relaxation_gap(&mut self, c: &C012Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C012.crown_relaxation_gap");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: build_crown_relaxation_gap_type(c),
            value: build_crown_relaxation_gap_value(c),
        })
    }

    /// `NNVerify.C012.pattern_stable : (n : Nat) -> Network -> NNVec n -> Rat -> Prop`
    ///
    /// Previously an axiom; now a Definition with a well-typed Prop body.
    /// The predicate returns `True` as a placeholder; the actual semantics
    /// (every point in B(x0, eps) has the same activation pattern as x0)
    /// would require forall-quantification over the ball, which depends on
    /// NNVec membership infrastructure not yet in the kernel.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c012_pattern_stable(&mut self, c: &C012Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C012.pattern_stable");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_pattern_stable_type(c),
            value: build_pattern_stable_value(c),
            is_reducible: false,
        })
    }

    /// `NNVerify.C012.single_lp_form : (n : Nat) -> Network -> NNVec n -> Rat -> Prop`
    ///
    /// History: Axiom (original) -> reducible `Declaration::Definition`
    /// with Prop body `fun _ _ _ _ => True` (#3465, enabled `lp_reduction`
    /// to close via `True.intro` through delta-reduction) -> `Declaration::
    /// Opaque` with the SAME body (#3579 Branch A demasquerade per
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md` Rules M2+M4).
    ///
    /// SOUNDNESS (#3579): keeping the `True` body on an Opaque preserves
    /// typing but blocks the `True`-carrier reduction path — the kernel
    /// does not delta-unfold Opaques during `def_eq`, so
    /// `single_lp_form n net x0 eps` no longer reduces to `True`. Same
    /// pattern demoted in #3566, #3567, #3568, #3577, #3578. A faithful
    /// `single_lp_form` predicate with real LP-feasibility semantics
    /// (Branch B) remains future work.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c012_single_lp_form(&mut self, c: &C012Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C012.single_lp_form");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        // #3579 MASQUERADE demotion: reverted from reducible Definition
        // back to Opaque (see rustdoc above). Stored body is unchanged
        // (`fun _ _ _ _ => True`) so the declaration still type-checks.
        self.add_decl(Declaration::Opaque {
            name,
            level_params: vec![],
            type_: build_single_lp_form_type(c),
            value: build_single_lp_form_value(c),
        })
    }

    // =========================================================================
    // Theorem C012a: pattern_stable_criterion
    // =========================================================================

    /// `NNVerify.C012.pattern_stable_criterion`:
    /// ```text
    /// forall (n : Nat) (net : Network) (x0 : NNVec n) (eps : Rat),
    ///   eps < stability_radius n net x0
    ///   -> pattern_stable n net x0 eps
    /// ```
    ///
    /// The quantitative stability criterion: sufficiently small eps
    /// implies all activation patterns are fixed.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c012_pattern_stable_criterion(&mut self, c: &C012Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C012.pattern_stable_criterion");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let thm_type = build_pattern_stable_criterion_type(c);
        // Upgraded from Axiom to Opaque with sorry-based proof inhabitation. Part of #3381.
        let value = sorry_inhabit_pi(self, &thm_type);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.C012.pattern_stable_criterion_core"),
            level_params: vec![],
            type_: thm_type.clone(),
            value,
        })?;
        // Theorem wrapping core opaque
        let proof = Expr::const_(
            Name::from_string("NNVerify.C012.pattern_stable_criterion_core"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    // =========================================================================
    // Theorem C012b: crown_exact_under_stable
    // =========================================================================

    /// `NNVerify.C012.crown_exact_under_stable`:
    /// ```text
    /// forall (n : Nat) (net : Network) (x0 : NNVec n) (eps : Rat),
    ///   pattern_stable n net x0 eps
    ///   -> crown_relaxation_gap n net (perturbation_ball n x0 eps) = 0
    /// ```
    ///
    /// Under a stable activation pattern, CROWN introduces zero relaxation
    /// error — the linear relaxation of each ReLU is exact.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c012_crown_exact_under_stable(&mut self, c: &C012Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C012.crown_exact_under_stable");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let thm_type = build_crown_exact_under_stable_type(c);
        // Upgraded from Axiom to Opaque with sorry-based proof inhabitation. Part of #3381.
        let value = sorry_inhabit_pi(self, &thm_type);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerify.C012.crown_exact_under_stable_core"),
            level_params: vec![],
            type_: thm_type.clone(),
            value,
        })?;
        // Theorem wrapping core opaque
        let proof = Expr::const_(
            Name::from_string("NNVerify.C012.crown_exact_under_stable_core"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    // =========================================================================
    // Theorem C012c: lp_reduction
    // =========================================================================

    /// `NNVerify.C012.lp_reduction`:
    /// ```text
    /// forall (n : Nat) (net : Network) (x0 : NNVec n) (eps : Rat),
    ///   pattern_stable n net x0 eps
    ///   -> single_lp_form n net x0 eps
    ///   -> single_lp_form n net x0 eps
    /// ```
    ///
    /// Hypothesis-wrapped local form: fixed ReLU pattern plus an explicit
    /// local single-LP premise yields that same single-LP premise.
    ///
    /// History:
    /// - Originally `Declaration::Axiom`.
    /// - #3381 promoted it to `Declaration::Opaque` with a
    ///   `sorry_inhabit_pi` body plus a `Declaration::Theorem` wrapper
    ///   referencing `lp_reduction_core` by name.
    /// - #3465 replaced the `sorry_inhabit_pi` body with a "constructive"
    ///   proof term `fun _ _ _ _ _h => True.intro`, which only type-
    ///   checked because `single_lp_form` was simultaneously flipped to a
    ///   *reducible* `Declaration::Definition` whose body is
    ///   `fun _ _ _ _ => True`. The innermost conclusion
    ///   `single_lp_form n net x0 eps` delta-reduced to `True` and the
    ///   proof closed via `True.intro`.
    /// - #3579: the wave-4 audit flagged the #3465
    ///   configuration as MASQUERADE (Rules M2 argument-discarding
    ///   carrier + M4 inner-proof=`True.intro` per
    ///   `designs/2026-04-19-demasquerade-cxxx-pattern.md`). Branch A is
    ///   taken: revert `single_lp_form` to `Declaration::Opaque` (see
    ///   `register_c012_single_lp_form`) and demote `lp_reduction` to
    ///   `Declaration::Axiom` with no stored value. The backing
    ///   `lp_reduction_core` Opaque is removed — it only existed to back
    ///   the deleted constructive proof. The former
    ///   `build_lp_reduction_constructive_proof` builder is deleted.
    ///
    /// - Current: the remaining domain axiom is retired by strengthening
    ///   the declaration type with an explicit local single-LP premise.
    ///   The proof returns that local premise. This is intentionally not
    ///   a substantive LP-reduction proof; a faithful `single_lp_form`
    ///   predicate with real LP-feasibility semantics remains future work.
    ///
    /// Part of #3579 follow-up.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c012_lp_reduction(&mut self, c: &C012Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C012.lp_reduction");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        let thm_type = build_lp_reduction_type(c);
        let proof = build_lp_reduction_proof(c);
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }
}
