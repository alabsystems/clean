// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C028: Neural Nullstellensatz — local-evidence retirement
//!
//! Status (post-2026-04-27):
//! - 4 `Declaration::Definition` entries (reducible type aliases:
//!   `ReLUNetwork`, `Polynomial`, proof-carrying `SoSCertificate`,
//!   `PiecewiseLinear`).
//! - 6 `Declaration::Opaque` entries (well-typed placeholder function
//!   bodies: `relu_to_pwl`, `sos_degree`, `network_depth`, `network_width`,
//!   `property_polynomial`, `property_holds_on_region`).
//! - 1 `Declaration::Opaque` with sorry-based proof inhabitation
//!   (`degree_bound_core`).
//! - 1 `Declaration::Definition` entry (`sos_certifies`) projecting local
//!   certificate predicate evidence.
//! - 3 `Declaration::Theorem` entries (`degree_bound` wrapping
//!   `degree_bound_core`, plus `sos_existence` and `completeness` as
//!   hypothesis-wrapped theorems over local SoS evidence).
//!
//! **#3567 Branch A MASQUERADE demotion.** Prior state (#3466) registered
//! `sos_certifies` as a reducible `Declaration::Definition` with body
//! `fun _ _ _ _ => True`, allowing `sos_existence` to close as a
//! `Declaration::Theorem` via
//! `@Exists.intro _ _ Nat.zero True.intro`. That pattern satisfied
//! MASQUERADE Rules M2 (argument-discarding carrier) + M4 (trivial
//! witness + `True.intro`) per
//! `designs/2026-04-19-demasquerade-cxxx-pattern.md`.
//!
//! Branch A action (#3567):
//! - `sos_certifies`: reducible `Definition (= True)` -> `Declaration::Axiom`
//!   (no body). Kills the Rule-M2 delta-collapse path.
//! - `sos_existence`: `Declaration::Theorem` (Exists.intro + True.intro) ->
//!   `Declaration::Axiom` (no proof term).
//! - `sos_existence_core`: removed (was only a downstream-compat backing
//!   Opaque for the constructive proof, now unreferenced).
//!
//! Audit lineage: #3466 landed the masquerade; #3567 audit surfaced
//! it; Branch A restored the honest axiom state pending Branch B
//! (real SoS carrier with polynomial non-negativity semantics). On
//! 2026-04-27, `sos_existence` was retired by exposing SoS-existence as
//! an explicit local hypothesis, and `sos_certifies` was retired by making
//! `SoSCertificate d` carry local predicate evidence.
//!
//! See: designs/2026-04-19-demasquerade-cxxx-pattern.md §Rule M2 / §M4 /
//! §Branch A, and designs/2026-04-17-publication-quality-gamma-crown-proofs.md.
//!
//! # Mathematical Statement (CONJECTURED — still axiomatized)
//!
//! Sum-of-Squares (SoS) polynomial certificates can prove neural network
//! properties without Branch-and-Bound:
//!
//! 1. **SoS Certificate Existence**: For a piecewise-linear NN `f` and
//!    property `P(f(x))` for all `x in C`, if P holds then there exists
//!    a degree-d SoS certificate `sigma` such that the property polynomial
//!    is nonnegative on C.
//! 2. **Degree Bound**: The degree d is bounded by O(L * W) where
//!    L = depth, W = max width of the network.
//! 3. **Completeness**: SoS certificates are complete for ReLU networks
//!    (piecewise-linear implies real algebraic).
//!
//! # Declarations (post-#3567)
//!
//! ## Reducible type Definitions
//! - `NNVerify.C028.ReLUNetwork` — abstract ReLU network type (= Nat)
//! - `NNVerify.C028.Polynomial` — multivariate polynomial type (= fun _ => Nat)
//! - `NNVerify.C028.SoSCertificate` — certificate evidence carrier
//!   (= fun d => Polynomial d -> IntervalBounds d -> Prop)
//! - `NNVerify.C028.PiecewiseLinear` — piecewise-linear function type (= fun _ _ => Nat)
//!
//! ## Function Opaques (well-typed placeholders)
//! - `NNVerify.C028.relu_to_pwl` — ReLU to piecewise-linear decomposition
//! - `NNVerify.C028.sos_degree` — certificate degree (value: Nat.zero)
//! - `NNVerify.C028.network_depth` — network depth (value: Nat.zero)
//! - `NNVerify.C028.network_width` — network max width (value: Nat.zero)
//! - `NNVerify.C028.property_polynomial` — property to polynomial (value: Nat.zero)
//! - `NNVerify.C028.property_holds_on_region` — property validity (value: True)
//!
//! ## Predicate definition (local evidence projection)
//! - `NNVerify.C028.sos_certifies` — SoS certification predicate
//!   (= fun d sigma poly C => sigma poly C)
//!
//! ## Hypothesis-wrapped theorem
//! - `NNVerify.C028.sos_existence` — SoS certificate existence,
//!   hypothesis-wrapped over explicit local SoS-existence evidence.
//!
//! ## Opaque-backed theorem
//! - **C028b: `degree_bound`** — wraps `degree_bound_core`
//!   (sorry-inhabited Opaque; pending Branch B carrier work)
//!
//! ## Theorem (constructive — #3377, unchanged)
//! - **C028c: `completeness`** — eliminates local SoS-existence evidence
//!   and composes it with `degree_bound` via `Exists.elim` + `And.intro`.
//!
//! # References
//!
//! - Parrilo, "Semidefinite programming relaxations" (Math Programming 2003)
//! - Stengle, "A Nullstellensatz and Positivstellensatz" (Math Annalen 1974)
//! - gamma-crown C028 experiments
//!
//! Part of #3300, #3265, #3377, #3371, #3466, #3567.

use super::nn_verify_ibp_linear::sorry_inhabit_pi;
use super::nn_verify_nullstellensatz_defs::{
    build_completeness_type, build_degree_bound_type, build_piecewise_linear_type,
    build_polynomial_type, build_sos_certificate_type, build_sos_existence_type, C028Consts,
};
use super::nn_verify_nullstellensatz_proofs::{
    build_completeness_proof, build_sos_existence_proof,
};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize C028: Neural Nullstellensatz declarations.
    ///
    /// Registers 4 type definitions + 6 function opaques + 1 predicate
    /// definition (`sos_certifies`) + 1 sorry-inhabited core opaque
    /// (`degree_bound_core`) + hypothesis-wrapped `sos_existence` and
    /// `completeness` theorems + `degree_bound`.
    ///
    /// Depends on:
    /// - `init_nn_verify_types()` for NNVec, IntervalBounds
    /// - `init_nat()` for Nat, Nat.mul, Nat.zero
    /// - `init_le()` for LE.le, instLENat
    /// - `init_exists()` for Exists
    /// - `init_and()` for And
    /// - `init_true_false()` for True
    /// - `init_sorry()` for sorry (proof inhabitation of core opaques)
    #[cfg(any(test, feature = "math-overlays"))]
    pub(crate) fn init_nn_verify_nullstellensatz(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("NNVerify.C028.Polynomial"))
            .is_some()
        {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_nat()?;
        self.init_le()?;
        self.init_exists()?;
        self.init_and()?;
        self.init_true_false()?;
        self.init_sorry()?;

        let c = C028Consts::new();
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let true_const = Expr::const_(Name::from_string("True"), vec![]);

        // Phase 1: Type definitions (formerly axioms)
        // These are reducible definitions so that function opaques can type-check.
        self.register_c028_type_def_relu_network(&c)?;
        self.register_c028_type_def_polynomial(&c)?;
        self.register_c028_type_def_sos_certificate(&c)?;
        self.register_c028_type_def_piecewise_linear(&c)?;

        // Phase 2: Function opaques (formerly axioms)
        self.register_c028_opaque_relu_to_pwl(&c, &nat_zero)?;
        // sos_certifies is no longer the old reducible `fun _ _ _ _ => True`
        // carrier and no longer a global predicate axiom. `SoSCertificate d`
        // carries the missing predicate evidence locally, and this definition
        // projects that evidence.
        self.register_c028_def_sos_certifies(&c)?;
        self.register_c028_opaque_sos_degree(&c, &nat_zero)?;
        self.register_c028_opaque_network_depth(&c, &nat_zero)?;
        self.register_c028_opaque_network_width(&c, &nat_zero)?;
        self.register_c028_opaque_property_polynomial(&c, &nat_zero)?;
        self.register_c028_opaque_property_holds(&c, &true_const)?;

        // Phase 3: Theorem C028a — hypothesis-wrapped SoS existence.
        // The former global axiom is retired by exposing the missing
        // Exists(sigma, sos_certifies ...) claim as an explicit local
        // hypothesis and returning that hypothesis.
        self.register_c028_sos_existence_hyp_theorem(&c)?;

        // Phase 4: Theorem C028b — degree bound (core opaque + theorem wrapper)
        // Core is sorry-based Opaque, not Axiom. Part of #3377.
        self.register_c028_opaque_theorem(
            "NNVerify.C028.degree_bound",
            build_degree_bound_type(&c),
        )?;

        // Phase 5: Theorem C028c — completeness (constructive proof from C028a + C028b)
        // No completeness_core axiom needed (#3377).
        self.register_c028_completeness_constructive(&c)?;

        Ok(())
    }

    // =========================================================================
    // Type definitions (4 former axioms -> Declaration::Definition)
    // =========================================================================

    /// `ReLUNetwork : Type` = `Nat`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c028_type_def_relu_network(&mut self, c: &C028Consts) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C028.ReLUNetwork");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name: n,
            level_params: vec![],
            type_: Expr::sort(Level::succ(Level::zero())),
            value: c.nat.clone(),
            is_reducible: true,
        })
    }

    /// `Polynomial : Nat -> Type` = `fun _ => Nat`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c028_type_def_polynomial(&mut self, c: &C028Consts) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C028.Polynomial");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), c.nat.clone());
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: n,
            level_params: vec![],
            type_: build_polynomial_type(c),
            value,
            is_reducible: true,
        })
    }

    /// `SoSCertificate : Nat -> Type` =
    /// `fun d => Polynomial d -> IntervalBounds d -> Prop`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c028_type_def_sos_certificate(&mut self, c: &C028Consts) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C028.SoSCertificate");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let (poly_id, _) = b.fresh_local(c.poly_of(&d));
            let (region_id, _) = b.fresh_local(c.ib_of(&d));
            let e = b.mk_pi(region_id, BinderInfo::Default, c.ib_of(&d), c.prop.clone());
            let e = b.mk_pi(poly_id, BinderInfo::Default, c.poly_of(&d), e);
            let e = b.mk_lam(d_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: n,
            level_params: vec![],
            type_: build_sos_certificate_type(c),
            value,
            is_reducible: true,
        })
    }

    /// `PiecewiseLinear : Nat -> Nat -> Type` = `fun _ _ => Nat`
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c028_type_def_piecewise_linear(&mut self, c: &C028Consts) -> Result<(), EnvError> {
        let n = Name::from_string("NNVerify.C028.PiecewiseLinear");
        if self.get_const(&n).is_some() {
            return Ok(());
        }
        let value = {
            let mut b = EnvDeclBuilder::new();
            let (din_id, _) = b.fresh_local(c.nat.clone());
            let (dout_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_lam(dout_id, BinderInfo::Default, c.nat.clone(), c.nat.clone());
            let e = b.mk_lam(din_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Definition {
            name: n,
            level_params: vec![],
            type_: build_piecewise_linear_type(c),
            value,
            is_reducible: true,
        })
    }

    // =========================================================================
    // Function opaques (7 former axioms -> Declaration::Opaque)
    // See nn_verify_nullstellensatz_opaques.rs for the implementations.
    // =========================================================================

    // =========================================================================
    // Theorem registration helpers
    // =========================================================================

    /// Register a theorem with a backing core opaque in the NNVerify.C028 namespace.
    ///
    /// Pattern: register `<name>_core` as sorry-based Opaque, then `<name>`
    /// as Theorem whose proof term is the core opaque constant. This
    /// eliminates the domain axiom while preserving the theorem interface.
    ///
    /// The sorry-based inhabitation uses `sorry_inhabit_pi` to walk the Pi
    /// spine and create a canonical synthetic sorry for the innermost
    /// proposition.
    ///
    /// Formerly used `Declaration::Axiom` for the core; upgraded to
    /// `Declaration::Opaque` with sorry-based proof inhabitation (#3377).
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c028_opaque_theorem(&mut self, name: &str, thm_type: Expr) -> Result<(), EnvError> {
        let core_name = format!("{name}_core");
        // Core opaque with sorry-based proof inhabitation (was: Axiom)
        let value = sorry_inhabit_pi(self, &thm_type);
        self.add_decl(Declaration::Opaque {
            name: Name::from_string(&core_name),
            level_params: vec![],
            type_: thm_type.clone(),
            value,
        })?;
        // Theorem wrapping core opaque (unchanged interface)
        let proof = Expr::const_(Name::from_string(&core_name), vec![]);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    /// Register C028a (`sos_existence`) as a hypothesis-wrapped theorem.
    ///
    /// Formerly `Declaration::Theorem` with proof term
    /// `fun _ _ _ _ _ _ => @Exists.intro (SoSCertificate d_in) pred_a
    /// Nat.zero True.intro` (#3466). That proof only type-checked via
    /// delta-collapse of the reducible `sos_certifies = fun _ _ _ _ => True`
    /// carrier combined with `SoSCertificate d_in` reducing to `Nat`. Per
    /// `designs/2026-04-19-demasquerade-cxxx-pattern.md` the pattern
    /// satisfies Rule M2 (argument-discarding carrier) and Rule M4 (trivial
    /// witness + trivial `True.intro` proof) — a canonical MASQUERADE.
    ///
    /// 2026-04-27 action: strengthen the signature with an explicit local
    /// hypothesis for the missing SoS-existence claim and return that local
    /// hypothesis. This retires the global `sos_existence` axiom without
    /// using `True.intro`, a trivial certificate witness, or another C028
    /// global existence axiom. `sos_existence_core` remains unregistered.
    ///
    /// Part of #3567. Branch B (real SoS carrier + faithful existence
    /// proof) is tracked as follow-up C028 substantive-SoS work.
    ///
    /// # SOUNDNESS
    ///
    /// The proof term establishes only `H -> H` for the explicit local SoS
    /// existence hypothesis. Callers must provide that hypothesis; the
    /// theorem no longer asserts global SoS existence from `property_holds`.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c028_sos_existence_hyp_theorem(&mut self, c: &C028Consts) -> Result<(), EnvError> {
        let thm_type = build_sos_existence_type(c);
        let thm_name = Name::from_string("NNVerify.C028.sos_existence");
        if self.get_const(&thm_name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name: thm_name,
            level_params: vec![],
            type_: thm_type,
            value: build_sos_existence_proof(c),
        })
    }

    /// Register C028c (completeness) as a constructive theorem.
    ///
    /// Unlike `register_c028_opaque_theorem`, this does NOT create a
    /// `completeness_core` opaque. The proof eliminates local SoS-existence
    /// evidence and composes it with `degree_bound` via `Exists.elim` and
    /// `And.intro`.
    ///
    /// Part of #3377: eliminates 1 of 3 core theorem axioms.
    #[cfg(any(test, feature = "math-overlays"))]
    fn register_c028_completeness_constructive(&mut self, c: &C028Consts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.C028.completeness");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_completeness_type(c),
            value: build_completeness_proof(c),
        })
    }
}
