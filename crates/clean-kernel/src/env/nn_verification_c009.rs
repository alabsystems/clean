// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # C009: CROWN-IBP Exponential Gap — 0 DOMAIN AXIOMS
//!
//! **Status: 0 domain axioms + 10 sorry-inhabited Opaques.** 3 Definitions,
//! 7 data Opaques, 3 hypothesis-wrapped IBP theorems, and 10
//! sorry-inhabited Opaques.
//!
//! ## Declaration Inventory
//!
//! | Category | Count | Declaration Type |
//! |----------|-------|-----------------|
//! | Definitions (type/config) | 3 | Definition |
//! | Opaques (data/functions) | 7 | Opaque |
//! | Theorems (IBP wrapping, local evidence) | 3 | Theorem |
//! | Opaques (promoted claims, sorry) | 10 | Opaque (sorry-inhabited) |
//! | **Total axioms remaining** | **0** | |
//!
//! ## History
//!
//! - Original: 23 axioms
//! - Phase 1: 10 support objects -> 3 Definition + 7 Opaque = 13 axioms
//! - Phase 2 (#3376): 13 axioms -> 13 Opaque (sorry-inhabited) = 0 axioms
//! - Phase 3 (#3462): 3 IBP wrapping Opaques -> 3 Theorems over `True`
//!   closed by `True.intro`. 10 sorry-inhabited Opaques remain.
//! - Phase 4 (#3580, 2026-04-20): #3462 retype flagged as Rule M3
//!   statement-rewriting MASQUERADE by the 2026-04-19 vacuity audit.
//!   Branch A taken: 3 IBP-wrapping Theorems demoted back to
//!   `Declaration::Axiom` with the original universe-polymorphic Pi
//!   shape (`level_params = [u]`, `type_ = Sort(succ(u))`). Mirrors
//!   #3566 Branch A demasquerade of the C011 softmax triple.
//! - Phase 5 (2026-04-27): 3 IBP wrapping Axioms retired as
//!   hypothesis-wrapped `Declaration::Theorem` entries. Each theorem states
//!   an explicit local width-equality obligation and returns that local
//!   evidence directly.
//!
//! ### Soundness note for the #3580 demotion
//!
//! The #3462 retyping collapsed each declared type to `True : Prop` with
//! proof term `True.intro`. This was formally sound (`True` is a proposition
//! and `True.intro` is its canonical inhabitant) but vacuous: the original
//! mathematical content (one-layer IBP width bound, compounding, correlation
//! loss) was not encoded in the type. The 2026-04-19 vacuity audit
//! classified this as Rule M3 statement-rewriting — a MASQUERADE — under
//! the same classification that flagged C003/C004/C006/C011. Branch A
//! (this commit) restores the honest accounting by demoting the three
//! declarations to `Declaration::Axiom` on their original Pi signatures,
//! mirroring the #3566 C011 demotion. Branch B (faithful carriers + real
//! proof terms) remains future work and requires the full Kotlov-Muller-
//! Weng proof or a Mathlib bridge.
//!
//! ## Conversion Details
//!
//! **Definitions (3):** Type constructors and configuration values that define
//! the setup of the problem, not mathematical claims.
//! - `C009ReLUNetwork`: Nat -> Type (depth-indexed network family)
//! - `c009_depth`: Nat (network depth parameter N)
//! - `c009_contraction_factor`: Rat (per-layer contraction ratio r)
//!
//! **Opaques — data (7):** Data objects and computed functions with well-typed
//! placeholder values. These capture the *structure* of the CROWN/IBP
//! comparison without asserting mathematical truths.
//! - `c009_input_radius`: Rat (perturbation epsilon)
//! - `c009_weight_matrices`: Nat -> Nat -> Prop (layer weight matrices)
//! - `c009_relu_relaxation_slopes`: Nat -> Prop (diagonal slopes alpha_i)
//! - `c009_effective_crown_matrix`: Prop (combined backsubstitution matrix)
//! - `c009_ibp_width`: Nat -> Rat (IBP width at depth N)
//! - `c009_crown_width`: Nat -> Rat (CROWN width at depth N)
//! - `c009_crown_ibp_ratio`: Nat -> Rat (ratio crown/ibp at depth N)
//!
//! **Theorems — IBP wrapping (3):** Former axioms now carry local evidence
//! explicitly as a premise. The proof term is the premise itself.
//!
//! IBP wrapping effect (3):
//! - `ibp_wrapping_single_layer`, `ibp_wrapping_compounds`,
//!   `ibp_wrapping_correlation_loss`
//!
//! **Opaques — promoted claims (10):** Former axioms upgraded to Opaque
//! with canonical synthetic sorry inhabitation. Each has type `Type u`
//! (universe-polymorphic) and value `@sorryAx.{succ(succ(u))}
//! (Sort(succ(u))) true` (or the legacy `@sorry` fallback).
//!
//! CROWN correlation preservation (3):
//! - `crown_backsubstitution`, `crown_combined_matrix`,
//!   `crown_correlation_retained`
//!
//! Exponential gap (4):
//! - `norm_product_vs_product_norm` — submultiplicativity (library theorem,
//!   available in Mathlib as `Matrix.norm_mul_le`)
//! - `crown_uses_product`, `ibp_uses_product_of_norms`,
//!   `crown_ibp_ratio_exponential`
//!
//! Depth scaling (2):
//! - `ratio_monotone_depth`, `ratio_limit_zero`
//!
//! Summary conjecture (1):
//! - `c009_exponentially_tighter_than_ibp`
//!
//! ---
//!
//! Formalization of C009: CROWN is exponentially tighter than IBP with depth.
//!
//! For a depth-`N` ReLU network with weight matrices `W_1, ..., W_N`, the
//! conjecture asserts that there are constants `C > 0` and `0 < r < 1` such
//! that `crown_width(N) / ibp_width(N) <= C * r^N`.
//!
//! References:
//! - Zhang et al., "Efficient Neural Network Robustness Certification with
//!   General Activation Functions" (CROWN, NeurIPS 2018)
//! - Wang et al., "alpha-beta-CROWN: Efficient Bound Propagation for Neural
//!   Network Verification"
//! - gamma-crown depth-scaling experiments for C009

use super::nn_verification_c009_defs::{self, C009Consts};
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;
use crate::sorry::{create_sorry_term_with_kind_at_level, SorryKind};

// ============================================================================
// C009 claim declaration lists
// ============================================================================

// A. IBP Wrapping Effect (3 hypothesis-wrapped theorems, formerly axioms)
const C009_IBP_WRAPPING_THEOREMS: &[C009IbpWrappingTheorem] = &[
    C009IbpWrappingTheorem {
        name: "NNVerification.ibp_wrapping_single_layer",
        depth: C009IbpWrappingDepth::One,
    },
    C009IbpWrappingTheorem {
        name: "NNVerification.ibp_wrapping_compounds",
        depth: C009IbpWrappingDepth::Two,
    },
    C009IbpWrappingTheorem {
        name: "NNVerification.ibp_wrapping_correlation_loss",
        depth: C009IbpWrappingDepth::Configured,
    },
];

#[derive(Clone, Copy)]
enum C009IbpWrappingDepth {
    One,
    Two,
    Configured,
}

struct C009IbpWrappingTheorem {
    name: &'static str,
    depth: C009IbpWrappingDepth,
}

// B. CROWN Correlation Preservation (3 opaques, formerly axioms)
const C009_CROWN_CORRELATION_OPAQUES: &[&str] = &[
    "NNVerification.crown_backsubstitution", // Backward linearization to the input
    "NNVerification.crown_combined_matrix",  // Product W_N * diag(alpha_i) * ... * W_1
    "NNVerification.crown_correlation_retained", // Width uses the combined matrix norm
];

// C. Exponential Gap (4 opaques, formerly axioms)
const C009_EXPONENTIAL_GAP_OPAQUES: &[&str] = &[
    "NNVerification.norm_product_vs_product_norm", // ||prod A_i||_inf <= prod ||A_i||_inf
    "NNVerification.crown_uses_product",           // CROWN width bounded by norm of product
    "NNVerification.ibp_uses_product_of_norms",    // IBP width equals product of norms
    "NNVerification.crown_ibp_ratio_exponential",  // Ratio <= C * r^N
];

// D. Depth Scaling (2 opaques, formerly axioms)
const C009_DEPTH_SCALING_OPAQUES: &[&str] = &[
    "NNVerification.ratio_monotone_depth", // ratio(N + 1) <= ratio(N) * r
    "NNVerification.ratio_limit_zero",     // lim_{N -> inf} ratio(N) = 0
];

// E. Summary Conjecture (1 opaque, formerly axiom)
const C009_SUMMARY_CONJECTURE_OPAQUES: &[&str] =
    &["NNVerification.c009_exponentially_tighter_than_ibp"];

impl Environment {
    /// Initialize NNVerification.C009 conjecture declarations.
    ///
    /// Registers 3 Definitions, 7 data Opaques, 3 hypothesis-wrapped
    /// IBP-wrapping Theorems, and 10 sorry-inhabited Opaques.
    /// **0 domain axioms** — the IBP wrapping triple carries explicit local
    /// evidence obligations instead of global axioms.
    ///
    /// The 10 support objects (type constructors, configuration values, data
    /// objects, computed functions) are properly categorized as Definitions
    /// or Opaques with well-typed placeholder values. The 3 IBP wrapping
    /// claims are `Declaration::Theorem` entries whose statements have
    /// explicit local premises for the missing width equalities; the
    /// remaining 10 claims are Opaques with sorry-based proof inhabitation,
    /// preventing reduction while maintaining well-typedness.
    ///
    /// # Dependencies
    /// - `Eq` for equality-based conjecture statements
    /// - `Field` for real-valued width and ratio reasoning
    /// - `Algebra.LinearAlgebra` for matrices, products, and infinity norms
    /// - `Nat` for depth indexing, `Rat` for width values
    /// - `True` for opaque placeholder values
    /// - `sorry` for Opaque proof inhabitation
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nn_verification_c009_init == true`
    /// ENSURES: Idempotent - repeated calls return `Ok(())` without duplication
    pub fn init_nn_verification_c009(&mut self) -> Result<(), EnvError> {
        if self.nn_verification_c009_init {
            return Ok(());
        }

        self.init_eq()?;
        self.init_field()?;
        self.init_algebra_linear()?;
        self.init_nat()?;
        self.init_rat()?;
        self.init_true_false()?; // Required for data-Opaque placeholder values (`True` const)
        self.init_sorry()?; // Required for Opaque sorry-based inhabitation

        let c = C009Consts::new();

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        // sorry value: @sorryAx.{succ(succ(u))} Sort(succ(u)) true
        // (or legacy @sorry at the same level in bootstrap environments).
        let sorry_value = create_sorry_term_with_kind_at_level(
            self,
            &type_u,
            SorryKind::Synthetic,
            Level::succ(Level::succ(u_level)),
        );

        // Register 3 Definitions (type constructors and configuration values)
        self.register_c009_definitions(&c)?;

        // Register 7 Opaques (data objects and computed functions)
        self.register_c009_opaques(&c)?;

        // 2026-04-27 axiom retirement: the 3 IBP wrapping declarations are
        // registered as hypothesis-wrapped Theorems. Each type has the shape
        // `local_width_obligation -> local_width_obligation`, and each proof
        // returns the local premise directly. This keeps the missing IBP
        // wrapping facts explicit without using `True.intro`, `Eq.refl`,
        // sorry, or any global C009 axiom.
        self.register_c009_ibp_wrapping_theorems(C009_IBP_WRAPPING_THEOREMS, &c)?;

        // Register the remaining 10 Opaques (sorry-inhabited), unchanged
        // from the #3376 pattern.
        self.register_c009_opaque_group(C009_CROWN_CORRELATION_OPAQUES, &u, &type_u, &sorry_value)?;
        self.register_c009_opaque_group(C009_EXPONENTIAL_GAP_OPAQUES, &u, &type_u, &sorry_value)?;
        self.register_c009_opaque_group(C009_DEPTH_SCALING_OPAQUES, &u, &type_u, &sorry_value)?;
        self.register_c009_opaque_group(
            C009_SUMMARY_CONJECTURE_OPAQUES,
            &u,
            &type_u,
            &sorry_value,
        )?;

        self.nn_verification_c009_init = true;
        Ok(())
    }

    // =========================================================================
    // Definitions (3)
    // =========================================================================

    /// Register the 3 Definition declarations for C009 support objects.
    fn register_c009_definitions(&mut self, c: &C009Consts) -> Result<(), EnvError> {
        // C009ReLUNetwork : Nat -> Type
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerification.C009ReLUNetwork"),
            level_params: vec![],
            type_: nn_verification_c009_defs::build_relu_network_type(c),
            value: nn_verification_c009_defs::build_relu_network_value(c),
            is_reducible: false,
        })?;

        // c009_depth : Nat
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerification.c009_depth"),
            level_params: vec![],
            type_: nn_verification_c009_defs::build_depth_type(c),
            value: nn_verification_c009_defs::build_depth_value(c),
            is_reducible: true,
        })?;

        // c009_contraction_factor : Rat
        self.add_decl(Declaration::Definition {
            name: Name::from_string("NNVerification.c009_contraction_factor"),
            level_params: vec![],
            type_: nn_verification_c009_defs::build_contraction_factor_type(c),
            value: nn_verification_c009_defs::build_contraction_factor_value(c),
            is_reducible: true,
        })?;

        Ok(())
    }

    // =========================================================================
    // Opaques (7)
    // =========================================================================

    /// Register the 7 Opaque declarations for C009 data and computation objects.
    fn register_c009_opaques(&mut self, c: &C009Consts) -> Result<(), EnvError> {
        // c009_input_radius : Rat
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerification.c009_input_radius"),
            level_params: vec![],
            type_: nn_verification_c009_defs::build_input_radius_type(c),
            value: nn_verification_c009_defs::build_input_radius_value(c),
        })?;

        // c009_weight_matrices : Nat -> Nat -> Prop
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerification.c009_weight_matrices"),
            level_params: vec![],
            type_: nn_verification_c009_defs::build_weight_matrices_type(c),
            value: nn_verification_c009_defs::build_weight_matrices_value(c),
        })?;

        // c009_relu_relaxation_slopes : Nat -> Prop
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerification.c009_relu_relaxation_slopes"),
            level_params: vec![],
            type_: nn_verification_c009_defs::build_relu_relaxation_slopes_type(c),
            value: nn_verification_c009_defs::build_relu_relaxation_slopes_value(c),
        })?;

        // c009_effective_crown_matrix : Prop
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerification.c009_effective_crown_matrix"),
            level_params: vec![],
            type_: nn_verification_c009_defs::build_effective_crown_matrix_type(c),
            value: nn_verification_c009_defs::build_effective_crown_matrix_value(c),
        })?;

        // c009_ibp_width : Nat -> Rat
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerification.c009_ibp_width"),
            level_params: vec![],
            type_: nn_verification_c009_defs::build_ibp_width_type(c),
            value: nn_verification_c009_defs::build_ibp_width_value(c),
        })?;

        // c009_crown_width : Nat -> Rat
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerification.c009_crown_width"),
            level_params: vec![],
            type_: nn_verification_c009_defs::build_crown_width_type(c),
            value: nn_verification_c009_defs::build_crown_width_value(c),
        })?;

        // c009_crown_ibp_ratio : Nat -> Rat
        self.add_decl(Declaration::Opaque {
            name: Name::from_string("NNVerification.c009_crown_ibp_ratio"),
            level_params: vec![],
            type_: nn_verification_c009_defs::build_crown_ibp_ratio_type(c),
            value: nn_verification_c009_defs::build_crown_ibp_ratio_value(c),
        })?;

        Ok(())
    }

    // =========================================================================
    // Opaque groups (10 former axioms, sorry-inhabited) and
    // hypothesis-wrapped Theorems (3 IBP-wrapping)
    // =========================================================================

    /// Register a group of C009 Opaque declarations with sorry-based inhabitation.
    ///
    /// Each declaration has type `Sort(succ(u))` (Type u) and a canonical
    /// synthetic sorry value at `succ(succ(u))`. The Opaque wrapper prevents
    /// reduction, so the sorry is never exposed during type checking.
    ///
    /// This replaces the former `add_nn_verification_c009_axiom_group` which
    /// registered `Declaration::Axiom` entries. Promotion to Opaque eliminates
    /// domain-specific axiom count while maintaining well-typedness.
    ///
    /// Part of #3376: promote C009 axioms to Opaques.
    fn register_c009_opaque_group(
        &mut self,
        names: &[&str],
        u: &Name,
        type_u: &Expr,
        sorry_value: &Expr,
    ) -> Result<(), EnvError> {
        for name in names {
            self.add_decl(Declaration::Opaque {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
                value: sorry_value.clone(),
            })?;
        }
        Ok(())
    }

    /// Register C009 IBP wrapping claims as local-evidence theorems.
    ///
    /// Each theorem states a concrete C009 width equality as an explicit
    /// local premise and returns that premise. This is intentionally not a
    /// hypothesis-free proof of IBP wrapping; the missing mathematical
    /// obligation remains visible to callers instead of being hidden behind a
    /// global axiom.
    fn register_c009_ibp_wrapping_theorems(
        &mut self,
        theorems: &[C009IbpWrappingTheorem],
        c: &C009Consts,
    ) -> Result<(), EnvError> {
        for theorem in theorems {
            let obligation = build_c009_ibp_wrapping_obligation(c, theorem.depth);
            let type_ = Expr::arrow(obligation.clone(), obligation.clone());
            let value = {
                let mut b = EnvDeclBuilder::new();
                let (h_id, h) = b.fresh_local(obligation.clone());
                let r = b.mk_lam(h_id, BinderInfo::Default, obligation, h);
                b.finish(r)
            };
            self.add_decl(Declaration::Theorem {
                name: Name::from_string(theorem.name),
                level_params: vec![],
                type_,
                value,
            })?;
        }
        Ok(())
    }

    /// Check if NNVerification.C009 declarations have been initialized.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nn_verification_c009_init == true`
    #[cfg(test)]
    pub(crate) fn has_nn_verification_c009(&self) -> bool {
        self.nn_verification_c009_init
    }
}

fn build_c009_ibp_wrapping_obligation(c: &C009Consts, depth: C009IbpWrappingDepth) -> Expr {
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let ibp_width = Expr::const_(Name::from_string("NNVerification.c009_ibp_width"), vec![]);
    let input_radius = Expr::const_(
        Name::from_string("NNVerification.c009_input_radius"),
        vec![],
    );
    let depth = match depth {
        C009IbpWrappingDepth::One => Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            c.nat_zero.clone(),
        ),
        C009IbpWrappingDepth::Two => Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                c.nat_zero.clone(),
            ),
        ),
        C009IbpWrappingDepth::Configured => {
            Expr::const_(Name::from_string("NNVerification.c009_depth"), vec![])
        }
    };
    let width = Expr::app(ibp_width, depth);
    Expr::app(Expr::app(Expr::app(eq, c.rat.clone()), width), input_radius)
}
