// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for proof complexity lower bounds of NN
//! verification certificates.
//!
//! Original mathematics establishing that:
//! 1. Any NN verification certificate has size >= f(depth, width)
//! 2. IBP certificates are polynomial in network size
//! 3. Tighter bounds require larger certificates (precision-cost trade-off)
//! 4. Certificate size is monotone in the depth*width product
//! 5. Certificate hierarchy: IBP < zonotope < DeepPoly
//!
//! These results connect proof complexity theory to neural network verification,
//! formalizing the computational cost of different abstract interpretation domains.
//!
//! Type and operation definitions live here; theorem type builders are in
//! `nn_verify_proof_complexity_defs.rs`.
//!
//! Part of #3260.

use super::nn_verify_proof_complexity_defs;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for proof complexity formalization.
pub(super) struct ProofComplexityConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    #[cfg(test)]
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    pub(super) and: Expr,
    pub(super) le_le: Expr,
    pub(super) lt_lt: Expr,
    pub(super) inst_le_nat: Expr,
    #[cfg(test)]
    pub(super) inst_lt_nat: Expr,
    pub(super) inst_le_rat: Expr,
    pub(super) inst_lt_rat: Expr,
    pub(super) nat_mul: Expr,
    pub(super) rat_zero: Expr,
    #[cfg(test)]
    pub(super) rat_div: Expr,
    /// NNVerify.ProofComplexity.CertificateSize : Nat -> Nat
    pub(super) certificate_size: Expr,
    /// NNVerify.ProofComplexity.NetworkComplexity : Nat -> Nat -> Nat
    pub(super) network_complexity: Expr,
    /// NNVerify.ProofComplexity.BoundTightness : Rat -> Rat -> Rat
    pub(super) bound_tightness: Expr,
    /// NNVerify.ProofComplexity.IBPCertificate : Type
    pub(super) ibp_cert: Expr,
    /// NNVerify.ProofComplexity.ZonotopeCertificate : Type
    pub(super) zonotope_cert: Expr,
    /// NNVerify.ProofComplexity.DeepPolyCertificate : Type
    pub(super) deep_poly_cert: Expr,
    /// NNVerify.ProofComplexity.ibp_cert_size : IBPCertificate -> Nat
    pub(super) ibp_cert_size: Expr,
    /// NNVerify.ProofComplexity.zonotope_cert_size : ZonotopeCertificate -> Nat
    pub(super) zonotope_cert_size: Expr,
    /// NNVerify.ProofComplexity.deep_poly_cert_size : DeepPolyCertificate -> Nat
    pub(super) deep_poly_cert_size: Expr,
}

impl ProofComplexityConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            #[cfg(test)]
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            and: Expr::const_(Name::from_string("And"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            lt_lt: Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
            inst_le_nat: Expr::const_(Name::from_string("instLENat"), vec![]),
            #[cfg(test)]
            inst_lt_nat: Expr::const_(Name::from_string("instLTNat"), vec![]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            inst_lt_rat: Expr::const_(Name::from_string("instLTRat"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
            rat_zero: Expr::const_(Name::from_string("Rat.zero"), vec![]),
            #[cfg(test)]
            rat_div: Expr::const_(Name::from_string("Rat.div"), vec![]),
            certificate_size: Expr::const_(
                Name::from_string("NNVerify.ProofComplexity.CertificateSize"),
                vec![],
            ),
            network_complexity: Expr::const_(
                Name::from_string("NNVerify.ProofComplexity.NetworkComplexity"),
                vec![],
            ),
            bound_tightness: Expr::const_(
                Name::from_string("NNVerify.ProofComplexity.BoundTightness"),
                vec![],
            ),
            ibp_cert: Expr::const_(
                Name::from_string("NNVerify.ProofComplexity.IBPCertificate"),
                vec![],
            ),
            zonotope_cert: Expr::const_(
                Name::from_string("NNVerify.ProofComplexity.ZonotopeCertificate"),
                vec![],
            ),
            deep_poly_cert: Expr::const_(
                Name::from_string("NNVerify.ProofComplexity.DeepPolyCertificate"),
                vec![],
            ),
            ibp_cert_size: Expr::const_(
                Name::from_string("NNVerify.ProofComplexity.ibp_cert_size"),
                vec![],
            ),
            zonotope_cert_size: Expr::const_(
                Name::from_string("NNVerify.ProofComplexity.zonotope_cert_size"),
                vec![],
            ),
            deep_poly_cert_size: Expr::const_(
                Name::from_string("NNVerify.ProofComplexity.deep_poly_cert_size"),
                vec![],
            ),
        }
    }

    /// Build `LE.le @Nat instLENat lhs rhs`.
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

    /// Build `LE.le @Rat instLERat lhs rhs`.
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

impl Environment {
    /// Initialize proof complexity lower bounds for NN verification certificates.
    ///
    /// Depends on:
    /// - `init_nat()` for Nat
    /// - `init_rat()` / `init_rat_ord()` for Rat arithmetic and ordering
    /// - `init_and()` for conjunction
    /// - `init_le()` / `init_lt()` for ordering typeclasses
    #[cfg(any(test, feature = "math-overlays"))]
    pub fn init_nn_verify_proof_complexity(&mut self) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string(
                "NNVerify.ProofComplexity.CertificateSize",
            ))
            .is_some()
        {
            return Ok(());
        }
        self.init_nat()?;
        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        self.init_and()?;

        let c = ProofComplexityConsts::new();

        // Definitions
        self.register_pc_certificate_size(&c)?;
        self.register_pc_network_complexity(&c)?;
        self.register_pc_bound_tightness(&c)?;
        self.register_pc_verification_problem(&c)?;
        self.register_pc_ibp_certificate(&c)?;
        self.register_pc_zonotope_certificate(&c)?;
        self.register_pc_deep_poly_certificate(&c)?;
        self.register_pc_ibp_cert_size(&c)?;
        self.register_pc_zonotope_cert_size(&c)?;
        self.register_pc_deep_poly_cert_size(&c)?;

        // Theorems
        self.register_pc_cert_size_lower_bound(&c)?;
        self.register_pc_ibp_cert_polynomial(&c)?;
        self.register_pc_tighter_bound_larger_cert(&c)?;
        self.register_pc_depth_width_tradeoff(&c)?;
        self.register_pc_cert_hierarchy(&c)?;

        Ok(())
    }

    // -- Definitions ----------------------------------------------------------

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_certificate_size(&mut self, c: &ProofComplexityConsts) -> Result<(), EnvError> {
        use nn_verify_proof_complexity_defs as defs;
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.CertificateSize"),
            level_params: vec![],
            type_: defs::build_certificate_size_type(c),
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_network_complexity(
        &mut self,
        c: &ProofComplexityConsts,
    ) -> Result<(), EnvError> {
        use nn_verify_proof_complexity_defs as defs;
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.NetworkComplexity"),
            level_params: vec![],
            type_: defs::build_network_complexity_type(c),
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_bound_tightness(&mut self, c: &ProofComplexityConsts) -> Result<(), EnvError> {
        use nn_verify_proof_complexity_defs as defs;
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.BoundTightness"),
            level_params: vec![],
            type_: defs::build_bound_tightness_type(c),
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_verification_problem(
        &mut self,
        c: &ProofComplexityConsts,
    ) -> Result<(), EnvError> {
        use nn_verify_proof_complexity_defs as defs;
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.VerificationProblem"),
            level_params: vec![],
            type_: defs::build_verification_problem_type(c),
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_ibp_certificate(&mut self, c: &ProofComplexityConsts) -> Result<(), EnvError> {
        use nn_verify_proof_complexity_defs as defs;
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.IBPCertificate"),
            level_params: vec![],
            type_: defs::build_ibp_certificate_type(c),
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_zonotope_certificate(
        &mut self,
        c: &ProofComplexityConsts,
    ) -> Result<(), EnvError> {
        use nn_verify_proof_complexity_defs as defs;
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.ZonotopeCertificate"),
            level_params: vec![],
            type_: defs::build_zonotope_certificate_type(c),
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_deep_poly_certificate(
        &mut self,
        c: &ProofComplexityConsts,
    ) -> Result<(), EnvError> {
        use nn_verify_proof_complexity_defs as defs;
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.DeepPolyCertificate"),
            level_params: vec![],
            type_: defs::build_deep_poly_certificate_type(c),
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_ibp_cert_size(&mut self, c: &ProofComplexityConsts) -> Result<(), EnvError> {
        use nn_verify_proof_complexity_defs as defs;
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.ibp_cert_size"),
            level_params: vec![],
            type_: defs::build_ibp_cert_size_type(c),
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_zonotope_cert_size(
        &mut self,
        c: &ProofComplexityConsts,
    ) -> Result<(), EnvError> {
        use nn_verify_proof_complexity_defs as defs;
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.zonotope_cert_size"),
            level_params: vec![],
            type_: defs::build_zonotope_cert_size_type(c),
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_deep_poly_cert_size(
        &mut self,
        c: &ProofComplexityConsts,
    ) -> Result<(), EnvError> {
        use nn_verify_proof_complexity_defs as defs;
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.deep_poly_cert_size"),
            level_params: vec![],
            type_: defs::build_deep_poly_cert_size_type(c),
        })
    }

    // -- Theorems -------------------------------------------------------------

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_cert_size_lower_bound(
        &mut self,
        c: &ProofComplexityConsts,
    ) -> Result<(), EnvError> {
        let thm_type = nn_verify_proof_complexity_defs::build_cert_size_lower_bound_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.cert_size_lower_bound_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.ProofComplexity.cert_size_lower_bound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.ProofComplexity.cert_size_lower_bound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_ibp_cert_polynomial(
        &mut self,
        c: &ProofComplexityConsts,
    ) -> Result<(), EnvError> {
        let thm_type = nn_verify_proof_complexity_defs::build_ibp_cert_polynomial_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.ibp_cert_polynomial_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.ProofComplexity.ibp_cert_polynomial_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.ProofComplexity.ibp_cert_polynomial"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_tighter_bound_larger_cert(
        &mut self,
        c: &ProofComplexityConsts,
    ) -> Result<(), EnvError> {
        let thm_type = nn_verify_proof_complexity_defs::build_tighter_bound_larger_cert_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.tighter_bound_larger_cert_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.ProofComplexity.tighter_bound_larger_cert_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.ProofComplexity.tighter_bound_larger_cert"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_depth_width_tradeoff(
        &mut self,
        c: &ProofComplexityConsts,
    ) -> Result<(), EnvError> {
        let thm_type = nn_verify_proof_complexity_defs::build_depth_width_tradeoff_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.depth_width_tradeoff_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.ProofComplexity.depth_width_tradeoff_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.ProofComplexity.depth_width_tradeoff"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(any(test, feature = "math-overlays"))]
    fn register_pc_cert_hierarchy(&mut self, c: &ProofComplexityConsts) -> Result<(), EnvError> {
        let thm_type = nn_verify_proof_complexity_defs::build_cert_hierarchy_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.ProofComplexity.cert_hierarchy_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.ProofComplexity.cert_hierarchy_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.ProofComplexity.cert_hierarchy"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }
}
