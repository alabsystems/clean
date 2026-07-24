// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem registrations for abstract domain theory.
//!
//! Contains the axiom-backed theorem declarations:
//! 1. `galois_soundness` — Galois connections ensure over-approximation
//! 2. `transformer_soundness` — abstract transformers are sound
//! 3. `composition_soundness` — composed domains preserve soundness
//! 4. `precision_monotone` — more precise domains yield tighter bounds
//! 5. `ibp_is_interval_domain` — IBP = abstract interpretation with intervals
//! 6. `zonotope_refines_interval` — zonotope domain refines interval domain
//!
//! Part of #3261.

use super::nn_verify_abstract_domain::AbstractDomainConsts;
use super::nn_verify_abstract_domain_defs as defs;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::name::Name;

impl Environment {
    pub(super) fn register_ad_galois_soundness(
        &mut self,
        c: &AbstractDomainConsts,
    ) -> Result<(), EnvError> {
        let thm_type = defs::build_galois_soundness_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.galois_soundness_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.AbstractDomain.galois_soundness_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.AbstractDomain.galois_soundness"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    pub(super) fn register_ad_transformer_soundness(
        &mut self,
        c: &AbstractDomainConsts,
    ) -> Result<(), EnvError> {
        let thm_type = defs::build_transformer_soundness_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.transformer_soundness_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.AbstractDomain.transformer_soundness_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.AbstractDomain.transformer_soundness"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    pub(super) fn register_ad_composition_soundness(
        &mut self,
        c: &AbstractDomainConsts,
    ) -> Result<(), EnvError> {
        let thm_type = defs::build_composition_soundness_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.composition_soundness_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.AbstractDomain.composition_soundness_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.AbstractDomain.composition_soundness"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    pub(super) fn register_ad_precision_monotone(
        &mut self,
        c: &AbstractDomainConsts,
    ) -> Result<(), EnvError> {
        let thm_type = defs::build_precision_monotone_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.precision_monotone_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.AbstractDomain.precision_monotone_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.AbstractDomain.precision_monotone"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    pub(super) fn register_ad_ibp_is_interval_domain(
        &mut self,
        c: &AbstractDomainConsts,
    ) -> Result<(), EnvError> {
        let thm_type = defs::build_ibp_is_interval_domain_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.ibp_is_interval_domain_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.AbstractDomain.ibp_is_interval_domain_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.AbstractDomain.ibp_is_interval_domain"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    pub(super) fn register_ad_zonotope_refines_interval(
        &mut self,
        c: &AbstractDomainConsts,
    ) -> Result<(), EnvError> {
        let thm_type = defs::build_zonotope_refines_interval_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.zonotope_refines_interval_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.AbstractDomain.zonotope_refines_interval_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.AbstractDomain.zonotope_refines_interval"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }
}
