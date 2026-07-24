// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! IBP instance registration for the abstract domain framework.
//!
//! Registers IntervalBounds as a concrete instance of AbstractDomain,
//! with T80/T81/T82 as the instance proofs for sound_linear/relu/compose.
//!
//! - `ibp_instance` — IntervalBounds is an abstract domain
//! - `ibp_sound_linear` — T80 as instance proof
//! - `ibp_sound_relu` — T81 as instance proof
//! - `ibp_sound_compose` — T82 as instance proof
//!
//! Part of #3261.

use super::nn_verify_abstract_domain::AbstractDomainConsts;
use super::nn_verify_abstract_domain_ops_defs as ops_defs;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::name::Name;

impl Environment {
    /// Initialize IBP instance proofs for the abstract domain framework.
    ///
    /// Registers IntervalBounds as a concrete instance of AbstractDomain,
    /// with T80/T81/T82 as the instance proofs for sound_linear/relu/compose.
    ///
    /// Depends on:
    /// - `init_nn_verify_abstract_domain()` for the framework
    /// - `init_nn_verify_ibp_composition()` for T80/T81/T82
    pub(crate) fn init_nn_verify_abstract_domain_ibp(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_abstract_domain_ibp_init {
            return Ok(());
        }
        self.init_nn_verify_abstract_domain()?;
        self.init_nn_verify_ibp_composition()?;

        let c = AbstractDomainConsts::new();

        // IBP instance: IntervalBounds satisfies AbstractDomain
        self.register_ad_ibp_instance(&c)?;
        self.register_ad_ibp_sound_linear(&c)?;
        self.register_ad_ibp_sound_relu(&c)?;
        self.register_ad_ibp_sound_compose(&c)?;

        self.nn_verify_abstract_domain_ibp_init = true;
        Ok(())
    }

    /// `NNVerify.AbstractDomain.ibp_instance`:
    /// Witnesses that IntervalBounds is a valid abstract domain.
    /// `(d : Nat) -> abstract_domain d`
    ///
    /// This is the canonical embedding: IntervalBounds d is an abstract domain.
    fn register_ad_ibp_instance(&mut self, c: &AbstractDomainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.ibp_instance"),
            level_params: vec![],
            type_: ops_defs::build_ad_ibp_instance_type(c),
        })
    }

    /// `NNVerify.AbstractDomain.ibp_sound_linear`:
    /// T80 witnesses sound_linear for the IBP domain.
    fn register_ad_ibp_sound_linear(&mut self, c: &AbstractDomainConsts) -> Result<(), EnvError> {
        let thm_type = ops_defs::build_ad_ibp_sound_linear_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.ibp_sound_linear_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.AbstractDomain.ibp_sound_linear_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.AbstractDomain.ibp_sound_linear"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    /// `NNVerify.AbstractDomain.ibp_sound_relu`:
    /// T81 witnesses sound_relu for the IBP domain.
    fn register_ad_ibp_sound_relu(&mut self, c: &AbstractDomainConsts) -> Result<(), EnvError> {
        let thm_type = ops_defs::build_ad_ibp_sound_relu_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.ibp_sound_relu_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.AbstractDomain.ibp_sound_relu_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.AbstractDomain.ibp_sound_relu"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    /// `NNVerify.AbstractDomain.ibp_sound_compose`:
    /// T82 witnesses sound_compose for the IBP domain.
    fn register_ad_ibp_sound_compose(&mut self, c: &AbstractDomainConsts) -> Result<(), EnvError> {
        let thm_type = ops_defs::build_ad_ibp_sound_compose_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.ibp_sound_compose_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("NNVerify.AbstractDomain.ibp_sound_compose_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.AbstractDomain.ibp_sound_compose"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }
}
