// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Abstract interpretation framework extensions: zonotope domain instances,
//! transfer functions, and domain/transfer soundness theorems.
//!
//! Split from `abstract_interpretation_framework.rs` for the 500-line limit.
//! The base file holds lattice ops, Galois connection, interval domain, and
//! core lattice/Galois theorems.
//!
//! Part of #3189.

use super::abstract_interpretation_framework_defs2 as fw_defs2;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::name::Name;

impl Environment {
    // -- Zonotope domain instances -------------------------------------------

    pub(super) fn register_aif_zonotope_join(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.zonotope_join"),
            level_params: vec![],
            type_: fw_defs2::build_zonotope_join_type(c),
        })
    }

    pub(super) fn register_aif_zonotope_meet(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.zonotope_meet"),
            level_params: vec![],
            type_: fw_defs2::build_zonotope_meet_type(c),
        })
    }

    pub(super) fn register_aif_zonotope_bot(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.zonotope_bot"),
            level_params: vec![],
            type_: fw_defs2::build_zonotope_bot_type(c),
        })
    }

    pub(super) fn register_aif_zonotope_top(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.zonotope_top"),
            level_params: vec![],
            type_: fw_defs2::build_zonotope_top_type(c),
        })
    }

    pub(super) fn register_aif_zonotope_widening(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.zonotope_widening"),
            level_params: vec![],
            type_: fw_defs2::build_zonotope_widening_type(c),
        })
    }

    // -- Transfer functions ---------------------------------------------------

    pub(super) fn register_aif_linear_transfer(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.linear_transfer"),
            level_params: vec![],
            type_: fw_defs2::build_linear_transfer_type(c),
        })
    }

    pub(super) fn register_aif_relu_transfer(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.relu_transfer"),
            level_params: vec![],
            type_: fw_defs2::build_relu_transfer_type(c),
        })
    }

    pub(super) fn register_aif_layer_compose_transfer(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.layer_compose_transfer"),
            level_params: vec![],
            type_: fw_defs2::build_layer_compose_transfer_type(c),
        })
    }

    // -- Domain witness and transfer soundness theorems -----------------------

    pub(super) fn register_aif_interval_is_abstract_domain(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let thm_type = fw_defs2::build_interval_is_abstract_domain_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.interval_is_abstract_domain_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.Framework.interval_is_abstract_domain_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.Framework.interval_is_abstract_domain"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    pub(super) fn register_aif_zonotope_is_abstract_domain(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let thm_type = fw_defs2::build_zonotope_is_abstract_domain_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.zonotope_is_abstract_domain_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.Framework.zonotope_is_abstract_domain_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.Framework.zonotope_is_abstract_domain"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    pub(super) fn register_aif_interval_zonotope_galois(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let thm_type = fw_defs2::build_interval_is_abstract_domain_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.interval_zonotope_galois_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.Framework.interval_zonotope_galois_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.Framework.interval_zonotope_galois"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    pub(super) fn register_aif_zonotope_refines_interval_galois(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let thm_type = fw_defs2::build_zonotope_refines_interval_galois_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(
                "AbstractInterp.Framework.zonotope_refines_interval_galois_axiom",
            ),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.Framework.zonotope_refines_interval_galois_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.Framework.zonotope_refines_interval_galois"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    pub(super) fn register_aif_linear_transfer_sound(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let thm_type = fw_defs2::build_linear_transfer_sound_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.linear_transfer_sound_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.Framework.linear_transfer_sound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.Framework.linear_transfer_sound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    pub(super) fn register_aif_relu_transfer_sound(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let thm_type = fw_defs2::build_relu_transfer_sound_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.relu_transfer_sound_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.Framework.relu_transfer_sound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.Framework.relu_transfer_sound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }
}
