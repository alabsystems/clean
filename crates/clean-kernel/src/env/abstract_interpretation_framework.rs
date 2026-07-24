// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Abstract interpretation framework registration overlay.
//!
//! Registers the `AbstractInterp.Framework` declarations that extend the base
//! abstract interpretation surface with lattice operators, Galois interfaces,
//! concrete abstract-domain instances, transfer functions, and axiom-backed
//! soundness theorems.
//!
//! Part of #3189.

use super::abstract_interpretation_framework_defs as fw_defs;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::name::Name;

impl Environment {
    /// Initialize abstract interpretation framework declarations.
    ///
    /// Depends on:
    /// - `init_abstract_interpretation()` for the shared abstract-state
    ///   carrier and lattice-ordering infrastructure
    pub(crate) fn init_abstract_interpretation_framework(&mut self) -> Result<(), EnvError> {
        if self.abstract_interpretation_framework_init {
            return Ok(());
        }
        self.init_abstract_interpretation()?;

        let c = super::abstract_interpretation::AbstractInterpConsts::new();

        // Lattice operations
        self.register_aif_join(&c)?;
        self.register_aif_meet(&c)?;
        self.register_aif_bot(&c)?;
        self.register_aif_top(&c)?;

        // Galois connection interface
        self.register_aif_galois_connection(&c)?;
        self.register_aif_galois_adjunction(&c)?;

        // Domain instances
        self.register_aif_interval_join(&c)?;
        self.register_aif_interval_meet(&c)?;
        self.register_aif_interval_bot(&c)?;
        self.register_aif_interval_top(&c)?;
        self.register_aif_interval_widening(&c)?;
        self.register_aif_zonotope_join(&c)?;
        self.register_aif_zonotope_meet(&c)?;
        self.register_aif_zonotope_bot(&c)?;
        self.register_aif_zonotope_top(&c)?;
        self.register_aif_zonotope_widening(&c)?;

        // Transfer functions
        self.register_aif_linear_transfer(&c)?;
        self.register_aif_relu_transfer(&c)?;
        self.register_aif_layer_compose_transfer(&c)?;

        // Soundness theorems (axiom-backed)
        self.register_aif_join_upper_bound(&c)?;
        self.register_aif_meet_lower_bound(&c)?;
        self.register_aif_bot_least(&c)?;
        self.register_aif_top_greatest(&c)?;
        self.register_aif_galois_connection_sound(&c)?;
        self.register_aif_interval_is_abstract_domain(&c)?;
        self.register_aif_zonotope_is_abstract_domain(&c)?;
        self.register_aif_interval_zonotope_galois(&c)?;
        self.register_aif_zonotope_refines_interval_galois(&c)?;
        self.register_aif_linear_transfer_sound(&c)?;
        self.register_aif_relu_transfer_sound(&c)?;

        self.abstract_interpretation_framework_init = true;
        Ok(())
    }

    // -- Lattice operations -------------------------------------------------

    fn register_aif_join(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.join"),
            level_params: vec![],
            type_: fw_defs::build_join_type(c),
        })
    }

    fn register_aif_meet(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.meet"),
            level_params: vec![],
            type_: fw_defs::build_meet_type(c),
        })
    }

    fn register_aif_bot(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.bot"),
            level_params: vec![],
            type_: fw_defs::build_bot_type(c),
        })
    }

    fn register_aif_top(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.top"),
            level_params: vec![],
            type_: fw_defs::build_top_type(c),
        })
    }

    // -- Galois connection --------------------------------------------------

    fn register_aif_galois_connection(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.GaloisConnection"),
            level_params: vec![],
            type_: fw_defs::build_galois_connection_type(c),
        })
    }

    fn register_aif_galois_adjunction(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let thm_type = fw_defs::build_galois_adjunction_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.galois_adjunction_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.Framework.galois_adjunction_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.Framework.galois_adjunction"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    // -- Domain instances ---------------------------------------------------

    fn register_aif_interval_join(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.interval_join"),
            level_params: vec![],
            type_: fw_defs::build_interval_join_type(c),
        })
    }

    fn register_aif_interval_meet(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.interval_meet"),
            level_params: vec![],
            type_: fw_defs::build_interval_meet_type(c),
        })
    }

    fn register_aif_interval_bot(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.interval_bot"),
            level_params: vec![],
            type_: fw_defs::build_interval_bot_type(c),
        })
    }

    fn register_aif_interval_top(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.interval_top"),
            level_params: vec![],
            type_: fw_defs::build_interval_top_type(c),
        })
    }

    fn register_aif_interval_widening(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.interval_widening"),
            level_params: vec![],
            type_: fw_defs::build_interval_widening_type(c),
        })
    }

    // -- Theorems -----------------------------------------------------------

    fn register_aif_join_upper_bound(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let thm_type = fw_defs::build_join_upper_bound_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.join_upper_bound_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.Framework.join_upper_bound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.Framework.join_upper_bound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    fn register_aif_meet_lower_bound(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let thm_type = fw_defs::build_meet_lower_bound_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.meet_lower_bound_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.Framework.meet_lower_bound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.Framework.meet_lower_bound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    fn register_aif_bot_least(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let thm_type = fw_defs::build_bot_least_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.bot_least_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.Framework.bot_least_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.Framework.bot_least"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    fn register_aif_top_greatest(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let thm_type = fw_defs::build_top_greatest_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.top_greatest_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.Framework.top_greatest_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.Framework.top_greatest"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    fn register_aif_galois_connection_sound(
        &mut self,
        c: &super::abstract_interpretation::AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let thm_type = fw_defs::build_galois_connection_sound_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Framework.galois_connection_sound_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.Framework.galois_connection_sound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.Framework.galois_connection_sound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }
}
