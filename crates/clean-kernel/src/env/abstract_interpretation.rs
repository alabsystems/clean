// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Abstract interpretation framework (Cousot & Cousot, 1977).
//!
//! Formalizes the classical abstract interpretation framework as kernel-level
//! declarations. This is the general-purpose framework — not specific to NN
//! verification (see `nn_verify_abstract_domain` for that specialization).
//!
//! ## Definitions
//!
//! 1. `AbstractInterp.ConcreteSemantics` — concrete collecting semantics of a
//!    program: maps program states to sets of reachable states
//! 2. `AbstractInterp.AbstractSemantics` — abstract semantics over an abstract
//!    domain: maps abstract states to abstract states
//! 3. `AbstractInterp.Widening` — widening operator for accelerating fixpoint
//!    computation (ensures termination on infinite-height lattices)
//! 4. `AbstractInterp.Narrowing` — narrowing operator for refining after
//!    widening (recovers precision without losing soundness)
//! 5. `AbstractInterp.fixpoint_iteration` — Kleene iteration with
//!    widening/narrowing
//!
//! ## Theorems (axiom-backed)
//!
//! 1. `AbstractInterp.soundness` — abstract semantics over-approximates
//!    concrete semantics
//! 2. `AbstractInterp.widening_termination` — iteration with widening
//!    terminates in finite steps
//! 3. `AbstractInterp.narrowing_refines` — narrowing refines without losing
//!    soundness
//! 4. `AbstractInterp.fixpoint_sound` — computed fixpoint over-approximates
//!    least fixpoint of concrete semantics
//! 5. `AbstractInterp.domain_product_sound` — reduced product of sound domains
//!    is sound
//!
//! Part of #3189.

#[cfg(test)]
use super::abstract_interpretation_defs as defs;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::Expr;
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Shared constants for abstract interpretation formalization.
///
/// Unlike NN-specific `AbstractDomainConsts`, these are program-analysis
/// primitives parameterized by a lattice structure.
#[cfg(test)]
pub(super) struct AbstractInterpConsts {
    pub(super) nat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    // Self-referencing abstract interpretation primitives
    pub(super) concrete_semantics: Expr,
    pub(super) abstract_semantics: Expr,
    pub(super) widening: Expr,
    pub(super) narrowing: Expr,
    pub(super) fixpoint_iteration: Expr,
    // Lattice ordering: LE.le @(AbstractState) inst
    pub(super) abstract_state: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_abstract_state: Expr,
}

#[cfg(test)]
impl AbstractInterpConsts {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::sort(Level::zero()),
            type0: Expr::sort(Level::succ(Level::zero())),
            concrete_semantics: Expr::const_(
                Name::from_string("AbstractInterp.ConcreteSemantics"),
                vec![],
            ),
            abstract_semantics: Expr::const_(
                Name::from_string("AbstractInterp.AbstractSemantics"),
                vec![],
            ),
            widening: Expr::const_(Name::from_string("AbstractInterp.Widening"), vec![]),
            narrowing: Expr::const_(Name::from_string("AbstractInterp.Narrowing"), vec![]),
            fixpoint_iteration: Expr::const_(
                Name::from_string("AbstractInterp.fixpoint_iteration"),
                vec![],
            ),
            abstract_state: Expr::const_(Name::from_string("AbstractInterp.AbstractState"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_abstract_state: Expr::const_(
                Name::from_string("AbstractInterp.instLEAbstractState"),
                vec![],
            ),
        }
    }

    /// Build `LE.le @AbstractState instLEAbstractState lhs rhs`.
    #[cfg(test)]
    pub(super) fn state_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.abstract_state.clone()),
                    self.inst_le_abstract_state.clone(),
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

#[cfg(test)]
impl Environment {
    /// Initialize abstract interpretation framework declarations.
    ///
    /// Depends on:
    /// - `init_eq()` for equality
    /// - `init_le()` for LE ordering class
    #[cfg(test)]
    pub(crate) fn init_abstract_interpretation(&mut self) -> Result<(), EnvError> {
        if self.abstract_interpretation_init {
            return Ok(());
        }
        self.init_eq()?;
        self.init_le()?;

        let c = AbstractInterpConsts::new();

        // Register the abstract state type first (other definitions reference it)
        self.register_ai_abstract_state(&c)?;
        self.register_ai_inst_le_abstract_state(&c)?;

        // Definitions (registered as axioms — abstract type-level specifications)
        self.register_ai_concrete_semantics(&c)?;
        self.register_ai_abstract_semantics(&c)?;
        self.register_ai_widening(&c)?;
        self.register_ai_narrowing(&c)?;
        self.register_ai_fixpoint_iteration(&c)?;

        // Theorems (axiom-backed)
        self.register_ai_soundness(&c)?;
        self.register_ai_widening_termination(&c)?;
        self.register_ai_narrowing_refines(&c)?;
        self.register_ai_fixpoint_sound(&c)?;
        self.register_ai_domain_product_sound(&c)?;

        self.abstract_interpretation_init = true;
        Ok(())
    }

    // -- Infrastructure types ------------------------------------------------

    /// `AbstractInterp.AbstractState : Type`
    ///
    /// The type of abstract lattice elements. Programs map between these.
    #[cfg(test)]
    fn register_ai_abstract_state(&mut self, c: &AbstractInterpConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.AbstractState"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    /// `AbstractInterp.instLEAbstractState : LE AbstractState`
    ///
    /// Ordering instance for the abstract lattice. Provides the partial order.
    #[cfg(test)]
    fn register_ai_inst_le_abstract_state(
        &mut self,
        c: &AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let le_class = Expr::const_(Name::from_string("LE"), vec![Level::zero()]);
        let le_abstract_state = Expr::app(le_class, c.abstract_state.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.instLEAbstractState"),
            level_params: vec![],
            type_: le_abstract_state,
        })
    }

    // -- Definitions ---------------------------------------------------------

    #[cfg(test)]
    fn register_ai_concrete_semantics(&mut self, c: &AbstractInterpConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.ConcreteSemantics"),
            level_params: vec![],
            type_: defs::build_concrete_semantics_type(c),
        })
    }

    #[cfg(test)]
    fn register_ai_abstract_semantics(&mut self, c: &AbstractInterpConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.AbstractSemantics"),
            level_params: vec![],
            type_: defs::build_abstract_semantics_type(c),
        })
    }

    #[cfg(test)]
    fn register_ai_widening(&mut self, c: &AbstractInterpConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Widening"),
            level_params: vec![],
            type_: defs::build_widening_type(c),
        })
    }

    #[cfg(test)]
    fn register_ai_narrowing(&mut self, c: &AbstractInterpConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.Narrowing"),
            level_params: vec![],
            type_: defs::build_narrowing_type(c),
        })
    }

    #[cfg(test)]
    fn register_ai_fixpoint_iteration(&mut self, c: &AbstractInterpConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.fixpoint_iteration"),
            level_params: vec![],
            type_: defs::build_fixpoint_iteration_type(c),
        })
    }

    // -- Theorems ------------------------------------------------------------

    #[cfg(test)]
    fn register_ai_soundness(&mut self, c: &AbstractInterpConsts) -> Result<(), EnvError> {
        let thm_type = defs::build_soundness_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.soundness_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(Name::from_string("AbstractInterp.soundness_axiom"), vec![]);
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.soundness"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(test)]
    fn register_ai_widening_termination(
        &mut self,
        c: &AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let thm_type = defs::build_widening_termination_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.widening_termination_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.widening_termination_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.widening_termination"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(test)]
    fn register_ai_narrowing_refines(&mut self, c: &AbstractInterpConsts) -> Result<(), EnvError> {
        let thm_type = defs::build_narrowing_refines_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.narrowing_refines_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.narrowing_refines_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.narrowing_refines"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(test)]
    fn register_ai_fixpoint_sound(&mut self, c: &AbstractInterpConsts) -> Result<(), EnvError> {
        let thm_type = defs::build_fixpoint_sound_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.fixpoint_sound_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.fixpoint_sound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.fixpoint_sound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }

    #[cfg(test)]
    fn register_ai_domain_product_sound(
        &mut self,
        c: &AbstractInterpConsts,
    ) -> Result<(), EnvError> {
        let thm_type = defs::build_domain_product_sound_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("AbstractInterp.domain_product_sound_axiom"),
            level_params: vec![],
            type_: thm_type.clone(),
        })?;
        let proof = Expr::const_(
            Name::from_string("AbstractInterp.domain_product_sound_axiom"),
            vec![],
        );
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("AbstractInterp.domain_product_sound"),
            level_params: vec![],
            type_: thm_type,
            value: proof,
        })
    }
}
