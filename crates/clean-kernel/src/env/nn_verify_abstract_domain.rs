// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Abstract domain theory for neural network verification.
//!
//! Formalizes the lattice-theoretic foundations of abstract interpretation
//! as applied to NN verification. The key mathematical objects:
//!
//! ## Definitions (type-level specifications)
//!
//! - `abstract_domain` — abstract domain structure (Nat -> Type)
//! - `galois_connection` — Galois connection predicate
//! - `abstract_transformer` — sound abstract transformer
//! - `domain_precision` — precision metric
//! - `domain_composition` — product domain composition
//!
//! ## Generalized Domain Operations
//!
//! - `ad_contains` — membership predicate (generalizes IntervalBounds.contains)
//! - `sound_linear` — soundness through linear layers (generalizes T80)
//! - `sound_relu` — soundness through ReLU activation (generalizes T81)
//! - `sound_compose` — soundness of linear+ReLU composition (generalizes T82)
//! - `tighter_than` — partial order: D1 tighter than D2 iff D1 certifies
//!   a subset of what D2 certifies
//!
//! ## IBP Instance (in `nn_verify_abstract_domain_ibp`)
//!
//! - `ibp_instance` — IntervalBounds is an abstract domain
//! - `ibp_sound_linear` — T80 as instance proof
//! - `ibp_sound_relu` — T81 as instance proof
//! - `ibp_sound_compose` — T82 as instance proof
//!
//! ## Theorems (in `nn_verify_abstract_domain_thms`)
//!
//! 1. `galois_soundness` — Galois connection ensures over-approximation
//! 2. `transformer_soundness` — abstract transformer is sound
//! 3. `composition_soundness` — composed domains preserve soundness
//! 4. `precision_monotone` — more precise domains yield tighter bounds
//! 5. `ibp_is_interval_domain` — IBP is interval abstract interpretation
//! 6. `zonotope_refines_interval` — zonotope refines interval domain
//!
//! Type builders are in sibling modules:
//! - `nn_verify_abstract_domain_defs` — definition and theorem type builders
//! - `nn_verify_abstract_domain_ops_defs` — generalized ops and IBP type builders
//!
//! Part of #3261.

#[cfg(test)]
use super::nn_verify_abstract_domain_defs as defs;
#[cfg(test)]
use super::nn_verify_abstract_domain_ops_defs as ops_defs;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{Expr, ExprKind};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Shared constants for abstract domain formalization.
#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(super) struct AbstractDomainConsts {
    pub(super) nat: Expr,
    pub(super) rat: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    pub(super) nn_vec: Expr,
    pub(super) ib: Expr,
    pub(super) ib_contains: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_rat: Expr,
    // Abstract domain primitives (self-referencing constants)
    pub(super) abstract_domain: Expr,
    pub(super) galois_connection: Expr,
    pub(super) abstract_transformer: Expr,
    pub(super) domain_precision: Expr,
    pub(super) domain_composition: Expr,
    // IBP/zonotope references
    pub(super) ibp_linear_bounds: Expr,
    pub(super) ibp_relu_bounds: Expr,
    // Generalized domain operations
    pub(super) ad_contains: Expr,
    pub(super) ad_sound_linear: Expr,
    pub(super) ad_sound_relu: Expr,
    pub(super) ad_sound_compose: Expr,
    pub(super) ad_tighter_than: Expr,
    // IBP instance declarations
    pub(super) ad_ibp_instance: Expr,
    pub(super) ad_ibp_sound_linear: Expr,
    pub(super) ad_ibp_sound_relu: Expr,
    pub(super) ad_ibp_sound_compose: Expr,
    // References to T80/T81/T82
    pub(super) ibp_linear_sound: Expr,
    pub(super) ibp_relu_soundness: Expr,
    pub(super) ibp_composition: Expr,
    pub(super) relu_vec: Expr,
    pub(super) linear_output: Expr,
    pub(super) nn_mat: Expr,
    pub(super) fin: Expr,
}

#[cfg(test)]
impl AbstractDomainConsts {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            nn_vec: Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_contains: Expr::const_(
                Name::from_string("NNVerify.IntervalBounds.contains"),
                vec![],
            ),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            abstract_domain: Expr::const_(
                Name::from_string("NNVerify.AbstractDomain.abstract_domain"),
                vec![],
            ),
            galois_connection: Expr::const_(
                Name::from_string("NNVerify.AbstractDomain.galois_connection"),
                vec![],
            ),
            abstract_transformer: Expr::const_(
                Name::from_string("NNVerify.AbstractDomain.abstract_transformer"),
                vec![],
            ),
            domain_precision: Expr::const_(
                Name::from_string("NNVerify.AbstractDomain.domain_precision"),
                vec![],
            ),
            domain_composition: Expr::const_(
                Name::from_string("NNVerify.AbstractDomain.domain_composition"),
                vec![],
            ),
            ibp_linear_bounds: Expr::const_(
                Name::from_string("NNVerify.ibp_linear_bounds"),
                vec![],
            ),
            ibp_relu_bounds: Expr::const_(Name::from_string("NNVerify.ibp_relu_bounds"), vec![]),
            ad_contains: Expr::const_(
                Name::from_string("NNVerify.AbstractDomain.ad_contains"),
                vec![],
            ),
            ad_sound_linear: Expr::const_(
                Name::from_string("NNVerify.AbstractDomain.sound_linear"),
                vec![],
            ),
            ad_sound_relu: Expr::const_(
                Name::from_string("NNVerify.AbstractDomain.sound_relu"),
                vec![],
            ),
            ad_sound_compose: Expr::const_(
                Name::from_string("NNVerify.AbstractDomain.sound_compose"),
                vec![],
            ),
            ad_tighter_than: Expr::const_(
                Name::from_string("NNVerify.AbstractDomain.tighter_than"),
                vec![],
            ),
            ad_ibp_instance: Expr::const_(
                Name::from_string("NNVerify.AbstractDomain.ibp_instance"),
                vec![],
            ),
            ad_ibp_sound_linear: Expr::const_(
                Name::from_string("NNVerify.AbstractDomain.ibp_sound_linear"),
                vec![],
            ),
            ad_ibp_sound_relu: Expr::const_(
                Name::from_string("NNVerify.AbstractDomain.ibp_sound_relu"),
                vec![],
            ),
            ad_ibp_sound_compose: Expr::const_(
                Name::from_string("NNVerify.AbstractDomain.ibp_sound_compose"),
                vec![],
            ),
            ibp_linear_sound: Expr::const_(Name::from_string("NNVerify.ibp_linear_sound"), vec![]),
            ibp_relu_soundness: Expr::const_(
                Name::from_string("NNVerify.ibp_relu_soundness"),
                vec![],
            ),
            ibp_composition: Expr::const_(Name::from_string("NNVerify.ibp_composition"), vec![]),
            relu_vec: Expr::const_(Name::from_string("NNVerify.relu_vec"), vec![]),
            linear_output: Expr::const_(Name::from_string("NNVerify.linear_output"), vec![]),
            nn_mat: Expr::const_(Name::from_string("NNVerify.NNMat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
        }
    }

    /// Build `NNVerify.NNVec n`.
    #[cfg(test)]
    pub(super) fn vec_of(&self, n: Expr) -> Expr {
        Expr::app(self.nn_vec.clone(), n)
    }

    /// Build `NNVerify.IntervalBounds d`.
    #[cfg(test)]
    pub(super) fn ib_of(&self, d: Expr) -> Expr {
        Expr::app(self.ib.clone(), d)
    }

    /// Build `NNVerify.IntervalBounds.contains d b x`.
    #[cfg(test)]
    pub(super) fn contains(&self, d: &Expr, b: &Expr, x: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_contains.clone(), d.clone()), b.clone()),
            x.clone(),
        )
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
    #[cfg(test)]
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

    /// Build `NNVerify.NNMat m n`.
    #[cfg(test)]
    pub(super) fn mat_of(&self, m: Expr, n: Expr) -> Expr {
        Expr::app(Expr::app(self.nn_mat.clone(), m), n)
    }

    /// Build `abstract_domain d`.
    #[cfg(test)]
    pub(super) fn abs_dom_of(&self, d: Expr) -> Expr {
        Expr::app(self.abstract_domain.clone(), d)
    }

    /// Build `Fin d`.
    #[cfg(test)]
    pub(super) fn fin_of(&self, d: Expr) -> Expr {
        Expr::app(self.fin.clone(), d)
    }
}

// =============================================================================
// Environment impl
// =============================================================================

#[cfg(test)]
impl Environment {
    /// Initialize abstract domain theory declarations.
    ///
    /// Registers the generalized abstract domain framework:
    /// - Type-level specifications (abstract_domain, galois_connection, etc.)
    /// - Generalized operations (ad_contains, sound_linear, sound_relu, etc.)
    /// - Tightness ordering
    /// - Theorems (galois_soundness, transformer_soundness, etc.)
    ///
    /// Does NOT register IBP instance proofs (those need T80/T81/T82).
    /// Use `init_nn_verify_abstract_domain_ibp()` for that.
    ///
    /// Depends on:
    /// - `init_nn_verify_types()` for NNVec, IntervalBounds
    /// - `init_rat()` / `init_rat_ord()` for Rat arithmetic and ordering
    /// - `init_eq()` for equality
    #[cfg(test)]
    pub(crate) fn init_nn_verify_abstract_domain(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_abstract_domain_init {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_rat_ord()?;
        self.init_eq()?;

        let c = AbstractDomainConsts::new();

        // Definitions (registered as axioms — abstract type-level specifications)
        self.register_ad_abstract_domain(&c)?;
        self.register_ad_galois_connection(&c)?;
        self.register_ad_abstract_transformer(&c)?;
        self.register_ad_domain_precision(&c)?;
        self.register_ad_domain_composition(&c)?;

        // Generalized domain operations (parameterized by abstract domain)
        self.register_ad_contains(&c)?;
        self.register_ad_sound_linear(&c)?;
        self.register_ad_sound_relu(&c)?;
        self.register_ad_sound_compose(&c)?;
        self.register_ad_tighter_than(&c)?;

        // Theorems (axiom-backed, in nn_verify_abstract_domain_thms)
        self.register_ad_galois_soundness(&c)?;
        self.register_ad_transformer_soundness(&c)?;
        self.register_ad_composition_soundness(&c)?;
        self.register_ad_precision_monotone(&c)?;
        self.register_ad_ibp_is_interval_domain(&c)?;
        self.register_ad_zonotope_refines_interval(&c)?;

        self.nn_verify_abstract_domain_init = true;
        Ok(())
    }

    // -- Definitions ----------------------------------------------------------

    #[cfg(test)]
    fn register_ad_abstract_domain(&mut self, c: &AbstractDomainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.abstract_domain"),
            level_params: vec![],
            type_: defs::build_abstract_domain_type(c),
        })
    }

    #[cfg(test)]
    fn register_ad_galois_connection(&mut self, c: &AbstractDomainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.galois_connection"),
            level_params: vec![],
            type_: defs::build_galois_connection_type(c),
        })
    }

    #[cfg(test)]
    fn register_ad_abstract_transformer(
        &mut self,
        c: &AbstractDomainConsts,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.abstract_transformer"),
            level_params: vec![],
            type_: defs::build_abstract_transformer_type(c),
        })
    }

    #[cfg(test)]
    fn register_ad_domain_precision(&mut self, c: &AbstractDomainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.domain_precision"),
            level_params: vec![],
            type_: defs::build_domain_precision_type(c),
        })
    }

    #[cfg(test)]
    fn register_ad_domain_composition(&mut self, c: &AbstractDomainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.domain_composition"),
            level_params: vec![],
            type_: defs::build_domain_composition_type(c),
        })
    }

    // -- Generalized domain operations ----------------------------------------

    /// `NNVerify.AbstractDomain.ad_contains`:
    /// `(d : Nat) -> abstract_domain d -> (Fin d -> Rat) -> Prop`
    ///
    /// Generalized membership predicate for any abstract domain element.
    /// For IBP, this reduces to `IntervalBounds.contains`.
    #[cfg(test)]
    fn register_ad_contains(&mut self, c: &AbstractDomainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.ad_contains"),
            level_params: vec![],
            type_: ops_defs::build_ad_contains_type(c),
        })
    }

    /// `NNVerify.AbstractDomain.sound_linear`:
    /// Soundness of an abstract domain through linear layers.
    /// Generalizes T80 (IBP linear soundness).
    #[cfg(test)]
    fn register_ad_sound_linear(&mut self, c: &AbstractDomainConsts) -> Result<(), EnvError> {
        let thm_type = ops_defs::build_ad_sound_linear_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.sound_linear"),
            level_params: vec![],
            type_: thm_type,
        })
    }

    /// `NNVerify.AbstractDomain.sound_relu`:
    /// Soundness of an abstract domain through ReLU.
    /// Generalizes T81 (IBP ReLU soundness).
    #[cfg(test)]
    fn register_ad_sound_relu(&mut self, c: &AbstractDomainConsts) -> Result<(), EnvError> {
        let thm_type = ops_defs::build_ad_sound_relu_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.sound_relu"),
            level_params: vec![],
            type_: thm_type,
        })
    }

    /// `NNVerify.AbstractDomain.sound_compose`:
    /// Soundness of an abstract domain through layer composition.
    /// Generalizes T82 (IBP composition).
    #[cfg(test)]
    fn register_ad_sound_compose(&mut self, c: &AbstractDomainConsts) -> Result<(), EnvError> {
        let thm_type = ops_defs::build_ad_sound_compose_type(c);
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.sound_compose"),
            level_params: vec![],
            type_: thm_type,
        })
    }

    /// `NNVerify.AbstractDomain.tighter_than`:
    /// D1 tighter_than D2 iff for all d, a, x:
    ///   ad_contains D1 d a x -> ad_contains D2 d a x
    ///
    /// D1 is at least as tight as D2 — anything D1 certifies, D2 also certifies.
    #[cfg(test)]
    fn register_ad_tighter_than(&mut self, c: &AbstractDomainConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("NNVerify.AbstractDomain.tighter_than"),
            level_params: vec![],
            type_: ops_defs::build_ad_tighter_than_type(c),
        })
    }
}
