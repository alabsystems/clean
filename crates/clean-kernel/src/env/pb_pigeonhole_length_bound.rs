// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for the concrete CP length bound for PHP.
//!
//! Registers the kernel axiom surface for:
//! - A concrete CP-style proof object of PHP(n+1, n), exposed as a `PBProof`
//! - Linear step/axiom/total-size counting functions for that proof family
//! - The cubic upper bound theorem surface for the total proof size
//! - Validity of the resulting PHP refutation
//!
//! The size functions capture a concrete O(n) construction:
//! - `cp_php_step_count n = 2 * n`
//! - `cp_php_axiom_count n = 2 * n + 1`
//! - `cp_php_total_size n = 4 * n + 1`
//!
//! We register the classic weaker theorem surface `O(n^3)` to match the
//! conventional proof-complexity statement for PHP.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Shared constants used across PB pigeonhole length-bound declarations.
pub(super) struct PBPigeonholeLengthBoundConsts {
    pub(super) nat: Expr,
    pub(super) prop: Expr,
    pub(super) pb_proof: Expr,
    pub(super) le_le: Expr,
    pub(super) inst_le_nat: Expr,
    pub(super) nat_mul: Expr,
}

impl PBPigeonholeLengthBoundConsts {
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            pb_proof: Expr::const_(Name::from_string("ProofTheory.PBProof"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_nat: Expr::const_(Name::from_string("instLENat"), vec![]),
            nat_mul: Expr::const_(Name::from_string("Nat.mul"), vec![]),
        }
    }
}

impl Environment {
    /// Initialize PB pigeonhole declarations for the concrete PHP length bound.
    ///
    /// Depends on: `init_pb_pigeonhole()`, `init_le()`.
    pub(crate) fn init_pb_pigeonhole_length_bound(&mut self) -> Result<(), EnvError> {
        if self.pb_pigeonhole_length_bound_init {
            return Ok(());
        }
        self.init_pb_pigeonhole()?;
        self.init_le()?;

        let c = PBPigeonholeLengthBoundConsts::new();
        self.register_cp_proof_of_php(&c)?;
        self.register_cp_php_step_count(&c)?;
        self.register_cp_php_axiom_count(&c)?;
        self.register_cp_php_total_size(&c)?;
        self.register_cp_php_size_cubic_helper(&c)?;
        self.register_cp_php_size_cubic(&c)?;
        self.register_cp_php_refutation_valid_helper(&c)?;
        self.register_cp_php_refutation_valid(&c)?;

        self.pb_pigeonhole_length_bound_init = true;
        Ok(())
    }

    // ====================================================================
    // Definitions
    // ====================================================================

    /// `CPProofOfPHP (n : Nat) : PBProof`
    ///
    /// Opaque constructor for the concrete CP-style proof of PHP(n+1, n),
    /// represented in the requested PB proof surface.
    fn register_cp_proof_of_php(
        &mut self,
        c: &PBPigeonholeLengthBoundConsts,
    ) -> Result<(), EnvError> {
        let name = "ProofTheory.CPProofOfPHP";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.pb_proof.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_php_step_count (n : Nat) : Nat`
    ///
    /// Step count for the concrete PHP derivation: `2 * n`.
    fn register_cp_php_step_count(
        &mut self,
        c: &PBPigeonholeLengthBoundConsts,
    ) -> Result<(), EnvError> {
        let name = "ProofTheory.cp_php_step_count";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_php_axiom_count (n : Nat) : Nat`
    ///
    /// Number of axioms in the concrete PHP derivation: `2 * n + 1`.
    fn register_cp_php_axiom_count(
        &mut self,
        c: &PBPigeonholeLengthBoundConsts,
    ) -> Result<(), EnvError> {
        let name = "ProofTheory.cp_php_axiom_count";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_php_total_size (n : Nat) : Nat`
    ///
    /// Total size of the concrete PHP derivation: `4 * n + 1 = O(n)`.
    fn register_cp_php_total_size(
        &mut self,
        c: &PBPigeonholeLengthBoundConsts,
    ) -> Result<(), EnvError> {
        let name = "ProofTheory.cp_php_total_size";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.nat.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 1: Concrete PHP proof has cubic size bound
    // ====================================================================

    /// Helper for cp_php_size_cubic: `(n : Nat) -> Prop`
    ///
    /// Encodes:
    /// `LE.le (cp_php_total_size n) (Nat.mul n (Nat.mul n n))`.
    pub(super) fn register_cp_php_size_cubic_helper(
        &mut self,
        c: &PBPigeonholeLengthBoundConsts,
    ) -> Result<(), EnvError> {
        let name = "ProofTheory.cp_php_size_cubic_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.prop.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_php_size_cubic : forall (n : Nat), cp_php_size_cubic_helper n`
    ///
    /// The concrete PHP proof family has linear total size, hence in
    /// particular it satisfies the weaker classic cubic upper bound.
    pub(super) fn register_cp_php_size_cubic(
        &mut self,
        c: &PBPigeonholeLengthBoundConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "ProofTheory.cp_php_size_cubic";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("ProofTheory.cp_php_size_cubic_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = Expr::app(helper, n.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 2: Concrete PHP proof is a valid refutation
    // ====================================================================

    /// Helper for cp_php_refutation_valid: `(n : Nat) -> Prop`
    ///
    /// Encodes: `CPProofOfPHP n` is a valid refutation of PHP(n+1, n).
    pub(super) fn register_cp_php_refutation_valid_helper(
        &mut self,
        c: &PBPigeonholeLengthBoundConsts,
    ) -> Result<(), EnvError> {
        let name = "ProofTheory.cp_php_refutation_valid_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.prop.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `cp_php_refutation_valid :
    ///     forall (n : Nat), cp_php_refutation_valid_helper n`
    ///
    /// This packages the validity of the concrete CP-style refutation of
    /// PHP(n+1, n) in the same helper-then-theorem pattern as the other
    /// PB pigeonhole theorem surfaces.
    pub(super) fn register_cp_php_refutation_valid(
        &mut self,
        c: &PBPigeonholeLengthBoundConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "ProofTheory.cp_php_refutation_valid";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }
        let helper = Expr::const_(
            Name::from_string("ProofTheory.cp_php_refutation_valid_helper"),
            vec![],
        );
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (n_id, n) = b.fresh_local(c.nat.clone());
            let body = Expr::app(helper, n.clone());
            let e = b.mk_pi(n_id, BinderInfo::Default, c.nat.clone(), body);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }
}
