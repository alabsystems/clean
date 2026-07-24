// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trust/bootstrap initializers for the kernel environment.

use super::super::decl_builder::EnvDeclBuilder;
use super::super::*;

impl Environment {
    fn init_polymorphic_axiom(&mut self, name: &str) -> Result<(), EnvError> {
        let name = Name::from_string(name);
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(sort_u.clone());
            let r = b.mk_pi(a_id, BinderInfo::Implicit, sort_u, a_var);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name,
            level_params: vec![u],
            type_,
        })?;

        Ok(())
    }

    /// Initialize a polymorphic `sorry` axiom.
    ///
    /// This is used as a placeholder proof/term for tactic blocks (currently parsed as `sorry`)
    /// and for tactics that fall back to admitting goals.
    ///
    /// The axiom has type:
    /// ```text
    /// sorry.{u} : {α : Sort u} → α
    /// ```
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.get_const("sorry").is_some()`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    pub(crate) fn init_sorry(&mut self) -> Result<(), EnvError> {
        self.init_polymorphic_axiom("sorry")
    }

    /// Initialize a Lean 4-compatible `sorryAx`.
    ///
    /// The richer provenance-aware form is only valid once the Bool surface is
    /// already present in the environment.
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.get_const("sorryAx").is_some()`
    /// ENSURES: Returns `Ok(())` when `sorryAx` is already registered
    /// ENSURES: Uses actual Bool declarations as the readiness predicate
    pub(crate) fn init_sorry_ax(&mut self) -> Result<(), EnvError> {
        let sorry_ax = Name::from_string("sorryAx");
        if self.get_const(&sorry_ax).is_some() {
            return Ok(());
        }

        if let Some(missing) = self.bool_surface_missing_symbol() {
            return Err(EnvError::MissingRequiredDeclaration {
                init: "init_sorry_ax",
                decl: missing,
            });
        }

        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
        let type_ = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(sort_u.clone());
            let (synthetic_id, _synthetic) = b.fresh_local(bool_ty.clone());
            let r = b.mk_pi(synthetic_id, BinderInfo::Default, bool_ty, a_var);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, sort_u, r);
            b.finish(r)
        };

        self.add_decl(Declaration::Axiom {
            name: sorry_ax,
            level_params: vec![u],
            type_,
        })?;

        Ok(())
    }

    /// Initialize a polymorphic `trustedAy` axiom.
    ///
    /// This axiom is used when Ay SMT solver proves a goal. Unlike `sorry`,
    /// which indicates an incomplete proof, `trustedAy` indicates that an
    /// external solver verified the goal.
    ///
    /// The axiom has type:
    /// ```text
    /// trustedAy.{u} : {α : Sort u} → α
    /// ```
    ///
    /// # Soundness Note
    ///
    /// This axiom trusts Ay's correctness. A proof using `trustedAy` is sound
    /// if and only if Ay is sound for the translated goal. This is tracked
    /// separately from `sorry` to allow auditing which proofs rely on external
    /// solvers vs which are incomplete.
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.get_const("trustedAy").is_some()`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    pub fn init_trusted_ay(&mut self) -> Result<(), EnvError> {
        self.init_polymorphic_axiom("trustedAy")
    }

    /// Initialize a polymorphic `trustedArith` axiom.
    ///
    /// This axiom is used when arithmetic tactics (linarith, mathverse, nlinarith)
    /// verify a goal via decision procedures but cannot reconstruct a
    /// kernel-level proof term. Unlike `sorry`, which indicates an incomplete
    /// proof, `trustedArith` indicates that a verified arithmetic decision
    /// procedure confirmed the goal.
    ///
    /// The axiom has type:
    /// ```text
    /// trustedArith.{u} : {α : Sort u} → α
    /// ```
    ///
    /// # Soundness Note
    ///
    /// This axiom trusts the correctness of Fourier-Motzkin elimination and
    /// the Mathverse test. A proof using `trustedArith` is sound if and only if
    /// the decision procedure is sound for the translated goal. This is
    /// tracked separately from `sorry` to allow auditing which proofs rely
    /// on arithmetic decision procedures vs which are truly incomplete.
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.get_const("trustedArith").is_some()`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    pub fn init_trusted_arith(&mut self) -> Result<(), EnvError> {
        self.init_polymorphic_axiom("trustedArith")
    }
}
