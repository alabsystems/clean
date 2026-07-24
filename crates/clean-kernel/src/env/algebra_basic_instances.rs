// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat typeclass instances for basic algebraic operations
//!
//! This module contains instance definitions for:
//! - Nat: Zero, One, Add, Mul, Sub instances
//!
//! Int instances are in algebra_basic_instances_int.rs.
//! Split from algebra_basic.rs for #307.

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    // ========================================================================
    // Typeclass Instances for Nat
    // ========================================================================

    /// Initialize Zero instance for Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_zero_inst_init == true`
    /// ENSURES: On success, required dependencies (`zero`, `nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_zero_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_zero_inst_init {
            return Ok(());
        }

        self.init_zero()?;
        self.init_nat()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let zero_mk = Expr::const_(Name::from_string("Zero.mk"), vec![Level::zero()]);

        // instZeroNat : Zero Nat := Zero.mk Nat.zero
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Zero"), vec![Level::zero()]),
            nat_const.clone(),
        );

        let inst_value = Expr::app(Expr::app(zero_mk, nat_const), nat_zero);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instZeroNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.nat_zero_inst_init = true;
        Ok(())
    }

    /// Check if Nat Zero instance has been initialized
    pub(crate) fn has_nat_zero_inst(&self) -> bool {
        self.nat_zero_inst_init
    }

    /// Initialize One instance for Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_one_inst_init == true`
    /// ENSURES: On success, required dependencies (`one`, `nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_one_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_one_inst_init {
            return Ok(());
        }

        self.init_one()?;
        self.init_nat()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        // Nat.succ Nat.zero
        let nat_one = Expr::app(
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );
        let one_mk = Expr::const_(Name::from_string("One.mk"), vec![Level::zero()]);

        // instOneNat : One Nat := One.mk (Nat.succ Nat.zero)
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("One"), vec![Level::zero()]),
            nat_const.clone(),
        );

        let inst_value = Expr::app(Expr::app(one_mk, nat_const), nat_one);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instOneNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.nat_one_inst_init = true;
        Ok(())
    }

    /// Check if Nat One instance has been initialized
    pub(crate) fn has_nat_one_inst(&self) -> bool {
        self.nat_one_inst_init
    }

    /// Initialize Add instance for Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_add_inst_init == true`
    /// ENSURES: On success, required dependencies (`add`, `nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_add_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_add_inst_init {
            return Ok(());
        }

        self.init_add()?;
        self.init_nat()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let add_mk = Expr::const_(Name::from_string("Add.mk"), vec![Level::zero()]);

        // instAddNat : Add Nat := Add.mk Nat.add
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Add"), vec![Level::zero()]),
            nat_const.clone(),
        );

        let inst_value = Expr::app(Expr::app(add_mk, nat_const), nat_add);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instAddNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.nat_add_inst_init = true;
        Ok(())
    }

    /// Check if Nat Add instance has been initialized
    pub(crate) fn has_nat_add_inst(&self) -> bool {
        self.nat_add_inst_init
    }

    /// Initialize Mul instance for Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_mul_inst_init == true`
    /// ENSURES: On success, required dependencies (`mul`, `nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_mul_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_mul_inst_init {
            return Ok(());
        }

        self.init_mul()?;
        self.init_nat()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let mul_mk = Expr::const_(Name::from_string("Mul.mk"), vec![Level::zero()]);

        // instMulNat : Mul Nat := Mul.mk Nat.mul
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Mul"), vec![Level::zero()]),
            nat_const.clone(),
        );

        let inst_value = Expr::app(Expr::app(mul_mk, nat_const), nat_mul);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instMulNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.nat_mul_inst_init = true;
        Ok(())
    }

    /// Check if Nat Mul instance has been initialized
    pub(crate) fn has_nat_mul_inst(&self) -> bool {
        self.nat_mul_inst_init
    }

    /// Initialize Sub instance for Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_sub_inst_init == true`
    /// ENSURES: On success, required dependencies (`sub`, `nat`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_sub_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_sub_inst_init {
            return Ok(());
        }

        self.init_sub()?;
        self.init_nat()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_sub = Expr::const_(Name::from_string("Nat.sub"), vec![]);
        let sub_mk = Expr::const_(Name::from_string("Sub.mk"), vec![Level::zero()]);

        // instSubNat : Sub Nat := Sub.mk Nat.sub
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Sub"), vec![Level::zero()]),
            nat_const.clone(),
        );

        let inst_value = Expr::app(Expr::app(sub_mk, nat_const), nat_sub);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instSubNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.nat_sub_inst_init = true;
        Ok(())
    }

    /// Check if Nat Sub instance has been initialized
    pub(crate) fn has_nat_sub_inst(&self) -> bool {
        self.nat_sub_inst_init
    }
}
