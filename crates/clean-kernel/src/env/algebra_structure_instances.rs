// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat/Int AddSemigroup and AddMonoid instances
//!
//! Concrete instances of the base algebraic structures for Nat and Int.
//! The generic typeclass definitions are in algebra_structures.rs.

use crate::env::Environment;
#[cfg(test)]
use crate::env::{Declaration, EnvError};
#[cfg(test)]
use crate::expr::Expr;
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

impl Environment {
    // -----------------------------------------------------------------------
    // Nat/Int AddSemigroup and AddMonoid instances
    // -----------------------------------------------------------------------

    /// Initialize the instAddSemigroupNat instance
    ///
    /// This creates an AddSemigroup instance for Nat using Nat.add and Nat.add_assoc
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_add_semigroup_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_nat_add_semigroup_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_add_semigroup_inst_init {
            return Ok(());
        }

        self.init_add_semigroup()?;
        self.init_nat_arith_lemmas()?; // For Nat.add_assoc

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_add_assoc = Expr::const_(Name::from_string("Nat.add_assoc"), vec![]);
        let add_semigroup_mk =
            Expr::const_(Name::from_string("AddSemigroup.mk"), vec![Level::zero()]);

        // Type: AddSemigroup Nat
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("AddSemigroup"), vec![Level::zero()]),
            nat_const.clone(),
        );

        // Value: AddSemigroup.mk Nat.add Nat.add_assoc
        let inst_value = Expr::app(
            Expr::app(Expr::app(add_semigroup_mk, nat_const), nat_add),
            nat_add_assoc,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instAddSemigroupNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.nat_add_semigroup_inst_init = true;
        Ok(())
    }

    /// Check if Nat AddSemigroup instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_add_semigroup_inst_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_add_semigroup_inst(&self) -> bool {
        self.nat_add_semigroup_inst_init
    }

    /// Initialize the instAddSemigroupInt instance
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_add_semigroup_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_int_add_semigroup_inst(&mut self) -> Result<(), EnvError> {
        if self.int_add_semigroup_inst_init {
            return Ok(());
        }

        self.init_add_semigroup()?;
        self.init_int_arith_lemmas()?; // For Int.add_assoc

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_add_assoc = Expr::const_(Name::from_string("Int.add_assoc"), vec![]);
        let add_semigroup_mk =
            Expr::const_(Name::from_string("AddSemigroup.mk"), vec![Level::zero()]);

        let inst_type = Expr::app(
            Expr::const_(Name::from_string("AddSemigroup"), vec![Level::zero()]),
            int_const.clone(),
        );

        let inst_value = Expr::app(
            Expr::app(Expr::app(add_semigroup_mk, int_const), int_add),
            int_add_assoc,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instAddSemigroupInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_add_semigroup_inst_init = true;
        Ok(())
    }

    /// Check if Int AddSemigroup instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_add_semigroup_inst_init == true`
    #[cfg(test)]
    pub(crate) fn has_int_add_semigroup_inst(&self) -> bool {
        self.int_add_semigroup_inst_init
    }

    /// Initialize the instAddMonoidNat instance
    ///
    /// This creates an AddMonoid instance for Nat
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_add_monoid_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_nat_add_monoid_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_add_monoid_inst_init {
            return Ok(());
        }

        self.init_add_monoid()?;
        self.init_nat_arith_lemmas()?; // For Nat.add_assoc, Nat.zero_add, Nat.add_zero

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_add_assoc = Expr::const_(Name::from_string("Nat.add_assoc"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_zero_add = Expr::const_(Name::from_string("Nat.zero_add"), vec![]);
        let nat_add_zero = Expr::const_(Name::from_string("Nat.add_zero"), vec![]);
        let add_monoid_mk = Expr::const_(Name::from_string("AddMonoid.mk"), vec![Level::zero()]);

        let inst_type = Expr::app(
            Expr::const_(Name::from_string("AddMonoid"), vec![Level::zero()]),
            nat_const.clone(),
        );

        // AddMonoid.mk Nat.add Nat.add_assoc Nat.zero Nat.zero_add Nat.add_zero
        let inst_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(add_monoid_mk, nat_const), nat_add),
                        nat_add_assoc,
                    ),
                    nat_zero,
                ),
                nat_zero_add,
            ),
            nat_add_zero,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instAddMonoidNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.nat_add_monoid_inst_init = true;
        Ok(())
    }

    /// Check if Nat AddMonoid instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_add_monoid_inst_init == true`
    #[cfg(test)]
    pub(crate) fn has_nat_add_monoid_inst(&self) -> bool {
        self.nat_add_monoid_inst_init
    }

    /// Initialize the instAddMonoidInt instance
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_add_monoid_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_int_add_monoid_inst(&mut self) -> Result<(), EnvError> {
        if self.int_add_monoid_inst_init {
            return Ok(());
        }

        self.init_add_monoid()?;
        self.init_int_arith_lemmas()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_add_assoc = Expr::const_(Name::from_string("Int.add_assoc"), vec![]);
        let int_zero = Expr::const_(Name::from_string("Int.zero"), vec![]);
        let int_zero_add = Expr::const_(Name::from_string("Int.zero_add"), vec![]);
        let int_add_zero = Expr::const_(Name::from_string("Int.add_zero"), vec![]);
        let add_monoid_mk = Expr::const_(Name::from_string("AddMonoid.mk"), vec![Level::zero()]);

        let inst_type = Expr::app(
            Expr::const_(Name::from_string("AddMonoid"), vec![Level::zero()]),
            int_const.clone(),
        );

        let inst_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(add_monoid_mk, int_const), int_add),
                        int_add_assoc,
                    ),
                    int_zero,
                ),
                int_zero_add,
            ),
            int_add_zero,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instAddMonoidInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_add_monoid_inst_init = true;
        Ok(())
    }

    /// Check if Int AddMonoid instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_add_monoid_inst_init == true`
    #[cfg(test)]
    pub(crate) fn has_int_add_monoid_inst(&self) -> bool {
        self.int_add_monoid_inst_init
    }
}
