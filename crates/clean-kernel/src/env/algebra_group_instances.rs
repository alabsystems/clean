// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat/Int instances for commutative algebraic structures
//!
//! Split from algebra_groups.rs (#307). Contains:
//! - Nat AddCommSemigroup instance
//! - Int AddCommSemigroup instance
//! - Nat AddCommMonoid instance
//! - Int AddCommMonoid instance
//! - Int AddCommGroup instance

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Nat AddCommSemigroup instance
    ///
    /// Nat forms an AddCommSemigroup with Nat.add, Nat.add_assoc, Nat.add_comm
    pub(crate) fn init_nat_add_comm_semigroup_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_add_comm_semigroup_inst_init {
            return Ok(());
        }

        self.init_add_comm_semigroup()?;
        self.init_nat_arith_lemmas()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_add_assoc = Expr::const_(Name::from_string("Nat.add_assoc"), vec![]);
        let nat_add_comm = Expr::const_(Name::from_string("Nat.add_comm"), vec![]);

        let add_comm_semigroup_mk = Expr::const_(
            Name::from_string("AddCommSemigroup.mk"),
            vec![Level::zero()],
        );

        let inst_type = Expr::app(
            Expr::const_(Name::from_string("AddCommSemigroup"), vec![Level::zero()]),
            nat_const.clone(),
        );

        let inst_value = Expr::app(
            Expr::app(
                Expr::app(Expr::app(add_comm_semigroup_mk, nat_const), nat_add),
                nat_add_assoc,
            ),
            nat_add_comm,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instAddCommSemigroupNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.nat_add_comm_semigroup_inst_init = true;
        Ok(())
    }

    /// Check if Nat AddCommSemigroup instance has been initialized
    pub(crate) fn has_nat_add_comm_semigroup_inst(&self) -> bool {
        self.nat_add_comm_semigroup_inst_init
    }

    /// Initialize the Int AddCommSemigroup instance
    ///
    /// Int forms an AddCommSemigroup with Int.add, Int.add_assoc, Int.add_comm
    pub(crate) fn init_int_add_comm_semigroup_inst(&mut self) -> Result<(), EnvError> {
        if self.int_add_comm_semigroup_inst_init {
            return Ok(());
        }

        self.init_add_comm_semigroup()?;
        self.init_int_arith_lemmas()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_add_assoc = Expr::const_(Name::from_string("Int.add_assoc"), vec![]);
        let int_add_comm = Expr::const_(Name::from_string("Int.add_comm"), vec![]);

        let add_comm_semigroup_mk = Expr::const_(
            Name::from_string("AddCommSemigroup.mk"),
            vec![Level::zero()],
        );

        let inst_type = Expr::app(
            Expr::const_(Name::from_string("AddCommSemigroup"), vec![Level::zero()]),
            int_const.clone(),
        );

        let inst_value = Expr::app(
            Expr::app(
                Expr::app(Expr::app(add_comm_semigroup_mk, int_const), int_add),
                int_add_assoc,
            ),
            int_add_comm,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instAddCommSemigroupInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_add_comm_semigroup_inst_init = true;
        Ok(())
    }

    /// Check if Int AddCommSemigroup instance has been initialized
    pub(crate) fn has_int_add_comm_semigroup_inst(&self) -> bool {
        self.int_add_comm_semigroup_inst_init
    }

    /// Initialize the Nat AddCommMonoid instance
    ///
    /// Nat forms an AddCommMonoid with Nat.add, Nat.add_assoc, Nat.zero,
    /// Nat.zero_add, Nat.add_zero, Nat.add_comm
    pub(crate) fn init_nat_add_comm_monoid_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_add_comm_monoid_inst_init {
            return Ok(());
        }

        self.init_add_comm_monoid()?;
        self.init_nat_arith_lemmas()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_add_assoc = Expr::const_(Name::from_string("Nat.add_assoc"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_zero_add = Expr::const_(Name::from_string("Nat.zero_add"), vec![]);
        let nat_add_zero = Expr::const_(Name::from_string("Nat.add_zero"), vec![]);
        let nat_add_comm = Expr::const_(Name::from_string("Nat.add_comm"), vec![]);

        let add_comm_monoid_mk =
            Expr::const_(Name::from_string("AddCommMonoid.mk"), vec![Level::zero()]);

        let inst_type = Expr::app(
            Expr::const_(Name::from_string("AddCommMonoid"), vec![Level::zero()]),
            nat_const.clone(),
        );

        let inst_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(Expr::app(add_comm_monoid_mk, nat_const), nat_add),
                            nat_add_assoc,
                        ),
                        nat_zero,
                    ),
                    nat_zero_add,
                ),
                nat_add_zero,
            ),
            nat_add_comm,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instAddCommMonoidNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.nat_add_comm_monoid_inst_init = true;
        Ok(())
    }

    /// Check if Nat AddCommMonoid instance has been initialized
    pub(crate) fn has_nat_add_comm_monoid_inst(&self) -> bool {
        self.nat_add_comm_monoid_inst_init
    }

    /// Initialize the Int AddCommMonoid instance
    ///
    /// Int forms an AddCommMonoid with Int.add, Int.add_assoc, Int.zero,
    /// Int.zero_add, Int.add_zero, Int.add_comm
    pub(crate) fn init_int_add_comm_monoid_inst(&mut self) -> Result<(), EnvError> {
        if self.int_add_comm_monoid_inst_init {
            return Ok(());
        }

        self.init_add_comm_monoid()?;
        self.init_int_arith_lemmas()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_add_assoc = Expr::const_(Name::from_string("Int.add_assoc"), vec![]);
        let int_zero = Expr::const_(Name::from_string("Int.zero"), vec![]);
        let int_zero_add = Expr::const_(Name::from_string("Int.zero_add"), vec![]);
        let int_add_zero = Expr::const_(Name::from_string("Int.add_zero"), vec![]);
        let int_add_comm = Expr::const_(Name::from_string("Int.add_comm"), vec![]);

        let add_comm_monoid_mk =
            Expr::const_(Name::from_string("AddCommMonoid.mk"), vec![Level::zero()]);

        let inst_type = Expr::app(
            Expr::const_(Name::from_string("AddCommMonoid"), vec![Level::zero()]),
            int_const.clone(),
        );

        let inst_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(Expr::app(add_comm_monoid_mk, int_const), int_add),
                            int_add_assoc,
                        ),
                        int_zero,
                    ),
                    int_zero_add,
                ),
                int_add_zero,
            ),
            int_add_comm,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instAddCommMonoidInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_add_comm_monoid_inst_init = true;
        Ok(())
    }

    /// Check if Int AddCommMonoid instance has been initialized
    pub(crate) fn has_int_add_comm_monoid_inst(&self) -> bool {
        self.int_add_comm_monoid_inst_init
    }

    /// Initialize the Int AddCommGroup instance
    ///
    /// Int forms an AddCommGroup with Int.add, Int.add_assoc, Int.zero,
    /// Int.zero_add, Int.add_zero, Int.neg, Int.neg_add_self, Int.add_comm
    pub(crate) fn init_int_add_comm_group_inst(&mut self) -> Result<(), EnvError> {
        if self.int_add_comm_group_inst_init {
            return Ok(());
        }

        self.init_add_comm_group()?;
        self.init_int_arith_lemmas()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_add_assoc = Expr::const_(Name::from_string("Int.add_assoc"), vec![]);
        let int_zero = Expr::const_(Name::from_string("Int.zero"), vec![]);
        let int_zero_add = Expr::const_(Name::from_string("Int.zero_add"), vec![]);
        let int_add_zero = Expr::const_(Name::from_string("Int.add_zero"), vec![]);
        let int_neg = Expr::const_(Name::from_string("Int.neg"), vec![]);
        let int_neg_add_self = Expr::const_(Name::from_string("Int.neg_add_self"), vec![]);
        let int_add_comm = Expr::const_(Name::from_string("Int.add_comm"), vec![]);

        let add_comm_group_mk =
            Expr::const_(Name::from_string("AddCommGroup.mk"), vec![Level::zero()]);

        let inst_type = Expr::app(
            Expr::const_(Name::from_string("AddCommGroup"), vec![Level::zero()]),
            int_const.clone(),
        );

        let inst_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(Expr::app(add_comm_group_mk, int_const), int_add),
                                    int_add_assoc,
                                ),
                                int_zero,
                            ),
                            int_zero_add,
                        ),
                        int_add_zero,
                    ),
                    int_neg,
                ),
                int_neg_add_self,
            ),
            int_add_comm,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instAddCommGroupInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_add_comm_group_inst_init = true;
        Ok(())
    }

    /// Check if Int AddCommGroup instance has been initialized
    pub(crate) fn has_int_add_comm_group_inst(&self) -> bool {
        self.int_add_comm_group_inst_init
    }
}
