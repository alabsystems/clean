// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Nat/Int Semiring and Ring instances
//!
//! This module contains concrete instances:
//! - Nat Semiring instance
//! - Int Semiring instance
//! - Int Ring instance

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Nat Semiring instance
    ///
    /// Nat forms a Semiring with:
    /// - add = Nat.add
    /// - zero = Nat.zero
    /// - mul = Nat.mul
    /// - one = Nat.succ Nat.zero
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_semiring_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_semiring_inst(&mut self) -> Result<(), EnvError> {
        if self.nat_semiring_inst_init {
            return Ok(());
        }

        self.init_semiring()?;
        self.init_nat()?;
        self.init_nat_arith_lemmas()?;

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let nat_one = Expr::app(nat_succ, nat_zero.clone());

        // Instance type: Semiring Nat
        // Nat : Type 0 = Sort 1, so universe is Level::succ(Level::zero())
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Semiring"), vec![Level::zero()]),
            nat_const.clone(),
        );

        // Instance value: Semiring.mk Nat.add Nat.add_assoc Nat.zero Nat.zero_add Nat.add_zero
        //                              Nat.add_comm Nat.mul Nat.mul_assoc (Nat.succ Nat.zero)
        //                              Nat.one_mul Nat.mul_one Nat.zero_mul Nat.mul_zero
        //                              Nat.left_distrib Nat.right_distrib
        let inst_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::app(
                                            Expr::app(
                                                Expr::app(
                                                    Expr::app(
                                                        Expr::app(
                                                            Expr::app(
                                                                Expr::app(
                                                                    Expr::app(
                                                                        Expr::const_(
                                                                            Name::from_string(
                                                                                "Semiring.mk",
                                                                            ),
                                                                            // Nat : Type 0, so universe param is 0
                                                                            vec![Level::zero()],
                                                                        ),
                                                                        nat_const.clone(),
                                                                    ),
                                                                    nat_add, // add
                                                                ),
                                                                Expr::const_(
                                                                    Name::from_string(
                                                                        "Nat.add_assoc",
                                                                    ),
                                                                    vec![],
                                                                ),
                                                            ),
                                                            nat_zero, // zero
                                                        ),
                                                        Expr::const_(
                                                            Name::from_string("Nat.zero_add"),
                                                            vec![],
                                                        ),
                                                    ),
                                                    Expr::const_(
                                                        Name::from_string("Nat.add_zero"),
                                                        vec![],
                                                    ),
                                                ),
                                                Expr::const_(
                                                    Name::from_string("Nat.add_comm"),
                                                    vec![],
                                                ),
                                            ),
                                            nat_mul, // mul
                                        ),
                                        Expr::const_(Name::from_string("Nat.mul_assoc"), vec![]),
                                    ),
                                    nat_one, // one
                                ),
                                Expr::const_(Name::from_string("Nat.one_mul"), vec![]),
                            ),
                            Expr::const_(Name::from_string("Nat.mul_one"), vec![]),
                        ),
                        Expr::const_(Name::from_string("Nat.zero_mul"), vec![]),
                    ),
                    Expr::const_(Name::from_string("Nat.mul_zero"), vec![]),
                ),
                Expr::const_(Name::from_string("Nat.left_distrib"), vec![]),
            ),
            Expr::const_(Name::from_string("Nat.right_distrib"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instSemiringNat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.nat_semiring_inst_init = true;
        Ok(())
    }

    /// Check if Nat Semiring instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_semiring_inst_init == true`
    pub(crate) fn has_nat_semiring_inst(&self) -> bool {
        self.nat_semiring_inst_init
    }

    /// Initialize the Int Semiring instance
    ///
    /// Int forms a Semiring with:
    /// - add = Int.add
    /// - zero = Int.ofNat 0
    /// - mul = Int.mul
    /// - one = Int.ofNat 1
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_semiring_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_semiring_inst(&mut self) -> Result<(), EnvError> {
        if self.int_semiring_inst_init {
            return Ok(());
        }

        self.init_semiring()?;
        self.init_int_arith()?;
        self.init_int_arith_lemmas()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let int_zero = Expr::const_(Name::from_string("Int.zero"), vec![]);
        let int_one = Expr::app(int_of_nat, Expr::app(nat_succ, nat_zero));

        // Instance type: Semiring Int
        // Int : Type 0 = Sort 1, so universe is Level::succ(Level::zero())
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Semiring"), vec![Level::zero()]),
            int_const.clone(),
        );

        // Instance value: Semiring.mk Int.add Int.add_assoc (Int.ofNat 0) Int.zero_add Int.add_zero
        //                              Int.add_comm Int.mul Int.mul_assoc (Int.ofNat 1)
        //                              Int.one_mul Int.mul_one Int.zero_mul Int.mul_zero
        //                              Int.left_distrib Int.right_distrib
        let inst_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::app(
                                            Expr::app(
                                                Expr::app(
                                                    Expr::app(
                                                        Expr::app(
                                                            Expr::app(
                                                                Expr::app(
                                                                    Expr::app(
                                                                        Expr::const_(
                                                                            Name::from_string(
                                                                                "Semiring.mk",
                                                                            ),
                                                                            // Int : Type 0, so universe param is 0
                                                                            vec![Level::zero()],
                                                                        ),
                                                                        int_const.clone(),
                                                                    ),
                                                                    int_add, // add
                                                                ),
                                                                Expr::const_(
                                                                    Name::from_string(
                                                                        "Int.add_assoc",
                                                                    ),
                                                                    vec![],
                                                                ),
                                                            ),
                                                            int_zero, // zero
                                                        ),
                                                        Expr::const_(
                                                            Name::from_string("Int.zero_add"),
                                                            vec![],
                                                        ),
                                                    ),
                                                    Expr::const_(
                                                        Name::from_string("Int.add_zero"),
                                                        vec![],
                                                    ),
                                                ),
                                                Expr::const_(
                                                    Name::from_string("Int.add_comm"),
                                                    vec![],
                                                ),
                                            ),
                                            int_mul, // mul
                                        ),
                                        Expr::const_(Name::from_string("Int.mul_assoc"), vec![]),
                                    ),
                                    int_one, // one
                                ),
                                Expr::const_(Name::from_string("Int.one_mul"), vec![]),
                            ),
                            Expr::const_(Name::from_string("Int.mul_one"), vec![]),
                        ),
                        Expr::const_(Name::from_string("Int.zero_mul"), vec![]),
                    ),
                    Expr::const_(Name::from_string("Int.mul_zero"), vec![]),
                ),
                Expr::const_(Name::from_string("Int.left_distrib"), vec![]),
            ),
            Expr::const_(Name::from_string("Int.right_distrib"), vec![]),
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instSemiringInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_semiring_inst_init = true;
        Ok(())
    }

    /// Check if Int Semiring instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_semiring_inst_init == true`
    pub(crate) fn has_int_semiring_inst(&self) -> bool {
        self.int_semiring_inst_init
    }

    /// Initialize the Int Ring instance
    ///
    /// Int forms a Ring with:
    /// - All Semiring fields
    /// - neg = Int.neg
    /// - add_left_neg = Int.neg_add_self
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_ring_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_ring_inst(&mut self) -> Result<(), EnvError> {
        if self.int_ring_inst_init {
            return Ok(());
        }

        self.init_ring()?;
        self.init_int_arith()?;
        self.init_int_arith_lemmas()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
        let int_neg = Expr::const_(Name::from_string("Int.neg"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let int_zero = Expr::const_(Name::from_string("Int.zero"), vec![]);
        let int_one = Expr::app(int_of_nat, Expr::app(nat_succ, nat_zero));

        // Instance type: Ring Int
        // Int : Type 0 = Sort 1, so universe is Level::succ(Level::zero())
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Ring"), vec![Level::zero()]),
            int_const.clone(),
        );

        // Instance value: Ring.mk Int.add Int.add_assoc (Int.ofNat 0) Int.zero_add Int.add_zero
        //                         Int.add_comm Int.mul Int.mul_assoc (Int.ofNat 1)
        //                         Int.one_mul Int.mul_one Int.zero_mul Int.mul_zero
        //                         Int.left_distrib Int.right_distrib Int.neg Int.neg_add_self
        let inst_value = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::app(
                                            Expr::app(
                                                Expr::app(
                                                    Expr::app(
                                                        Expr::app(
                                                            Expr::app(
                                                                Expr::app(
                                                                    Expr::app(
                                                                        Expr::app(
                                                                            Expr::app(
                                                                                Expr::const_(
                                                                                    Name::from_string("Ring.mk"),
                                                                                    vec![Level::zero()],
                                                                                ),
                                                                                int_const.clone(),
                                                                            ),
                                                                            int_add, // add
                                                                        ),
                                                                        Expr::const_(Name::from_string("Int.add_assoc"), vec![]),
                                                                    ),
                                                                    int_zero, // zero
                                                                ),
                                                                Expr::const_(Name::from_string("Int.zero_add"), vec![]),
                                                            ),
                                                            Expr::const_(Name::from_string("Int.add_zero"), vec![]),
                                                        ),
                                                        Expr::const_(Name::from_string("Int.add_comm"), vec![]),
                                                    ),
                                                    int_mul, // mul
                                                ),
                                                Expr::const_(Name::from_string("Int.mul_assoc"), vec![]),
                                            ),
                                            int_one, // one
                                        ),
                                        Expr::const_(Name::from_string("Int.one_mul"), vec![]),
                                    ),
                                    Expr::const_(Name::from_string("Int.mul_one"), vec![]),
                                ),
                                Expr::const_(Name::from_string("Int.zero_mul"), vec![]),
                            ),
                            Expr::const_(Name::from_string("Int.mul_zero"), vec![]),
                        ),
                        Expr::const_(Name::from_string("Int.left_distrib"), vec![]),
                    ),
                    Expr::const_(Name::from_string("Int.right_distrib"), vec![]),
                ),
                int_neg, // neg
            ),
            Expr::const_(Name::from_string("Int.neg_add_self"), vec![]), // add_left_neg
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instRingInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_ring_inst_init = true;
        Ok(())
    }

    /// Check if Int Ring instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_ring_inst_init == true`
    pub(crate) fn has_int_ring_inst(&self) -> bool {
        self.int_ring_inst_init
    }
}
