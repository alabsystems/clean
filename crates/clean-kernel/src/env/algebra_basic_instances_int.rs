// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Int typeclass instances for basic algebraic operations
//!
//! This module contains instance definitions for:
//! - Int: Zero, One, Add, Mul, Neg, Sub instances
//!
//! Nat instances are in algebra_basic_instances.rs.
//! Split from algebra_basic.rs for #307.

use crate::env::{
    Declaration, EnvError, Environment, KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    // ========================================================================
    // Typeclass Instances for Int
    // ========================================================================

    /// Initialize Zero instance for Int
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_zero_inst_init == true`
    /// ENSURES: On success, required dependencies (`zero`, `int`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_zero_inst(&mut self) -> Result<(), EnvError> {
        if self.int_zero_inst_init {
            return Ok(());
        }

        self.init_zero()?;
        self.init_int()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        // Int.ofNat Nat.zero
        let zero_const = Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );
        let zero_mk = Expr::const_(Name::from_string("Zero.mk"), vec![Level::zero()]);

        // instZeroInt : Zero Int := Zero.mk (Int.ofNat Nat.zero)
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Zero"), vec![Level::zero()]),
            int_const.clone(),
        );

        let inst_value = Expr::app(Expr::app(zero_mk, int_const), zero_const);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instZeroInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_zero_inst_init = true;
        Ok(())
    }

    /// Check if Int Zero instance has been initialized
    pub(crate) fn has_int_zero_inst(&self) -> bool {
        self.int_zero_inst_init
    }

    /// Initialize One instance for Int
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_one_inst_init == true`
    /// ENSURES: On success, required dependencies (`one`, `int`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_one_inst(&mut self) -> Result<(), EnvError> {
        if self.int_one_inst_init {
            return Ok(());
        }

        self.init_one()?;
        self.init_int()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        // Int.ofNat (Nat.succ Nat.zero)
        let one_const = Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::const_(Name::from_string("Nat.zero"), vec![]),
            ),
        );
        let one_mk = Expr::const_(Name::from_string("One.mk"), vec![Level::zero()]);

        // instOneInt : One Int := One.mk (Int.ofNat (Nat.succ Nat.zero))
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("One"), vec![Level::zero()]),
            int_const.clone(),
        );

        let inst_value = Expr::app(Expr::app(one_mk, int_const), one_const);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instOneInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_one_inst_init = true;
        Ok(())
    }

    /// Check if Int One instance has been initialized
    pub(crate) fn has_int_one_inst(&self) -> bool {
        self.int_one_inst_init
    }

    /// Initialize Add instance for Int
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_add_inst_init == true`
    /// ENSURES: On success, required dependencies (`add`, `int_arith`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_add_inst(&mut self) -> Result<(), EnvError> {
        if self.int_add_inst_init {
            return Ok(());
        }

        self.init_add()?;
        self.init_int_arith()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let add_mk = Expr::const_(Name::from_string("Add.mk"), vec![Level::zero()]);

        // instAddInt : Add Int := Add.mk Int.add
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Add"), vec![Level::zero()]),
            int_const.clone(),
        );

        let inst_value = Expr::app(Expr::app(add_mk, int_const), int_add);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instAddInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_add_inst_init = true;
        Ok(())
    }

    /// Check if Int Add instance has been initialized
    pub(crate) fn has_int_add_inst(&self) -> bool {
        self.int_add_inst_init
    }

    /// Initialize Mul instance for Int
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_mul_inst_init == true`
    /// ENSURES: On success, required dependencies (`mul`, `int_arith`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_mul_inst(&mut self) -> Result<(), EnvError> {
        if self.int_mul_inst_init {
            return Ok(());
        }

        self.init_mul()?;
        self.init_int_arith()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
        let mul_mk = Expr::const_(Name::from_string("Mul.mk"), vec![Level::zero()]);

        // instMulInt : Mul Int := Mul.mk Int.mul
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Mul"), vec![Level::zero()]),
            int_const.clone(),
        );

        let inst_value = Expr::app(Expr::app(mul_mk, int_const), int_mul);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instMulInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_mul_inst_init = true;
        Ok(())
    }

    /// Check if Int Mul instance has been initialized
    pub(crate) fn has_int_mul_inst(&self) -> bool {
        self.int_mul_inst_init
    }

    /// Initialize Neg instance for Int
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_neg_inst_init == true`
    /// ENSURES: On success, required dependencies (`neg`, `int_arith`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_neg_inst(&mut self) -> Result<(), EnvError> {
        // IMPORT MODE (`suppress_lossy_structure_stubs`, residual-to-zero
        // campaign 2026-07-03): the Clean-native Int arithmetic cluster is
        // NOT Lean-faithful in its SYMBOLIC reduction behaviour —
        // `Int.subNatNat` is an iterated-decrement loop (vs Lean's single
        // case on `Nat.sub n m`), so Lean-valid rfl-proofs over open Int
        // terms (`Int.exists_strictMono`: `negSucc (n+1) + 1 ≟ negSucc n`)
        // are rejected when the stubs SHADOW the genuine olean definitions.
        // In import mode skip the whole cluster so Lean's genuine
        // `Int.add`/`Int.subNatNat`/instances import through the checked
        // path (the caller-closure audit shows nothing else in the import
        // prelude references these names). The default proof-execution lane
        // (stubs + their constructive lemma web) is byte-identical.
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.int_neg_inst_init {
            return Ok(());
        }

        self.init_neg()?;
        self.init_int_arith()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_neg = Expr::const_(Name::from_string("Int.neg"), vec![]);
        let neg_mk = Expr::const_(Name::from_string("Neg.mk"), vec![Level::zero()]);

        // instNegInt : Neg Int := Neg.mk Int.neg
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Neg"), vec![Level::zero()]),
            int_const.clone(),
        );

        let inst_value = Expr::app(Expr::app(neg_mk, int_const), int_neg);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instNegInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        // Register with the kernel instance table so prefix `-` over `Int`
        // (desugared to `Neg.neg`) resolves its `[Neg Int]` argument instead of
        // leaking a metavariable ("contains free variables"). (Track EF)
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instNegInt"),
            class_name: Name::from_string("Neg"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.int_neg_inst_init = true;
        Ok(())
    }

    /// Check if Int Neg instance has been initialized
    pub(crate) fn has_int_neg_inst(&self) -> bool {
        self.int_neg_inst_init
    }

    /// Initialize Sub instance for Int
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_sub_inst_init == true`
    /// ENSURES: On success, required dependencies (`sub`, `int_arith`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_sub_inst(&mut self) -> Result<(), EnvError> {
        if self.int_sub_inst_init {
            return Ok(());
        }

        self.init_sub()?;
        self.init_int_arith()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_sub = Expr::const_(Name::from_string("Int.sub"), vec![]);
        let sub_mk = Expr::const_(Name::from_string("Sub.mk"), vec![Level::zero()]);

        // instSubInt : Sub Int := Sub.mk Int.sub
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Sub"), vec![Level::zero()]),
            int_const.clone(),
        );

        let inst_value = Expr::app(Expr::app(sub_mk, int_const), int_sub);

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instSubInt"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.int_sub_inst_init = true;
        Ok(())
    }

    /// Check if Int Sub instance has been initialized
    pub(crate) fn has_int_sub_inst(&self) -> bool {
        self.int_sub_inst_init
    }
}
