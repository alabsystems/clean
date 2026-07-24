// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rational number core types and operations for Environment
//!
//! This module contains basic Rat initialization:
//! - Rat type, constructors, projections
//! - Rat arithmetic operations (add, sub, mul, neg, inv, div)
//! - Rat normalization (Rat.normalize)
//! - Rat ordering (le, lt, instLERat, instLTRat)
//!
//! Field instances are in `algebra_field`.
//! Abs/MinMax/DecidableOrd are in `algebra_abs`.
//! Distance metrics are in `algebra_dist`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the Rat (rational number) type
    ///
    /// Rat is defined as:
    /// inductive Rat where
    ///   | mk (num : Int) (denom : Nat) : Rat
    ///
    /// The invariant (denom > 0, gcd |num| denom = 1) is maintained externally.
    /// Also adds:
    /// - Rat.num : Rat → Int (numerator projection)
    /// - Rat.denom : Rat → Nat (denominator projection)
    /// - Rat.zero : Rat := Rat.mk 0 1
    /// - Rat.one : Rat := Rat.mk 1 1
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.rat_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_rat(&mut self) -> Result<(), EnvError> {
        if self.rat_init {
            return Ok(());
        }

        // Ensure Int and Nat are initialized
        self.init_int()?;
        // `Eq` is needed for the `Rat.Raw.Equiv` definition (its body is
        // `Eq Int … …`). `init_eq` does not depend on `init_rat`, so this
        // introduces no init cycle.
        self.init_eq()?;
        // The `Rat.Raw.Equiv` body multiplies numerators by effective
        // denominators (`Int.mul`, `Int.ofNat`); pull in Int arithmetic.
        // `init_int_arith` does not depend on `init_rat`, so no init cycle.
        self.init_int_arith()?;

        // WS-A ATOMIC LIVE SWITCH (step 1, carrier): the live `Rat` IS now the
        // QUOTIENT carrier `Rat := @Quot.{1} Rat.Raw Rat.Raw.Equiv`, with
        // `Rat.mk n d := @Quot.mk _ Rat.Raw.Equiv (Rat.Raw.mk n d)`. This makes
        // the structural-equality `Rat.*` axioms (`zero_mul`, distrib, cancel,
        // `le_antisymm`, …) genuine theorems (they identify equivalent
        // representatives). `Rat.num`/`Rat.denom` are NOT registered: they are
        // not well-defined on the quotient; consumers project via
        // `Rat.Raw.num`/`Rat.Raw.denom` on representatives instead.
        //
        // `rat_quotient_carrier_into_live` registers the `Rat.Raw` pre-quotient
        // carrier + `Rat.Raw.Equiv` (+ refl/symm/trans) and then the quotient
        // `Rat`, `Rat.mk`, `Rat.zero`, `Rat.one`.
        self.rat_quotient_carrier_into_live()?;

        self.rat_init = true;
        Ok(())
    }

    /// Check if Rat has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.rat_init == true`
    pub(crate) fn has_rat(&self) -> bool {
        self.rat_init
    }

    /// Check if Rat arithmetic has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.rat_arith_init == true`
    pub(crate) fn has_rat_arith(&self) -> bool {
        self.rat_arith_init
    }

    /// Initialize Rat arithmetic operations
    ///
    /// This adds:
    /// - Rat.neg : Rat → Rat (negation)
    /// - Rat.add : Rat → Rat → Rat (addition)
    /// - Rat.sub : Rat → Rat → Rat (subtraction)
    /// - Rat.mul : Rat → Rat → Rat (multiplication)
    /// - Rat.inv : Rat → Rat (multiplicative inverse)
    /// - Rat.div : Rat → Rat → Rat (division)
    ///
    /// These are defined using Int and Nat operations.
    /// For simplicity, we do NOT normalize to lowest terms in the kernel.
    /// Normalization is done by the consumer or by tactics.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.rat_arith_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_rat_arith(&mut self) -> Result<(), EnvError> {
        if self.rat_arith_init {
            return Ok(());
        }

        // Ensure Rat and Int arithmetic are initialized
        self.init_rat()?;
        self.init_int_arith()?;

        // WS-A ATOMIC LIVE SWITCH (step 2, arithmetic): register the QUOTIENT
        // operations `Rat.neg/add/mul/inv/div`, each a checked `Quot.lift` whose
        // well-definedness (respect of `Rat.Raw.Equiv`) is a kernel-checked
        // proof. They normalize via the EFFECTIVE denominator, which restores
        // the well-definedness the free carrier lacked.
        self.rat_quotient_arith_into_live()?;

        // Rat.sub : Rat → Rat → Rat := fun a b => Rat.add a (Rat.neg b)
        // (purely in terms of the quotient `Rat.add`/`Rat.neg`).
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_neg_const = Expr::const_(Name::from_string("Rat.neg"), vec![]);
        let rat_add_const = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let rat_sub_type = Expr::pi(
            BinderInfo::Default,
            rat_const.clone(),
            Expr::pi(BinderInfo::Default, rat_const.clone(), rat_const.clone()),
        );
        let rat_sub_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a) = b.fresh_local(rat_const.clone());
            let (bv_id, bv) = b.fresh_local(rat_const.clone());
            let neg_bv = Expr::app(rat_neg_const.clone(), bv);
            let body = Expr::app(Expr::app(rat_add_const.clone(), a), neg_bv);
            let e = b.mk_lam(bv_id, BinderInfo::Default, rat_const.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Default, rat_const.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Rat.sub"),
            level_params: vec![],
            type_: rat_sub_type,
            value: rat_sub_value,
            is_reducible: true,
        })?;

        self.rat_arith_init = true;
        Ok(())
    }

    /// Initialize Rat normalization
    ///
    /// This adds:
    /// - Rat.normalize : Rat → Rat (reduce numerator/denominator by their gcd)
    ///
    /// The definition guards against gcd = 0 by using max(gcd, 1) as the divisor.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.rat_normalize_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_rat_normalize(&mut self) -> Result<(), EnvError> {
        if self.rat_normalize_init {
            return Ok(());
        }

        // Dependencies: Rat arithmetic.
        self.init_rat_arith()?;

        // WS-A ATOMIC LIVE SWITCH: over the QUOTIENT carrier the rational is
        // ALREADY in canonical form (the quotient identifies every representative
        // of a fraction), so reduction-to-lowest-terms is the identity on `Rat`.
        // The old free-carrier `Rat.normalize` projected `Rat.num`/`Rat.denom`
        // and `gcd`-divided them — those projections are not well-defined on the
        // quotient, and normalization is semantically a no-op here.
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let normalize_type = Expr::pi(BinderInfo::Default, rat_const.clone(), rat_const.clone());
        let normalize_value = {
            let mut bd = EnvDeclBuilder::new();
            let (r_id, r) = bd.fresh_local(rat_const.clone());
            let e = bd.mk_lam(r_id, BinderInfo::Default, rat_const.clone(), r);
            bd.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Rat.normalize"),
            level_params: vec![],
            type_: normalize_type,
            value: normalize_value,
            is_reducible: true,
        })?;

        self.rat_normalize_init = true;
        Ok(())
    }

    /// Check if Rat normalization has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.rat_normalize_init == true`
    pub(crate) fn has_rat_normalize(&self) -> bool {
        self.rat_normalize_init
    }

    /// Initialize Rat ordering operations
    ///
    /// This adds:
    /// - Rat.le : Rat → Rat → Prop (a ≤ b iff num_a * denom_b ≤ num_b * denom_a)
    /// - Rat.lt : Rat → Rat → Prop (a < b iff num_a * denom_b < num_b * denom_a)
    /// - instLERat : LE Rat
    /// - instLTRat : LT Rat
    ///
    /// For rationals a/b and c/d (with positive denominators), a/b ≤ c/d ⟺ a*d ≤ c*b.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.rat_ord_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_rat_ord(&mut self) -> Result<(), EnvError> {
        if self.rat_ord_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_rat()?;
        self.init_int_ord()?; // Provides Int.le, Int.lt
        self.init_le()?; // Provides LE typeclass
        self.init_lt()?; // Provides LT typeclass

        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);

        // WS-A ATOMIC LIVE SWITCH (step 2, order): register the QUOTIENT
        // `Rat.le`/`Rat.lt` (each a binary `Quot.lift` into `Prop` whose respect
        // of `Rat.Raw.Equiv` is a kernel-checked proof). The lift compares
        // `num · ofNat (Rat.Raw.effDenom)` cross-products on representatives, so
        // it matches the previous definitional shape on well-formed Rats while
        // being genuinely well-defined on the quotient. There is no live
        // `Rat.effDenom` on the quotient (it is not well-defined); the lift uses
        // `Rat.Raw.effDenom` internally.
        self.rat_quotient_ord_into_live()?;

        // ========================================
        // instLERat : LE Rat := ⟨Rat.le⟩
        // Rat : Type 0, so LE.{0}
        // ========================================
        let inst_le_rat_type = Expr::app(
            Expr::const_(Name::from_string("LE"), vec![Level::zero()]),
            rat_const.clone(),
        );

        let rat_le_def = Expr::const_(Name::from_string("Rat.le"), vec![]);

        // LE.mk @Rat Rat.le
        let inst_le_rat_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("LE.mk"), vec![Level::zero()]),
                rat_const.clone(),
            ),
            rat_le_def,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instLERat"),
            level_params: vec![],
            type_: inst_le_rat_type,
            value: inst_le_rat_value,
            is_reducible: true,
        })?;

        // ========================================
        // instLTRat : LT Rat := ⟨Rat.lt⟩
        // Rat : Type 0, so LT.{0}
        // ========================================
        let inst_lt_rat_type = Expr::app(
            Expr::const_(Name::from_string("LT"), vec![Level::zero()]),
            rat_const.clone(),
        );

        let rat_lt_def = Expr::const_(Name::from_string("Rat.lt"), vec![]);

        // LT.mk @Rat Rat.lt
        let inst_lt_rat_value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("LT.mk"), vec![Level::zero()]),
                rat_const.clone(),
            ),
            rat_lt_def,
        );

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instLTRat"),
            level_params: vec![],
            type_: inst_lt_rat_type,
            value: inst_lt_rat_value,
            is_reducible: true,
        })?;

        self.rat_ord_init = true;
        Ok(())
    }

    /// Check if Rat ordering has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.rat_ord_init == true`
    pub(crate) fn has_rat_ord(&self) -> bool {
        self.rat_ord_init
    }
}
