// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Int min/max and abs properties
//!
//! Contains:
//! - init_int_minmax: Int.min, Int.max and characterizing properties
//! - init_int_abs_props: Int.abs nonneg, triangle inequality, etc.
//!
//! Extracted from `algebra_abs.rs` for maintainability.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Int min/max functions
    ///
    /// Adds:
    /// - `Int.min : Int → Int → Int` (axiom)
    /// - `Int.max : Int → Int → Int` (axiom)
    /// - `Int.min_def : ∀ a b : Int, Int.le a b → Eq (Int.min a b) a` - min picks smaller
    /// - `Int.min_def' : ∀ a b : Int, Int.le b a → Eq (Int.min a b) b` - symmetric case
    /// - `Int.max_def : ∀ a b : Int, Int.le a b → Eq (Int.max a b) b` - max picks larger
    /// - `Int.max_def' : ∀ a b : Int, Int.le b a → Eq (Int.max a b) a` - symmetric case
    ///
    /// Note: min and max are defined axiomatically with their characterizing properties.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_minmax_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_minmax(&mut self) -> Result<(), EnvError> {
        if self.int_minmax_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_int_ord()?; // Provides Int.le
        self.init_eq()?; // Provides Eq

        // ELIMINATION: `Int.min` / `Int.max` are now reducible Definitions and
        // `Int.min_def` / `Int.max_def` are kernel-checked Theorems (see
        // `algebra_int_minmax_proof.rs`). Registering them here first means the
        // four `Declaration::Axiom` blocks below are skipped (each is now guarded
        // by a `get_const` check). `Int.min_def'` / `Int.max_def'` remain admitted
        // axioms (they need the reverse `ble` reflection + `Int.le_antisymm`).
        self.register_int_minmax_proofs()?;
        // ELIMINATION: `Int.min_def'` / `Int.max_def'` are now Constructive
        // Theorems (reverse `ble` reflection + `Int.le_antisymm`); the two axiom
        // blocks below are guarded and skip.
        self.register_int_minmax_def_prime()?;

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_le = Expr::const_(Name::from_string("Int.le"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // ========================================
        // Int.min : Int → Int → Int
        // ========================================
        let int_minmax_type = Expr::pi(
            BinderInfo::Default,
            int_const.clone(),
            Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone()),
        );

        if self.get_const(&Name::from_string("Int.min")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.min"),
                level_params: vec![],
                type_: int_minmax_type.clone(),
            })?;
        }

        // ========================================
        // Int.max : Int → Int → Int
        // ========================================
        if self.get_const(&Name::from_string("Int.max")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.max"),
                level_params: vec![],
                type_: int_minmax_type,
            })?;
        }

        let int_min = Expr::const_(Name::from_string("Int.min"), vec![]);
        let int_max = Expr::const_(Name::from_string("Int.max"), vec![]);

        // ========================================
        // Int.min_def : ∀ a b : Int, Int.le a b → Eq (Int.min a b) a
        // When a ≤ b, min a b = a
        // ========================================
        let min_def_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, bvar) = bldr.fresh_local(int_const.clone());
            let le_a_b = Expr::app(Expr::app(int_le.clone(), a.clone()), bvar.clone());
            let (h_id, _h) = bldr.fresh_local(le_a_b.clone());
            let min_a_b = Expr::app(Expr::app(int_min.clone(), a.clone()), bvar.clone());
            let eq_min_a_b_a = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), int_const.clone()), min_a_b),
                a.clone(),
            );
            let e = bldr.mk_pi(h_id, BinderInfo::Default, le_a_b, eq_min_a_b_a);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, int_const.clone(), e);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        if self.get_const(&Name::from_string("Int.min_def")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.min_def"),
                level_params: vec![],
                type_: min_def_type,
            })?;
        }

        // ========================================
        // Int.min_def' : ∀ a b : Int, Int.le b a → Eq (Int.min a b) b
        // When b ≤ a, min a b = b
        // ========================================
        let min_def_alt_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, bvar) = bldr.fresh_local(int_const.clone());
            let le_b_a = Expr::app(Expr::app(int_le.clone(), bvar.clone()), a.clone());
            let (h_id, _h) = bldr.fresh_local(le_b_a.clone());
            let min_a_b = Expr::app(Expr::app(int_min.clone(), a.clone()), bvar.clone());
            let eq_min_a_b_b = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), int_const.clone()), min_a_b),
                bvar.clone(),
            );
            let e = bldr.mk_pi(h_id, BinderInfo::Default, le_b_a, eq_min_a_b_b);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, int_const.clone(), e);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        if self.get_const(&Name::from_string("Int.min_def'")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.min_def'"),
                level_params: vec![],
                type_: min_def_alt_type,
            })?;
        }

        // ========================================
        // Int.max_def : ∀ a b : Int, Int.le a b → Eq (Int.max a b) b
        // When a ≤ b, max a b = b
        // ========================================
        let max_def_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, bvar) = bldr.fresh_local(int_const.clone());
            let le_a_b = Expr::app(Expr::app(int_le.clone(), a.clone()), bvar.clone());
            let (h_id, _h) = bldr.fresh_local(le_a_b.clone());
            let max_a_b = Expr::app(Expr::app(int_max.clone(), a.clone()), bvar.clone());
            let eq_max_a_b_b = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), int_const.clone()), max_a_b),
                bvar.clone(),
            );
            let e = bldr.mk_pi(h_id, BinderInfo::Default, le_a_b, eq_max_a_b_b);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, int_const.clone(), e);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        if self.get_const(&Name::from_string("Int.max_def")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.max_def"),
                level_params: vec![],
                type_: max_def_type,
            })?;
        }

        // ========================================
        // Int.max_def' : ∀ a b : Int, Int.le b a → Eq (Int.max a b) a
        // When b ≤ a, max a b = a
        // ========================================
        let max_def_alt_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, bvar) = bldr.fresh_local(int_const.clone());
            let le_b_a = Expr::app(Expr::app(int_le.clone(), bvar.clone()), a.clone());
            let (h_id, _h) = bldr.fresh_local(le_b_a.clone());
            let max_a_b = Expr::app(Expr::app(int_max.clone(), a.clone()), bvar.clone());
            let eq_max_a_b_a = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), int_const.clone()), max_a_b),
                a.clone(),
            );
            let e = bldr.mk_pi(h_id, BinderInfo::Default, le_b_a, eq_max_a_b_a);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, int_const.clone(), e);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        if self.get_const(&Name::from_string("Int.max_def'")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.max_def'"),
                level_params: vec![],
                type_: max_def_alt_type,
            })?;
        }

        self.int_minmax_init = true;
        Ok(())
    }

    /// Check if Int min/max functions have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_minmax_init == true`
    pub(crate) fn has_int_minmax(&self) -> bool {
        self.int_minmax_init
    }

    /// Initialize Int.abs properties
    ///
    /// Adds axiomatic properties for Int.abs (which is defined computationally in init_int_sign_abs):
    /// - `Int.abs_nonneg : ∀ a : Int, Int.le (Int.ofNat 0) (Int.abs a)` - abs is nonnegative
    /// - `Int.abs_of_nonneg : ∀ a : Int, Int.le (Int.ofNat 0) a → Eq (Int.abs a) a` - abs of nonneg is self
    /// - `Int.abs_of_neg : ∀ a : Int, Int.lt a (Int.ofNat 0) → Eq (Int.abs a) (Int.neg a)` - abs of neg is neg
    /// - `Int.abs_neg : ∀ a : Int, Eq (Int.abs (Int.neg a)) (Int.abs a)` - abs of negation is abs
    /// - `Int.abs_zero : Eq (Int.abs (Int.ofNat 0)) (Int.ofNat 0)` - abs of zero is zero
    /// - `Int.abs_mul : ∀ a b : Int, Eq (Int.abs (Int.mul a b)) (Int.mul (Int.abs a) (Int.abs b))` - abs is multiplicative
    /// - `Int.abs_add_le : ∀ a b : Int, Int.le (Int.abs (Int.add a b)) (Int.add (Int.abs a) (Int.abs b))` - triangle ineq
    /// - `Int.abs_sub_le : ∀ a b : Int, Int.le (Int.abs (Int.sub a b)) (Int.add (Int.abs a) (Int.abs b))` - triangle for sub
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_abs_props_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_abs_props(&mut self) -> Result<(), EnvError> {
        if self.int_abs_props_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_int_sign_abs()?; // Provides Int.abs
        self.init_int_ord()?; // Provides Int.le, Int.lt
        self.init_int_arith()?; // Provides Int.neg, Int.mul, Int.add, Int.sub
        self.init_eq()?; // Provides Eq

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_le = Expr::const_(Name::from_string("Int.le"), vec![]);
        let int_lt = Expr::const_(Name::from_string("Int.lt"), vec![]);
        let int_abs = Expr::const_(Name::from_string("Int.abs"), vec![]);
        let int_neg = Expr::const_(Name::from_string("Int.neg"), vec![]);
        let int_mul = Expr::const_(Name::from_string("Int.mul"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_sub = Expr::const_(Name::from_string("Int.sub"), vec![]);
        let int_of_nat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let int_zero = Expr::app(int_of_nat.clone(), nat_zero);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // Constructive Int.add_zero dependency for the `Int.abs_nonneg` proof
        // term below (mirrors `algebra_int_mul_nonneg_proof.rs`).
        self.register_int_add_zero_proof()?;

        // ELIMINATION: `Int.abs_of_nonneg` / `Int.abs_of_neg` (register_int_abs_cond)
        // and `Int.abs_neg` (register_int_abs_neg_proof) are now kernel-checked
        // Constructive Theorems. Registered here first; the corresponding
        // `Declaration::Axiom` blocks below are guarded by `get_const` and skip.
        self.register_int_abs_cond()?;
        self.register_int_abs_neg_proof()?;
        // ELIMINATION: `Int.abs_mul`, and `Int.abs_add_le` + `Int.dist_triangle`
        // (the latter via register_int_abs_add_le, which also sets up the
        // reducible `Int.dist`) are now Constructive Theorems; their axiom blocks
        // (here and in init_int_dist) are guarded and skip.
        self.register_int_abs_mul_proof()?;
        self.register_int_abs_add_le()?;
        self.register_int_abs_sub_le()?;

        // Cached constants for the genuine `Int.abs_zero` / `Int.abs_nonneg`
        // proof terms (these two are PROVEN, not admitted — see below).
        let type1 = Level::succ(Level::zero());
        let int_nonneg = Expr::const_(Name::from_string("Int.NonNeg"), vec![]);
        let int_nonneg_mk = Expr::const_(Name::from_string("Int.NonNeg.mk"), vec![]);
        let int_nat_abs = Expr::const_(Name::from_string("Int.natAbs"), vec![]);
        let int_add_zero = Expr::const_(Name::from_string("Int.add_zero"), vec![]);
        let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![type1.clone()]);
        let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![type1.clone()]);
        let eq_symm = Expr::const_(Name::from_string("Eq.symm"), vec![type1]);

        // ========================================
        // Int.abs_nonneg : ∀ a : Int, Int.le (Int.ofNat 0) (Int.abs a)
        // abs is always nonnegative
        // ========================================
        let abs_nonneg_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let body = Expr::app(
                Expr::app(int_le.clone(), int_zero.clone()),
                Expr::app(int_abs.clone(), a.clone()),
            );
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), body);
            bldr.finish(e)
        };

        // PROVEN (no longer admitted): `Int.abs a ≡ Int.ofNat (Int.natAbs a)` is
        // ALWAYS an `ofNat _`, so `@Int.NonNeg.mk (Int.natAbs a)` inhabits
        // `Int.NonNeg (Int.abs a)`. The goal `Int.le 0 (Int.abs a)` delta-reduces
        // to `Int.NonNeg (Int.sub (Int.abs a) 0) ≡ Int.NonNeg (Int.add (Int.abs a)
        // 0)` (since `Int.neg (ofNat 0) ≡ ofNat 0`), reached by transporting the
        // witness across `Eq.symm (Int.add_zero (Int.abs a))` via `@Eq.subst.{1}`.
        // Constructive (delegates only to `Int.add_zero` + Eq primitives).
        let abs_nonneg_value = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let abs_a = Expr::app(int_abs.clone(), a.clone());
            // motive := fun z : Int => Int.NonNeg z
            let motive = {
                let mut ch = EnvDeclBuilder::child_of(&bldr);
                let (z_id, z) = ch.fresh_local(int_const.clone());
                let body = Expr::app(int_nonneg.clone(), z);
                let r = ch.mk_lam(z_id, BinderInfo::Default, int_const.clone(), body);
                ch.finish_child(r)
            };
            // witness : Int.NonNeg (Int.abs a)  (≡ NonNeg (ofNat (natAbs a)))
            let witness = Expr::app(
                int_nonneg_mk.clone(),
                Expr::app(int_nat_abs.clone(), a.clone()),
            );
            // add_abs_zero := Int.add (Int.abs a) (Int.ofNat 0)
            let add_abs_zero =
                Expr::app(Expr::app(int_add.clone(), abs_a.clone()), int_zero.clone());
            // h : Int.add (Int.abs a) 0 = Int.abs a ; symm : Int.abs a = add (Int.abs a) 0
            let h_add_zero = Expr::app(int_add_zero.clone(), abs_a.clone());
            let h_symm = Expr::apps(
                eq_symm.clone(),
                [
                    int_const.clone(),
                    add_abs_zero.clone(),
                    abs_a.clone(),
                    h_add_zero,
                ],
            );
            // @Eq.subst Int motive (abs a) (add (abs a) 0) h_symm witness : NonNeg (add (abs a) 0)
            let body = Expr::apps(
                eq_subst.clone(),
                [
                    int_const.clone(),
                    motive,
                    abs_a,
                    add_abs_zero,
                    h_symm,
                    witness,
                ],
            );
            let e = bldr.mk_lam(a_id, BinderInfo::Default, int_const.clone(), body);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Int.abs_nonneg"),
            level_params: vec![],
            type_: abs_nonneg_type,
            value: abs_nonneg_value,
        })?;

        // ========================================
        // Int.abs_of_nonneg : ∀ a : Int, Int.le (Int.ofNat 0) a → Eq (Int.abs a) a
        // When a ≥ 0, abs a = a
        // ========================================
        let abs_of_nonneg_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let le_zero_a = Expr::app(Expr::app(int_le.clone(), int_zero.clone()), a.clone());
            let (h_id, _h) = bldr.fresh_local(le_zero_a.clone());
            let eq_abs_a_a = Expr::app(
                Expr::app(
                    Expr::app(eq_const.clone(), int_const.clone()),
                    Expr::app(int_abs.clone(), a.clone()),
                ),
                a.clone(),
            );
            let e = bldr.mk_pi(h_id, BinderInfo::Default, le_zero_a, eq_abs_a_a);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        if self
            .get_const(&Name::from_string("Int.abs_of_nonneg"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.abs_of_nonneg"),
                level_params: vec![],
                type_: abs_of_nonneg_type,
            })?;
        }

        // ========================================
        // Int.abs_of_neg : ∀ a : Int, Int.lt a (Int.ofNat 0) → Eq (Int.abs a) (Int.neg a)
        // When a < 0, abs a = -a
        // ========================================
        let abs_of_neg_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let lt_a_zero = Expr::app(Expr::app(int_lt.clone(), a.clone()), int_zero.clone());
            let (h_id, _h) = bldr.fresh_local(lt_a_zero.clone());
            let eq_abs_a_neg_a = Expr::app(
                Expr::app(
                    Expr::app(eq_const.clone(), int_const.clone()),
                    Expr::app(int_abs.clone(), a.clone()),
                ),
                Expr::app(int_neg.clone(), a.clone()),
            );
            let e = bldr.mk_pi(h_id, BinderInfo::Default, lt_a_zero, eq_abs_a_neg_a);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        if self
            .get_const(&Name::from_string("Int.abs_of_neg"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.abs_of_neg"),
                level_params: vec![],
                type_: abs_of_neg_type,
            })?;
        }

        // ========================================
        // Int.abs_neg : ∀ a : Int, Eq (Int.abs (Int.neg a)) (Int.abs a)
        // abs of negation equals abs: |-a| = |a|
        // ========================================
        let abs_neg_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let body = Expr::app(
                Expr::app(
                    Expr::app(eq_const.clone(), int_const.clone()),
                    Expr::app(int_abs.clone(), Expr::app(int_neg.clone(), a.clone())),
                ),
                Expr::app(int_abs.clone(), a.clone()),
            );
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), body);
            bldr.finish(e)
        };

        if self.get_const(&Name::from_string("Int.abs_neg")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.abs_neg"),
                level_params: vec![],
                type_: abs_neg_type,
            })?;
        }

        // ========================================
        // Int.abs_zero : Eq (Int.abs (Int.ofNat 0)) (Int.ofNat 0)
        // abs of zero is zero
        // ========================================
        let abs_zero_type = Expr::app(
            Expr::app(
                Expr::app(eq_const.clone(), int_const.clone()),
                Expr::app(int_abs.clone(), int_zero.clone()),
            ),
            int_zero.clone(),
        );

        // PROVEN (no longer admitted): `Int.abs (ofNat 0) ≡ Int.ofNat (Int.natAbs
        // (ofNat 0)) ≡ Int.ofNat 0 ≡ Int.zero` definitionally, so the goal
        // `Eq Int (Int.abs Int.zero) Int.zero` is closed by `@Eq.refl.{1} Int
        // Int.zero` (both sides are def-eq). Constructive.
        let abs_zero_value = Expr::apps(eq_refl.clone(), [int_const.clone(), int_zero.clone()]);

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Int.abs_zero"),
            level_params: vec![],
            type_: abs_zero_type,
            value: abs_zero_value,
        })?;

        // ========================================
        // Int.abs_mul : ∀ a b : Int, Eq (Int.abs (Int.mul a b)) (Int.mul (Int.abs a) (Int.abs b))
        // abs is multiplicative: |a * b| = |a| * |b|
        // ========================================
        let abs_mul_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, bvar) = bldr.fresh_local(int_const.clone());
            let abs_mul = Expr::app(
                int_abs.clone(),
                Expr::app(Expr::app(int_mul.clone(), a.clone()), bvar.clone()),
            );
            let mul_abs = Expr::app(
                Expr::app(int_mul.clone(), Expr::app(int_abs.clone(), a.clone())),
                Expr::app(int_abs.clone(), bvar.clone()),
            );
            let body = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), int_const.clone()), abs_mul),
                mul_abs,
            );
            let e = bldr.mk_pi(b_id, BinderInfo::Default, int_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        if self.get_const(&Name::from_string("Int.abs_mul")).is_none() {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.abs_mul"),
                level_params: vec![],
                type_: abs_mul_type,
            })?;
        }

        // ========================================
        // Int.abs_add_le : ∀ a b : Int, Int.le (Int.abs (Int.add a b)) (Int.add (Int.abs a) (Int.abs b))
        // Triangle inequality: |a + b| ≤ |a| + |b|
        // ========================================
        let abs_add_le_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, bvar) = bldr.fresh_local(int_const.clone());
            let lhs = Expr::app(
                int_abs.clone(),
                Expr::app(Expr::app(int_add.clone(), a.clone()), bvar.clone()),
            );
            let rhs = Expr::app(
                Expr::app(int_add.clone(), Expr::app(int_abs.clone(), a.clone())),
                Expr::app(int_abs.clone(), bvar.clone()),
            );
            let body = Expr::app(Expr::app(int_le.clone(), lhs), rhs);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, int_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        if self
            .get_const(&Name::from_string("Int.abs_add_le"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.abs_add_le"),
                level_params: vec![],
                type_: abs_add_le_type,
            })?;
        }

        // ========================================
        // Int.abs_sub_le : ∀ a b : Int, Int.le (Int.abs (Int.sub a b)) (Int.add (Int.abs a) (Int.abs b))
        // Triangle inequality for subtraction: |a - b| ≤ |a| + |b|
        // ========================================
        let abs_sub_le_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, bvar) = bldr.fresh_local(int_const.clone());
            let lhs = Expr::app(
                int_abs.clone(),
                Expr::app(Expr::app(int_sub.clone(), a.clone()), bvar.clone()),
            );
            let rhs = Expr::app(
                Expr::app(int_add.clone(), Expr::app(int_abs.clone(), a.clone())),
                Expr::app(int_abs.clone(), bvar.clone()),
            );
            let body = Expr::app(Expr::app(int_le.clone(), lhs), rhs);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, int_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        if self
            .get_const(&Name::from_string("Int.abs_sub_le"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.abs_sub_le"),
                level_params: vec![],
                type_: abs_sub_le_type,
            })?;
        }

        self.int_abs_props_init = true;
        Ok(())
    }

    /// Check if Int.abs properties have been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_abs_props_init == true`
    pub(crate) fn has_int_abs_props(&self) -> bool {
        self.int_abs_props_init
    }
}
