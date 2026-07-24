// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Distance metrics for Rat, Int, and Nat
//!
//! Contains:
//! - init_rat_dist: Rat.dist metric space properties
//! - init_int_dist: Int.dist metric space properties
//! - init_nat_dist: Nat.dist metric space properties

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Rat.dist (distance/metric) function and properties
    ///
    /// Adds:
    /// - `Rat.dist : Rat → Rat → Rat` (definition) - distance d(a,b) = |a - b|
    /// - `Rat.dist_self : ∀ a : Rat, Eq (Rat.dist a a) Rat.zero` - d(a,a) = 0
    /// - `Rat.dist_comm : ∀ a b : Rat, Eq (Rat.dist a b) (Rat.dist b a)` - symmetry
    /// - `Rat.dist_nonneg : ∀ a b : Rat, Rat.le Rat.zero (Rat.dist a b)` - non-negativity
    /// - `Rat.dist_triangle : ∀ a b c : Rat, Rat.le (Rat.dist a c) (Rat.add (Rat.dist a b) (Rat.dist b c))`
    /// - `Rat.dist_eq_abs_sub : ∀ a b : Rat, Eq (Rat.dist a b) (Rat.abs (Rat.sub a b))` - definition
    /// - `Rat.abs_sub_abs_le_dist : ∀ a b : Rat, Rat.le (Rat.abs (Rat.sub (Rat.abs a) (Rat.abs b))) (Rat.dist a b)` - reverse triangle
    ///
    /// Note: dist is defined as |a - b| and satisfies metric space axioms.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.rat_dist_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_rat_dist(&mut self) -> Result<(), EnvError> {
        if self.rat_dist_init {
            return Ok(());
        }

        // Initialize dependencies
        // Note: init_rat_abs already calls init_rat_arith and init_rat_ord
        self.init_rat_abs()?; // Provides Rat.abs, Rat.le, Rat.sub, Rat.add, Rat.neg
        self.init_eq()?; // Provides Eq

        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let rat_abs = Expr::const_(Name::from_string("Rat.abs"), vec![]);
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let rat_sub = Expr::const_(Name::from_string("Rat.sub"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // ========================================
        // Rat.dist : Rat → Rat → Rat
        // dist a b := |a - b|
        // ========================================
        let rat_dist_type = Expr::pi(
            BinderInfo::Default,
            rat_const.clone(),
            Expr::pi(BinderInfo::Default, rat_const.clone(), rat_const.clone()),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Rat.dist"),
            level_params: vec![],
            type_: rat_dist_type,
        })?;

        let rat_dist = Expr::const_(Name::from_string("Rat.dist"), vec![]);

        // ========================================
        // Rat.dist_self : ∀ a : Rat, Eq (Rat.dist a a) Rat.zero
        // d(a, a) = 0
        // ========================================
        let dist_self_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let lhs = Expr::app(Expr::app(rat_dist.clone(), a.clone()), a.clone());
            let body = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), rat_const.clone()), lhs),
                rat_zero.clone(),
            );
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), body);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Rat.dist_self"),
            level_params: vec![],
            type_: dist_self_type,
        })?;

        // ========================================
        // Rat.dist_comm : ∀ a b : Rat, Eq (Rat.dist a b) (Rat.dist b a)
        // Symmetry: d(a, b) = d(b, a)
        // ========================================
        let dist_comm_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let (b_id, b) = bldr.fresh_local(rat_const.clone());
            let lhs = Expr::app(Expr::app(rat_dist.clone(), a.clone()), b.clone());
            let rhs = Expr::app(Expr::app(rat_dist.clone(), b.clone()), a.clone());
            let body = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), rat_const.clone()), lhs),
                rhs,
            );
            let e = bldr.mk_pi(b_id, BinderInfo::Default, rat_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Rat.dist_comm"),
            level_params: vec![],
            type_: dist_comm_type,
        })?;

        // ========================================
        // Rat.dist_nonneg : ∀ a b : Rat, Rat.le Rat.zero (Rat.dist a b)
        // Non-negativity: d(a, b) ≥ 0
        // ========================================
        let dist_nonneg_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let (b_id, b) = bldr.fresh_local(rat_const.clone());
            let body = Expr::app(
                Expr::app(rat_le.clone(), rat_zero.clone()),
                Expr::app(Expr::app(rat_dist.clone(), a.clone()), b.clone()),
            );
            let e = bldr.mk_pi(b_id, BinderInfo::Default, rat_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Rat.dist_nonneg"),
            level_params: vec![],
            type_: dist_nonneg_type,
        })?;

        // ========================================
        // Rat.dist_triangle : ∀ a b c : Rat, Rat.le (Rat.dist a c) (Rat.add (Rat.dist a b) (Rat.dist b c))
        // Triangle inequality: d(a, c) ≤ d(a, b) + d(b, c)
        // ========================================
        let dist_triangle_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let (b_id, b) = bldr.fresh_local(rat_const.clone());
            let (c_id, c) = bldr.fresh_local(rat_const.clone());
            let lhs = Expr::app(Expr::app(rat_dist.clone(), a.clone()), c.clone());
            let rhs = Expr::app(
                Expr::app(
                    rat_add.clone(),
                    Expr::app(Expr::app(rat_dist.clone(), a.clone()), b.clone()),
                ),
                Expr::app(Expr::app(rat_dist.clone(), b.clone()), c.clone()),
            );
            let body = Expr::app(Expr::app(rat_le.clone(), lhs), rhs);
            let e = bldr.mk_pi(c_id, BinderInfo::Default, rat_const.clone(), body);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, rat_const.clone(), e);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Rat.dist_triangle"),
            level_params: vec![],
            type_: dist_triangle_type,
        })?;

        // ========================================
        // Rat.dist_eq_abs_sub : ∀ a b : Rat, Eq (Rat.dist a b) (Rat.abs (Rat.sub a b))
        // Definition: dist(a, b) = |a - b|
        // ========================================
        let dist_eq_abs_sub_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let (b_id, b) = bldr.fresh_local(rat_const.clone());
            let lhs = Expr::app(Expr::app(rat_dist.clone(), a.clone()), b.clone());
            let rhs = Expr::app(
                rat_abs.clone(),
                Expr::app(Expr::app(rat_sub.clone(), a.clone()), b.clone()),
            );
            let body = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), rat_const.clone()), lhs),
                rhs,
            );
            let e = bldr.mk_pi(b_id, BinderInfo::Default, rat_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Rat.dist_eq_abs_sub"),
            level_params: vec![],
            type_: dist_eq_abs_sub_type,
        })?;

        // ========================================
        // Rat.abs_sub_abs_le_dist : ∀ a b : Rat, Rat.le (Rat.abs (Rat.sub (Rat.abs a) (Rat.abs b))) (Rat.dist a b)
        // Reverse triangle inequality: ||a| - |b|| ≤ d(a, b) = |a - b|
        // ========================================
        let abs_sub_abs_le_dist_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(rat_const.clone());
            let (b_id, b) = bldr.fresh_local(rat_const.clone());
            let lhs = Expr::app(
                rat_abs.clone(),
                Expr::app(
                    Expr::app(rat_sub.clone(), Expr::app(rat_abs.clone(), a.clone())),
                    Expr::app(rat_abs.clone(), b.clone()),
                ),
            );
            let rhs = Expr::app(Expr::app(rat_dist.clone(), a.clone()), b.clone());
            let body = Expr::app(Expr::app(rat_le.clone(), lhs), rhs);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, rat_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, rat_const.clone(), e);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Rat.abs_sub_abs_le_dist"),
            level_params: vec![],
            type_: abs_sub_abs_le_dist_type,
        })?;

        self.rat_dist_init = true;
        Ok(())
    }

    /// Check if Rat.dist has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.rat_dist_init == true`
    pub(crate) fn has_rat_dist(&self) -> bool {
        self.rat_dist_init
    }

    /// Initialize Int.dist (distance/metric) function and properties
    ///
    /// Adds:
    /// - `Int.dist : Int → Int → Int` (definition) - distance d(a,b) = |a - b|
    /// - `Int.dist_self : ∀ a : Int, Eq (Int.dist a a) (Int.ofNat 0)` - d(a,a) = 0
    /// - `Int.dist_comm : ∀ a b : Int, Eq (Int.dist a b) (Int.dist b a)` - symmetry
    /// - `Int.dist_nonneg : ∀ a b : Int, Int.le (Int.ofNat 0) (Int.dist a b)` - non-negativity
    /// - `Int.dist_triangle : ∀ a b c : Int, Int.le (Int.dist a c) (Int.add (Int.dist a b) (Int.dist b c))`
    /// - `Int.dist_eq_abs_sub : ∀ a b : Int, Eq (Int.dist a b) (Int.abs (Int.sub a b))` - definition
    /// - `Int.abs_sub_abs_le_dist : ∀ a b : Int, Int.le (Int.abs (Int.sub (Int.abs a) (Int.abs b))) (Int.dist a b)` - reverse triangle
    ///
    /// Note: dist is defined as |a - b| and satisfies metric space axioms.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_dist_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_dist(&mut self) -> Result<(), EnvError> {
        if self.int_dist_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_int_abs_props()?; // Provides Int.abs and abs properties
        self.init_int_arith()?; // Provides Int.add, Int.sub
        self.init_int_ord()?; // Provides Int.le
        self.init_eq()?; // Provides Eq

        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let int_zero = Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        );
        let int_le = Expr::const_(Name::from_string("Int.le"), vec![]);
        let int_abs = Expr::const_(Name::from_string("Int.abs"), vec![]);
        let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
        let int_sub = Expr::const_(Name::from_string("Int.sub"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let eq_refl = Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        );
        // `Int.abs_nonneg` is a constructive Theorem (algebra_abs_int.rs); used by
        // the genuine `Int.dist_nonneg` proof below.
        let int_abs_nonneg = Expr::const_(Name::from_string("Int.abs_nonneg"), vec![]);

        // ========================================
        // Int.dist : Int → Int → Int
        // dist a b := Int.abs (Int.sub a b)   (|a - b|)
        // ========================================
        // PROVEN (no longer admitted): `Int.dist` was an opaque `Declaration::Axiom`
        // even though it has a perfectly computable body. It is now a reducible
        // `Declaration::Definition` `λ a b => Int.abs (Int.sub a b)`, which (a)
        // removes the axiom and (b) makes `Int.dist_eq_abs_sub` true by `Eq.refl`
        // and `Int.dist_nonneg` follow from `Int.abs_nonneg`.
        let int_dist_type = Expr::pi(
            BinderInfo::Default,
            int_const.clone(),
            Expr::pi(BinderInfo::Default, int_const.clone(), int_const.clone()),
        );

        let int_dist_value = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, b) = bldr.fresh_local(int_const.clone());
            let body = Expr::app(
                int_abs.clone(),
                Expr::app(Expr::app(int_sub.clone(), a.clone()), b.clone()),
            );
            let e = bldr.mk_lam(b_id, BinderInfo::Default, int_const.clone(), body);
            let e = bldr.mk_lam(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        // Guarded: `Int.dist` may already be registered (identically) by
        // `register_int_abs_add_le`'s `ensure_int_dist_def_local` running earlier
        // via `init_int_abs_props`.
        if self.get_const(&Name::from_string("Int.dist")).is_none() {
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Int.dist"),
                level_params: vec![],
                type_: int_dist_type,
                value: int_dist_value,
                is_reducible: true,
            })?;
        }

        let int_dist = Expr::const_(Name::from_string("Int.dist"), vec![]);

        // ELIMINATION: `Int.dist_self` is now a kernel-checked Constructive
        // Theorem (`algebra_int_dist_self_proof.rs`). Registered AFTER `Int.dist`
        // is defined above (its internal `register_int_dist_def` then skips via
        // `get_const`); the `Int.dist_self` axiom block below is guarded and skips.
        self.register_int_dist_self_proof()?;
        // ELIMINATION: `Int.dist_comm` is now a kernel-checked Constructive
        // Theorem (`algebra_int_dist_comm_proof.rs`, via `Int.neg_sub` +
        // `Int.abs_neg`); the axiom block below is guarded and skips.
        self.register_int_dist_comm()?;
        // ELIMINATION: `Int.abs_sub_abs_le_dist` (reverse triangle inequality)
        // is now a Constructive Theorem; the axiom block below is guarded.
        self.register_int_abs_sub_abs_le_dist()?;

        // ========================================
        // Int.dist_self : ∀ a : Int, Eq (Int.dist a a) (Int.ofNat 0)
        // d(a, a) = 0
        // ========================================
        let dist_self_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let lhs = Expr::app(Expr::app(int_dist.clone(), a.clone()), a.clone());
            let body = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), int_const.clone()), lhs),
                int_zero.clone(),
            );
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), body);
            bldr.finish(e)
        };

        if self
            .get_const(&Name::from_string("Int.dist_self"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.dist_self"),
                level_params: vec![],
                type_: dist_self_type,
            })?;
        }

        // ========================================
        // Int.dist_comm : ∀ a b : Int, Eq (Int.dist a b) (Int.dist b a)
        // Symmetry: d(a, b) = d(b, a)
        // ========================================
        let dist_comm_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, b) = bldr.fresh_local(int_const.clone());
            let lhs = Expr::app(Expr::app(int_dist.clone(), a.clone()), b.clone());
            let rhs = Expr::app(Expr::app(int_dist.clone(), b.clone()), a.clone());
            let body = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), int_const.clone()), lhs),
                rhs,
            );
            let e = bldr.mk_pi(b_id, BinderInfo::Default, int_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        if self
            .get_const(&Name::from_string("Int.dist_comm"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.dist_comm"),
                level_params: vec![],
                type_: dist_comm_type,
            })?;
        }

        // ========================================
        // Int.dist_nonneg : ∀ a b : Int, Int.le (Int.ofNat 0) (Int.dist a b)
        // Non-negativity: d(a, b) ≥ 0
        // ========================================
        let dist_nonneg_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, b) = bldr.fresh_local(int_const.clone());
            let body = Expr::app(
                Expr::app(int_le.clone(), int_zero.clone()),
                Expr::app(Expr::app(int_dist.clone(), a.clone()), b.clone()),
            );
            let e = bldr.mk_pi(b_id, BinderInfo::Default, int_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        // PROVEN: `Int.dist a b ≡ Int.abs (Int.sub a b)` (reducible), so the goal
        // `Int.le 0 (Int.dist a b)` is `Int.le 0 (Int.abs (Int.sub a b))`, which is
        // exactly `Int.abs_nonneg (Int.sub a b)`. Constructive.
        let dist_nonneg_value = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, b) = bldr.fresh_local(int_const.clone());
            let sub_ab = Expr::app(Expr::app(int_sub.clone(), a.clone()), b.clone());
            let body = Expr::app(int_abs_nonneg.clone(), sub_ab);
            let e = bldr.mk_lam(b_id, BinderInfo::Default, int_const.clone(), body);
            let e = bldr.mk_lam(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Int.dist_nonneg"),
            level_params: vec![],
            type_: dist_nonneg_type,
            value: dist_nonneg_value,
        })?;

        // ========================================
        // Int.dist_triangle : ∀ a b c : Int, Int.le (Int.dist a c) (Int.add (Int.dist a b) (Int.dist b c))
        // Triangle inequality: d(a, c) ≤ d(a, b) + d(b, c)
        // ========================================
        let dist_triangle_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, b) = bldr.fresh_local(int_const.clone());
            let (c_id, c) = bldr.fresh_local(int_const.clone());
            let lhs = Expr::app(Expr::app(int_dist.clone(), a.clone()), c.clone());
            let rhs = Expr::app(
                Expr::app(
                    int_add.clone(),
                    Expr::app(Expr::app(int_dist.clone(), a.clone()), b.clone()),
                ),
                Expr::app(Expr::app(int_dist.clone(), b.clone()), c.clone()),
            );
            let body = Expr::app(Expr::app(int_le.clone(), lhs), rhs);
            let e = bldr.mk_pi(c_id, BinderInfo::Default, int_const.clone(), body);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, int_const.clone(), e);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        if self
            .get_const(&Name::from_string("Int.dist_triangle"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.dist_triangle"),
                level_params: vec![],
                type_: dist_triangle_type,
            })?;
        }

        // ========================================
        // Int.dist_eq_abs_sub : ∀ a b : Int, Eq (Int.dist a b) (Int.abs (Int.sub a b))
        // Definition: dist(a, b) = |a - b|
        // ========================================
        let dist_eq_abs_sub_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, b) = bldr.fresh_local(int_const.clone());
            let lhs = Expr::app(Expr::app(int_dist.clone(), a.clone()), b.clone());
            let rhs = Expr::app(
                int_abs.clone(),
                Expr::app(Expr::app(int_sub.clone(), a.clone()), b.clone()),
            );
            let body = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), int_const.clone()), lhs),
                rhs,
            );
            let e = bldr.mk_pi(b_id, BinderInfo::Default, int_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        // PROVEN: with `Int.dist` now reducible to `Int.abs (Int.sub a b)`, the
        // goal `Eq Int (Int.dist a b) (Int.abs (Int.sub a b))` is closed by
        // `@Eq.refl.{1} Int (Int.abs (Int.sub a b))` (both sides def-eq).
        let dist_eq_abs_sub_value = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, b) = bldr.fresh_local(int_const.clone());
            let abs_sub = Expr::app(
                int_abs.clone(),
                Expr::app(Expr::app(int_sub.clone(), a.clone()), b.clone()),
            );
            let body = Expr::apps(eq_refl.clone(), [int_const.clone(), abs_sub]);
            let e = bldr.mk_lam(b_id, BinderInfo::Default, int_const.clone(), body);
            let e = bldr.mk_lam(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name: Name::from_string("Int.dist_eq_abs_sub"),
            level_params: vec![],
            type_: dist_eq_abs_sub_type,
            value: dist_eq_abs_sub_value,
        })?;

        // ========================================
        // Int.abs_sub_abs_le_dist : ∀ a b : Int, Int.le (Int.abs (Int.sub (Int.abs a) (Int.abs b))) (Int.dist a b)
        // Reverse triangle inequality: ||a| - |b|| ≤ d(a, b) = |a - b|
        // ========================================
        let abs_sub_abs_le_dist_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(int_const.clone());
            let (b_id, b) = bldr.fresh_local(int_const.clone());
            let lhs = Expr::app(
                int_abs.clone(),
                Expr::app(
                    Expr::app(int_sub.clone(), Expr::app(int_abs.clone(), a.clone())),
                    Expr::app(int_abs.clone(), b.clone()),
                ),
            );
            let rhs = Expr::app(Expr::app(int_dist.clone(), a.clone()), b.clone());
            let body = Expr::app(Expr::app(int_le.clone(), lhs), rhs);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, int_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, int_const.clone(), e);
            bldr.finish(e)
        };

        if self
            .get_const(&Name::from_string("Int.abs_sub_abs_le_dist"))
            .is_none()
        {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string("Int.abs_sub_abs_le_dist"),
                level_params: vec![],
                type_: abs_sub_abs_le_dist_type,
            })?;
        }

        self.int_dist_init = true;
        Ok(())
    }

    /// Check if Int.dist has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_dist_init == true`
    pub(crate) fn has_int_dist(&self) -> bool {
        self.int_dist_init
    }

    /// Initialize Nat.dist (distance/metric) function and properties
    ///
    /// Adds:
    /// - `Nat.dist : Nat → Nat → Nat` (definition) - distance d(a,b) = |a - b| = absDiff a b
    /// - `Nat.dist_self : ∀ a : Nat, Eq (Nat.dist a a) Nat.zero` - d(a,a) = 0
    /// - `Nat.dist_comm : ∀ a b : Nat, Eq (Nat.dist a b) (Nat.dist b a)` - symmetry
    /// - `Nat.dist_nonneg : ∀ a b : Nat, Nat.le Nat.zero (Nat.dist a b)` - non-negativity (trivially true for Nat)
    /// - `Nat.dist_triangle : ∀ a b c : Nat, Nat.le (Nat.dist a c) (Nat.add (Nat.dist a b) (Nat.dist b c))`
    /// - `Nat.dist_eq_absDiff : ∀ a b : Nat, Eq (Nat.dist a b) (Nat.absDiff a b)` - definition
    ///
    /// Note: For Nat, dist is the same as absDiff since there are no negative numbers.
    /// This provides a consistent API with Int.dist and Rat.dist for metric space abstractions.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_dist_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_dist(&mut self) -> Result<(), EnvError> {
        if self.nat_dist_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_nat_abs_diff()?; // Provides Nat.absDiff, Nat.add, Nat.le
        self.init_eq()?; // Provides Eq

        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let nat_le = Expr::const_(Name::from_string("Nat.le"), vec![]);
        let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
        let nat_abs_diff = Expr::const_(Name::from_string("Nat.absDiff"), vec![]);
        let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // ========================================
        // Nat.dist : Nat → Nat → Nat
        // dist a b := absDiff a b = |a - b|
        // ========================================
        let nat_dist_type = Expr::pi(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::pi(BinderInfo::Default, nat_const.clone(), nat_const.clone()),
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.dist"),
            level_params: vec![],
            type_: nat_dist_type,
        })?;

        let nat_dist = Expr::const_(Name::from_string("Nat.dist"), vec![]);

        // ========================================
        // Nat.dist_self : ∀ a : Nat, Eq (Nat.dist a a) Nat.zero
        // d(a, a) = 0
        // ========================================
        let dist_self_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(nat_const.clone());
            let lhs = Expr::app(Expr::app(nat_dist.clone(), a.clone()), a.clone());
            let body = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), nat_const.clone()), lhs),
                nat_zero.clone(),
            );
            let e = bldr.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), body);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.dist_self"),
            level_params: vec![],
            type_: dist_self_type,
        })?;

        // ========================================
        // Nat.dist_comm : ∀ a b : Nat, Eq (Nat.dist a b) (Nat.dist b a)
        // Symmetry: d(a, b) = d(b, a)
        // ========================================
        let dist_comm_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(nat_const.clone());
            let (b_id, b) = bldr.fresh_local(nat_const.clone());
            let lhs = Expr::app(Expr::app(nat_dist.clone(), a.clone()), b.clone());
            let rhs = Expr::app(Expr::app(nat_dist.clone(), b.clone()), a.clone());
            let body = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), nat_const.clone()), lhs),
                rhs,
            );
            let e = bldr.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.dist_comm"),
            level_params: vec![],
            type_: dist_comm_type,
        })?;

        // ========================================
        // Nat.dist_nonneg : ∀ a b : Nat, Nat.le Nat.zero (Nat.dist a b)
        // Non-negativity: d(a, b) ≥ 0 (trivially true for Nat)
        // ========================================
        let dist_nonneg_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(nat_const.clone());
            let (b_id, b) = bldr.fresh_local(nat_const.clone());
            let body = Expr::app(
                Expr::app(nat_le.clone(), nat_zero.clone()),
                Expr::app(Expr::app(nat_dist.clone(), a.clone()), b.clone()),
            );
            let e = bldr.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.dist_nonneg"),
            level_params: vec![],
            type_: dist_nonneg_type,
        })?;

        // ========================================
        // Nat.dist_triangle : ∀ a b c : Nat, Nat.le (Nat.dist a c) (Nat.add (Nat.dist a b) (Nat.dist b c))
        // Triangle inequality: d(a, c) ≤ d(a, b) + d(b, c)
        // ========================================
        let dist_triangle_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(nat_const.clone());
            let (b_id, b) = bldr.fresh_local(nat_const.clone());
            let (c_id, c) = bldr.fresh_local(nat_const.clone());
            let lhs = Expr::app(Expr::app(nat_dist.clone(), a.clone()), c.clone());
            let rhs = Expr::app(
                Expr::app(
                    nat_add.clone(),
                    Expr::app(Expr::app(nat_dist.clone(), a.clone()), b.clone()),
                ),
                Expr::app(Expr::app(nat_dist.clone(), b.clone()), c.clone()),
            );
            let body = Expr::app(Expr::app(nat_le.clone(), lhs), rhs);
            let e = bldr.mk_pi(c_id, BinderInfo::Default, nat_const.clone(), body);
            let e = bldr.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), e);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.dist_triangle"),
            level_params: vec![],
            type_: dist_triangle_type,
        })?;

        // ========================================
        // Nat.dist_eq_absDiff : ∀ a b : Nat, Eq (Nat.dist a b) (Nat.absDiff a b)
        // Definition: dist(a, b) = absDiff(a, b)
        // ========================================
        let dist_eq_abs_diff_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (a_id, a) = bldr.fresh_local(nat_const.clone());
            let (b_id, b) = bldr.fresh_local(nat_const.clone());
            let lhs = Expr::app(Expr::app(nat_dist.clone(), a.clone()), b.clone());
            let rhs = Expr::app(Expr::app(nat_abs_diff.clone(), a.clone()), b.clone());
            let body = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), nat_const.clone()), lhs),
                rhs,
            );
            let e = bldr.mk_pi(b_id, BinderInfo::Default, nat_const.clone(), body);
            let e = bldr.mk_pi(a_id, BinderInfo::Default, nat_const.clone(), e);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.dist_eq_absDiff"),
            level_params: vec![],
            type_: dist_eq_abs_diff_type,
        })?;

        // ========================================
        // Nat.dist_zero_left : ∀ n : Nat, Eq (Nat.dist Nat.zero n) n
        // dist 0 n = n
        // ========================================
        let dist_zero_left_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (n_id, n) = bldr.fresh_local(nat_const.clone());
            let lhs = Expr::app(Expr::app(nat_dist.clone(), nat_zero.clone()), n.clone());
            let body = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), nat_const.clone()), lhs),
                n.clone(),
            );
            let e = bldr.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), body);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.dist_zero_left"),
            level_params: vec![],
            type_: dist_zero_left_type,
        })?;

        // ========================================
        // Nat.dist_zero_right : ∀ n : Nat, Eq (Nat.dist n Nat.zero) n
        // dist n 0 = n
        // ========================================
        let dist_zero_right_type = {
            let mut bldr = EnvDeclBuilder::new();
            let (n_id, n) = bldr.fresh_local(nat_const.clone());
            let lhs = Expr::app(Expr::app(nat_dist.clone(), n.clone()), nat_zero.clone());
            let body = Expr::app(
                Expr::app(Expr::app(eq_const.clone(), nat_const.clone()), lhs),
                n.clone(),
            );
            let e = bldr.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), body);
            bldr.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("Nat.dist_zero_right"),
            level_params: vec![],
            type_: dist_zero_right_type,
        })?;

        self.nat_dist_init = true;
        Ok(())
    }

    /// Check if Nat.dist has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_dist_init == true`
    pub(crate) fn has_nat_dist(&self) -> bool {
        self.nat_dist_init
    }
}
