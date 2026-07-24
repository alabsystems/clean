// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core metric space initialization functions for Environment
//!
//! This module contains the MetricSpace typeclass definition and concrete
//! instances for Nat, Int, and Rat. Metric topology (balls, continuity,
//! Lipschitz, uniform continuity) is in metric_continuity.rs. Cauchy
//! sequences, completeness, and space properties are in metric_completeness.rs.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize metric space declarations (MetricSpace typeclass, dist function)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.metric_space_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_metric_space(&mut self) -> Result<(), EnvError> {
        if self.metric_space_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_rat()?; // Provides Rat type/base constants; metric only needs Rat.add/Rat.mul.
        let has_metric_rat_primitives = |env: &Environment| {
            env.get_const(&Name::from_string("Rat.add")).is_some()
                && env.get_const(&Name::from_string("Rat.mul")).is_some()
        };
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.init_rat_arith())) {
            Ok(Ok(())) => {}
            Ok(Err(err)) if !has_metric_rat_primitives(self) => return Err(err),
            Err(payload) if !has_metric_rat_primitives(self) => std::panic::resume_unwind(payload),
            _ => {}
        }
        self.init_rat_ord()?; // Provides Rat.le, instLERat
        self.init_eq()?; // Provides Eq
        self.init_le()?; // Provides LE typeclass

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1) // Type u

        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let eq_const_rat = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

        // ========================================
        // MetricSpace : Type u → Type u
        // ========================================
        let metric_space_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(), // α : Type u
            type_u.clone(), // Type u
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("MetricSpace"),
            level_params: vec![u.clone()],
            type_: metric_space_type,
        })?;

        // ========================================
        // MetricSpace.mk : {α : Type u} →
        //   (dist : α → α → Rat) →
        //   (dist_self : ∀ x : α, Eq (dist x x) Rat.zero) →
        //   (dist_comm : ∀ x y : α, Eq (dist x y) (dist y x)) →
        //   (dist_triangle : ∀ x y z : α, Rat.le (dist x z) (Rat.add (dist x y) (dist y z))) →
        //   (eq_of_dist_eq_zero : ∀ x y : α, Eq (dist x y) Rat.zero → Eq x y) →
        //   MetricSpace α
        // ========================================

        // Build MetricSpace.mk constructor type with EnvDeclBuilder
        // to avoid manual de Bruijn index arithmetic.
        let mk_type = {
            let mut b = EnvDeclBuilder::new();

            // Outer binders: {α : Type u}, (dist : α → α → Rat), ...
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let dist_type =
                Expr::arrow(alpha.clone(), Expr::arrow(alpha.clone(), rat_const.clone()));
            let (dist_id, dist) = b.fresh_local(dist_type.clone());

            // dist_self : ∀ x : α, Eq (dist x x) Rat.zero
            let dist_self_type = {
                let (x_id, x) = b.fresh_local(alpha.clone());
                let dist_x_x = Expr::app(Expr::app(dist.clone(), x.clone()), x.clone());
                let body = Expr::app(
                    Expr::app(Expr::app(eq_const_rat.clone(), rat_const.clone()), dist_x_x),
                    rat_zero.clone(),
                );
                b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), body)
            };
            let (dist_self_id, _dist_self) = b.fresh_local(dist_self_type.clone());

            // dist_comm : ∀ x y : α, Eq (dist x y) (dist y x)
            let dist_comm_type = {
                let (x_id, x) = b.fresh_local(alpha.clone());
                let (y_id, y) = b.fresh_local(alpha.clone());
                let dist_x_y = Expr::app(Expr::app(dist.clone(), x.clone()), y.clone());
                let dist_y_x = Expr::app(Expr::app(dist.clone(), y.clone()), x.clone());
                let body = Expr::app(
                    Expr::app(Expr::app(eq_const_rat.clone(), rat_const.clone()), dist_x_y),
                    dist_y_x,
                );
                let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), body);
                b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e)
            };
            let (dist_comm_id, _dist_comm) = b.fresh_local(dist_comm_type.clone());

            // dist_triangle : ∀ x y z : α, Rat.le (dist x z) (Rat.add (dist x y) (dist y z))
            let dist_triangle_type = {
                let (x_id, x) = b.fresh_local(alpha.clone());
                let (y_id, y) = b.fresh_local(alpha.clone());
                let (z_id, z) = b.fresh_local(alpha.clone());
                let dist_x_z = Expr::app(Expr::app(dist.clone(), x.clone()), z.clone());
                let dist_x_y = Expr::app(Expr::app(dist.clone(), x.clone()), y.clone());
                let dist_y_z = Expr::app(Expr::app(dist.clone(), y.clone()), z.clone());
                let body = Expr::app(
                    Expr::app(rat_le.clone(), dist_x_z),
                    Expr::app(Expr::app(rat_add.clone(), dist_x_y), dist_y_z),
                );
                let e = b.mk_pi(z_id, BinderInfo::Default, alpha.clone(), body);
                let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), e);
                b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e)
            };
            let (dist_triangle_id, _dist_triangle) = b.fresh_local(dist_triangle_type.clone());

            // eq_of_dist_eq_zero : ∀ x y : α, Eq (dist x y) Rat.zero → Eq x y
            let eq_of_dist_type = {
                let (x_id, x) = b.fresh_local(alpha.clone());
                let (y_id, y) = b.fresh_local(alpha.clone());
                let dist_x_y = Expr::app(Expr::app(dist.clone(), x.clone()), y.clone());
                let hypothesis = Expr::app(
                    Expr::app(Expr::app(eq_const_rat.clone(), rat_const.clone()), dist_x_y),
                    rat_zero.clone(),
                );
                let (h_id, _h) = b.fresh_local(hypothesis.clone());
                // Eq.{u+1} because α : Type u = Sort(u+1)
                let conclusion = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Eq"),
                                vec![Level::succ(u_level.clone())],
                            ),
                            alpha.clone(),
                        ),
                        x.clone(),
                    ),
                    y.clone(),
                );
                let e = b.mk_pi(h_id, BinderInfo::Default, hypothesis, conclusion);
                let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), e);
                b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e)
            };
            let (eq_of_dist_id, _eq_of_dist) = b.fresh_local(eq_of_dist_type.clone());

            // Result: MetricSpace α
            let result = Expr::app(
                Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]),
                alpha.clone(),
            );

            // Close binders inside-out
            let e = b.mk_pi(eq_of_dist_id, BinderInfo::Default, eq_of_dist_type, result);
            let e = b.mk_pi(dist_triangle_id, BinderInfo::Default, dist_triangle_type, e);
            let e = b.mk_pi(dist_comm_id, BinderInfo::Default, dist_comm_type, e);
            let e = b.mk_pi(dist_self_id, BinderInfo::Default, dist_self_type, e);
            let e = b.mk_pi(dist_id, BinderInfo::Default, dist_type, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("MetricSpace.mk"),
            level_params: vec![u.clone()],
            type_: mk_type,
        })?;

        // ========================================
        // Projections built with EnvDeclBuilder
        // ========================================

        // Helper: MetricSpace.dist {α} inst x y
        let ms_dist = |alpha: &Expr, inst: &Expr, x: &Expr, y: &Expr| {
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("MetricSpace.dist"),
                                vec![u_level.clone()],
                            ),
                            alpha.clone(),
                        ),
                        inst.clone(),
                    ),
                    x.clone(),
                ),
                y.clone(),
            )
        };

        // Projection: MetricSpace.dist
        // {α : Type u} → [inst : MetricSpace α] → α → α → Rat
        let dist_proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(
                Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, _inst) = b.fresh_local(ms_alpha.clone());
            let (x_id, _x) = b.fresh_local(alpha.clone());
            let (y_id, _y) = b.fresh_local(alpha.clone());

            let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), rat_const.clone());
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ms_alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("MetricSpace.dist"),
            level_params: vec![u.clone()],
            type_: dist_proj_type,
        })?;

        // Projection: MetricSpace.dist_self
        // {α : Type u} → [inst : MetricSpace α] → ∀ x : α, Eq (dist x x) Rat.zero
        let dist_self_proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(
                Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, inst) = b.fresh_local(ms_alpha.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());

            let dist_x_x = ms_dist(&alpha, &inst, &x, &x);
            let body = Expr::app(
                Expr::app(Expr::app(eq_const_rat.clone(), rat_const.clone()), dist_x_x),
                rat_zero.clone(),
            );

            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ms_alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("MetricSpace.dist_self"),
            level_params: vec![u.clone()],
            type_: dist_self_proj_type,
        })?;

        // Projection: MetricSpace.dist_comm
        // {α : Type u} → [inst : MetricSpace α] → ∀ x y : α, Eq (dist x y) (dist y x)
        let dist_comm_proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(
                Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, inst) = b.fresh_local(ms_alpha.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let (y_id, y) = b.fresh_local(alpha.clone());

            let dist_x_y = ms_dist(&alpha, &inst, &x, &y);
            let dist_y_x = ms_dist(&alpha, &inst, &y, &x);
            let body = Expr::app(
                Expr::app(Expr::app(eq_const_rat.clone(), rat_const.clone()), dist_x_y),
                dist_y_x,
            );

            let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ms_alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("MetricSpace.dist_comm"),
            level_params: vec![u.clone()],
            type_: dist_comm_proj_type,
        })?;

        // Projection: MetricSpace.dist_triangle
        // {α : Type u} → [inst : MetricSpace α] → ∀ x y z : α,
        //   Rat.le (dist x z) (Rat.add (dist x y) (dist y z))
        let dist_triangle_proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(
                Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, inst) = b.fresh_local(ms_alpha.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let (y_id, y) = b.fresh_local(alpha.clone());
            let (z_id, z) = b.fresh_local(alpha.clone());

            let dist_x_z = ms_dist(&alpha, &inst, &x, &z);
            let dist_x_y = ms_dist(&alpha, &inst, &x, &y);
            let dist_y_z = ms_dist(&alpha, &inst, &y, &z);
            let body = Expr::app(
                Expr::app(rat_le.clone(), dist_x_z),
                Expr::app(Expr::app(rat_add.clone(), dist_x_y), dist_y_z),
            );

            let e = b.mk_pi(z_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ms_alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("MetricSpace.dist_triangle"),
            level_params: vec![u.clone()],
            type_: dist_triangle_proj_type,
        })?;

        // Projection: MetricSpace.eq_of_dist_eq_zero
        // {α : Type u} → [inst : MetricSpace α] → ∀ x y : α,
        //   Eq (dist x y) Rat.zero → Eq x y
        let eq_of_dist_proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ms_alpha = Expr::app(
                Expr::const_(Name::from_string("MetricSpace"), vec![u_level.clone()]),
                alpha.clone(),
            );
            let (inst_id, inst) = b.fresh_local(ms_alpha.clone());
            let (x_id, x) = b.fresh_local(alpha.clone());
            let (y_id, y) = b.fresh_local(alpha.clone());

            let dist_x_y = ms_dist(&alpha, &inst, &x, &y);
            let hypothesis = Expr::app(
                Expr::app(Expr::app(eq_const_rat.clone(), rat_const.clone()), dist_x_y),
                rat_zero.clone(),
            );
            let (h_id, _h) = b.fresh_local(hypothesis.clone());

            // Eq.{u+1} because α : Type u = Sort(u+1)
            let conclusion = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]),
                        alpha.clone(),
                    ),
                    x.clone(),
                ),
                y.clone(),
            );

            let e = b.mk_pi(h_id, BinderInfo::Default, hypothesis, conclusion);
            let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ms_alpha.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("MetricSpace.eq_of_dist_eq_zero"),
            level_params: vec![u.clone()],
            type_: eq_of_dist_proj_type,
        })?;

        self.metric_space_init = true;
        Ok(())
    }

    /// Check if MetricSpace typeclass has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.metric_space_init == true`
    pub(crate) fn has_metric_space(&self) -> bool {
        self.metric_space_init
    }

    // ============================================================================
    // MetricSpace instances for Nat, Int, Rat
    // ============================================================================

    /// Initialize MetricSpace instance for Nat
    ///
    /// Adds:
    /// - instMetricSpaceNat : MetricSpace Nat
    ///
    /// Uses Nat.dist as the distance function (converted to Rat).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.nat_metric_space_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_nat_metric_space(&mut self) -> Result<(), EnvError> {
        if self.nat_metric_space_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_metric_space()?; // Provides MetricSpace typeclass
        self.init_nat_dist()?; // Provides Nat.dist and properties

        // instMetricSpaceNat : MetricSpace Nat
        // Nat : Type 0, so MetricSpace.{0}
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("MetricSpace"), vec![Level::zero()]),
            nat_const,
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("instMetricSpaceNat"),
            level_params: vec![],
            type_: inst_type,
        })?;

        self.nat_metric_space_init = true;
        Ok(())
    }

    /// Check if Nat MetricSpace instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.nat_metric_space_init == true`
    pub(crate) fn has_nat_metric_space(&self) -> bool {
        self.nat_metric_space_init
    }

    /// Initialize MetricSpace instance for Int
    ///
    /// Adds:
    /// - instMetricSpaceInt : MetricSpace Int
    ///
    /// Uses Int.dist as the distance function (converted to Rat).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.int_metric_space_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_int_metric_space(&mut self) -> Result<(), EnvError> {
        if self.int_metric_space_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_metric_space()?; // Provides MetricSpace typeclass
        self.init_int_dist()?; // Provides Int.dist and properties

        // instMetricSpaceInt : MetricSpace Int
        // Int : Type 0, so MetricSpace.{0}
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("MetricSpace"), vec![Level::zero()]),
            int_const,
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("instMetricSpaceInt"),
            level_params: vec![],
            type_: inst_type,
        })?;

        self.int_metric_space_init = true;
        Ok(())
    }

    /// Check if Int MetricSpace instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.int_metric_space_init == true`
    pub(crate) fn has_int_metric_space(&self) -> bool {
        self.int_metric_space_init
    }

    /// Initialize MetricSpace instance for Rat
    ///
    /// Adds:
    /// - instMetricSpaceRat : MetricSpace Rat
    ///
    /// Uses Rat.dist as the distance function.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.rat_metric_space_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_rat_metric_space(&mut self) -> Result<(), EnvError> {
        if self.rat_metric_space_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_metric_space()?; // Provides MetricSpace typeclass
        self.init_rat_dist()?; // Provides Rat.dist and properties

        // instMetricSpaceRat : MetricSpace Rat
        // Rat : Type 0, so MetricSpace.{0}
        let rat_const = Expr::const_(Name::from_string("Rat"), vec![]);
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("MetricSpace"), vec![Level::zero()]),
            rat_const,
        );

        self.add_decl(Declaration::Axiom {
            name: Name::from_string("instMetricSpaceRat"),
            level_params: vec![],
            type_: inst_type,
        })?;

        self.rat_metric_space_init = true;
        Ok(())
    }

    /// Check if Rat MetricSpace instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.rat_metric_space_init == true`
    pub(crate) fn has_rat_metric_space(&self) -> bool {
        self.rat_metric_space_init
    }
}
