// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hausdorff (T2) separation axiom

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Build the sequence of declarations for Topology.Hausdorff and related axioms.
///
/// Returns declarations in registration order. Conditional declarations are
/// controlled by boolean parameters:
/// - `include_compact`: adds `Topology.hausdorff_compact_closed` (requires Compact init)
/// - `include_metric`: adds `Topology.metric_hausdorff` (requires MetricSpace init)
///
/// This is a pure function with no side effects. Both the production init function
/// and the test harness can call it to get the same declaration list.
pub(crate) fn topology_hausdorff_decl_templates(
    include_compact: bool,
    include_metric: bool,
) -> Vec<Declaration> {
    let mut decls = Vec::new();

    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let topological_space =
        |lvl: Level| Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl]);
    let is_open = |lvl: Level| Expr::const_(Name::from_string("IsOpen"), vec![lvl]);
    let is_closed = |lvl: Level| Expr::const_(Name::from_string("IsClosed"), vec![lvl]);
    let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    let not_const = Expr::const_(Name::from_string("Not"), vec![]);
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);

    // Exists at level u+1 for (α → Prop) : Type u
    let exists_set_const = Expr::const_(
        Name::from_string("Exists"),
        vec![Level::succ(u_level.clone())],
    );

    let topology_hausdorff =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Hausdorff"), vec![lvl]);

    // ================================================================
    // Topology.Hausdorff : {α : Type u} → [TopologicalSpace α] → Prop
    // ================================================================

    let hausdorff_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, _inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            prop.clone(),
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.Hausdorff"),
        level_params: vec![u.clone()],
        type_: hausdorff_type,
    });

    // ================================================================
    // Topology.hausdorff_def : {α : Type u} → [TopologicalSpace α] →
    //   Iff (Topology.Hausdorff)
    //       (∀ x y : α, ¬(x = y) → ∃ U V : α → Prop,
    //         IsOpen U ∧ IsOpen V ∧ U x ∧ V y ∧ ∀ z, ¬(U z ∧ V z))
    // ================================================================

    let hausdorff_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));

        // LHS: Topology.Hausdorff α inst
        let hausdorff_inst = Expr::app(
            Expr::app(topology_hausdorff(u_level.clone()), alpha.clone()),
            inst.clone(),
        );

        // Build RHS: ∀ x y : α, ¬(x = y) → ∃ U V : α → Prop,
        //   IsOpen U ∧ IsOpen V ∧ U x ∧ V y ∧ ∀ z, ¬(U z ∧ V z)
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());

        // ¬(x = y)
        let eq_x_y = Expr::app(
            Expr::app(Expr::app(eq_const.clone(), alpha.clone()), x.clone()),
            y.clone(),
        );
        let not_eq_x_y = Expr::app(not_const.clone(), eq_x_y);
        let (h_ne_id, _h_ne) = b.fresh_local(not_eq_x_y.clone());

        // Existential variables U, V : α → Prop
        let alpha_to_prop = Expr::arrow(alpha.clone(), prop.clone());
        let (u_set_id, u_set) = b.fresh_local(alpha_to_prop.clone());
        let (v_set_id, v_set) = b.fresh_local(alpha_to_prop.clone());

        // IsOpen U, IsOpen V
        let is_open_u = Expr::apps(
            is_open(u_level.clone()),
            [alpha.clone(), inst.clone(), u_set.clone()],
        );
        let is_open_v = Expr::apps(
            is_open(u_level.clone()),
            [alpha.clone(), inst.clone(), v_set.clone()],
        );

        // U x, V y
        let ux = Expr::app(u_set.clone(), x.clone());
        let vy = Expr::app(v_set.clone(), y.clone());

        // Disjoint: ∀ z : α, ¬(U z ∧ V z)
        let (z_id, z) = b.fresh_local(alpha.clone());
        let u_z = Expr::app(u_set.clone(), z.clone());
        let v_z = Expr::app(v_set.clone(), z.clone());
        let not_u_z_and_v_z = Expr::app(
            not_const.clone(),
            Expr::app(Expr::app(and_const.clone(), u_z), v_z),
        );
        let disjoint = b.mk_pi(z_id, BinderInfo::Default, alpha.clone(), not_u_z_and_v_z);

        // Conjunction: IsOpen U ∧ IsOpen V ∧ U x ∧ V y ∧ Disjoint
        let and_4 = Expr::app(Expr::app(and_const.clone(), vy), disjoint);
        let and_3 = Expr::app(Expr::app(and_const.clone(), ux), and_4);
        let and_2 = Expr::app(Expr::app(and_const.clone(), is_open_v), and_3);
        let and_1 = Expr::app(Expr::app(and_const.clone(), is_open_u), and_2);

        // ∃ V : α → Prop, (conjunction)
        let exists_v_pred = b.mk_lam(v_set_id, BinderInfo::Default, alpha_to_prop.clone(), and_1);
        let exists_v = Expr::app(
            Expr::app(exists_set_const.clone(), alpha_to_prop.clone()),
            exists_v_pred,
        );

        // ∃ U : α → Prop, ∃ V ...
        let exists_u_pred = b.mk_lam(
            u_set_id,
            BinderInfo::Default,
            alpha_to_prop.clone(),
            exists_v,
        );
        let exists_u = Expr::app(
            Expr::app(exists_set_const.clone(), alpha_to_prop.clone()),
            exists_u_pred,
        );

        // ¬(x = y) → ∃ U V, ...
        let e = b.mk_pi(h_ne_id, BinderInfo::Default, not_eq_x_y, exists_u);
        // ∀ y : α, ...
        let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), e);
        // ∀ x : α, ...
        let forall_x = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);

        // Iff (Hausdorff) (∀ x y, ...)
        let hausdorff_iff = Expr::app(Expr::app(iff_const.clone(), hausdorff_inst), forall_x);

        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            hausdorff_iff,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.hausdorff_def"),
        level_params: vec![u.clone()],
        type_: hausdorff_def_type,
    });

    // ================================================================
    // Topology.hausdorff_singleton_closed : {α : Type u} → [TopologicalSpace α] →
    //   Topology.Hausdorff → (x : α) → IsClosed (fun y => y = x)
    // ================================================================

    let hausdorff_singleton_closed_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let hausdorff_ty = Expr::app(
            Expr::app(topology_hausdorff(u_level.clone()), alpha.clone()),
            inst.clone(),
        );
        let (h_id, _h) = b.fresh_local(hausdorff_ty.clone());
        let (x_id, x_var) = b.fresh_local(alpha.clone());

        // The singleton set: fun y : α => y = x
        let (y_id, y_var) = b.fresh_local(alpha.clone());
        let y_eq_x = Expr::app(
            Expr::app(Expr::app(eq_const.clone(), alpha.clone()), y_var.clone()),
            x_var.clone(),
        );
        let singleton_set = b.mk_lam(y_id, BinderInfo::Default, alpha.clone(), y_eq_x);

        // IsClosed {α} [inst] singleton_set
        let result = Expr::apps(
            is_closed(u_level.clone()),
            [alpha.clone(), inst.clone(), singleton_set],
        );

        let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), result);
        let e = b.mk_pi(h_id, BinderInfo::Default, hausdorff_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.hausdorff_singleton_closed"),
        level_params: vec![u.clone()],
        type_: hausdorff_singleton_closed_type,
    });

    // ================================================================
    // Topology.hausdorff_compact_closed : {α : Type u} → [TopologicalSpace α] →
    //   Topology.Hausdorff → (s : α → Prop) → Topology.IsCompactSet s → IsClosed s
    // (Only added if include_compact is true)
    // ================================================================

    if include_compact {
        let is_compact_set =
            |lvl: Level| Expr::const_(Name::from_string("Topology.IsCompactSet"), vec![lvl]);

        let hausdorff_compact_closed_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) =
                b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
            let hausdorff_ty = Expr::app(
                Expr::app(topology_hausdorff(u_level.clone()), alpha.clone()),
                inst.clone(),
            );
            let (h_id, _h) = b.fresh_local(hausdorff_ty.clone());
            let alpha_to_prop = Expr::arrow(alpha.clone(), prop.clone());
            let (s_id, s) = b.fresh_local(alpha_to_prop.clone());

            // IsCompactSet {α} [inst] s
            let compact_s = Expr::apps(
                is_compact_set(u_level.clone()),
                [alpha.clone(), inst.clone(), s.clone()],
            );
            let (hs_id, _hs) = b.fresh_local(compact_s.clone());

            // IsClosed {α} [inst] s
            let closed_s = Expr::apps(
                is_closed(u_level.clone()),
                [alpha.clone(), inst.clone(), s.clone()],
            );

            let e = b.mk_pi(hs_id, BinderInfo::Default, compact_s, closed_s);
            let e = b.mk_pi(s_id, BinderInfo::Default, alpha_to_prop, e);
            let e = b.mk_pi(h_id, BinderInfo::Default, hausdorff_ty, e);
            let e = b.mk_pi(
                inst_id,
                BinderInfo::InstImplicit,
                Expr::app(topological_space(u_level.clone()), alpha.clone()),
                e,
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        decls.push(Declaration::Axiom {
            name: Name::from_string("Topology.hausdorff_compact_closed"),
            level_params: vec![u.clone()],
            type_: hausdorff_compact_closed_type,
        });
    }

    // ================================================================
    // Topology.hausdorff_separated_by_closed : {α : Type u} → [TopologicalSpace α] →
    //   Topology.Hausdorff → (x y : α) → ¬(x = y) →
    //   ∃ C : α → Prop, IsClosed C ∧ C x ∧ ¬(C y)
    // ================================================================

    let separated_by_closed_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let hausdorff_ty = Expr::app(
            Expr::app(topology_hausdorff(u_level.clone()), alpha.clone()),
            inst.clone(),
        );
        let (h_id, _h) = b.fresh_local(hausdorff_ty.clone());
        let (x_id, x_var) = b.fresh_local(alpha.clone());
        let (y_id, y_var) = b.fresh_local(alpha.clone());

        // ¬(x = y)
        let ne_x_y = Expr::app(
            not_const.clone(),
            Expr::app(
                Expr::app(Expr::app(eq_const.clone(), alpha.clone()), x_var.clone()),
                y_var.clone(),
            ),
        );
        let (hne_id, _hne) = b.fresh_local(ne_x_y.clone());

        // Existential: ∃ C : α → Prop, IsClosed C ∧ C x ∧ ¬(C y)
        let alpha_to_prop = Expr::arrow(alpha.clone(), prop.clone());
        let (c_id, c_var) = b.fresh_local(alpha_to_prop.clone());

        // IsClosed {α} [inst] C
        let is_closed_c = Expr::apps(
            is_closed(u_level.clone()),
            [alpha.clone(), inst.clone(), c_var.clone()],
        );

        // C x, C y
        let c_x = Expr::app(c_var.clone(), x_var.clone());
        let c_y = Expr::app(c_var.clone(), y_var.clone());
        let not_c_y = Expr::app(not_const.clone(), c_y);

        // IsClosed C ∧ C x ∧ ¬(C y)
        let and_inner = Expr::app(Expr::app(and_const.clone(), c_x), not_c_y);
        let conjunction = Expr::app(Expr::app(and_const.clone(), is_closed_c), and_inner);

        // ∃ C : α → Prop, ...
        let exists_pred = b.mk_lam(
            c_id,
            BinderInfo::Default,
            alpha_to_prop.clone(),
            conjunction,
        );
        let exists_c = Expr::app(
            Expr::app(exists_set_const.clone(), alpha_to_prop.clone()),
            exists_pred,
        );

        // Close binders inside-out
        let e = b.mk_pi(hne_id, BinderInfo::Default, ne_x_y, exists_c);
        let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
        let e = b.mk_pi(h_id, BinderInfo::Default, hausdorff_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.hausdorff_separated_by_closed"),
        level_params: vec![u.clone()],
        type_: separated_by_closed_type,
    });

    // ================================================================
    // Topology.metric_hausdorff : {α : Type u} → [MetricSpace α] →
    //   Topology.Hausdorff (inst := Topology.metric_to_topology)
    // (Only added if include_metric is true)
    // ================================================================

    if include_metric {
        let metric_space_const =
            |lvl: Level| Expr::const_(Name::from_string("MetricSpace"), vec![lvl]);

        let metric_hausdorff_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (ms_id, ms) = b.fresh_local(Expr::app(
                metric_space_const(u_level.clone()),
                alpha.clone(),
            ));

            // Topology.metric_to_topology {α} ms
            let metric_to_topology = Expr::const_(
                Name::from_string("Topology.metric_to_topology"),
                vec![u_level.clone()],
            );
            let induced_topology =
                Expr::app(Expr::app(metric_to_topology, alpha.clone()), ms.clone());

            // Topology.Hausdorff {α} [induced_topology]
            let result = Expr::app(
                Expr::app(topology_hausdorff(u_level.clone()), alpha.clone()),
                induced_topology,
            );

            let e = b.mk_pi(
                ms_id,
                BinderInfo::InstImplicit,
                Expr::app(metric_space_const(u_level.clone()), alpha.clone()),
                result,
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        decls.push(Declaration::Axiom {
            name: Name::from_string("Topology.metric_hausdorff"),
            level_params: vec![u.clone()],
            type_: metric_hausdorff_type,
        });
    }

    decls
}

impl Environment {
    /// Initialize Topology.Hausdorff (T2 separation axiom)
    ///
    /// A topological space is Hausdorff if any two distinct points can be
    /// separated by disjoint open neighborhoods.
    ///
    /// This adds:
    /// - Topology.Hausdorff : {α : Type u} → [TopologicalSpace α] → Prop
    /// - Topology.hausdorff_def : Characterization via disjoint neighborhoods
    /// - Topology.hausdorff_singleton_closed : Singletons are closed in Hausdorff spaces
    /// - Topology.hausdorff_compact_closed : Compact sets are closed in Hausdorff spaces
    /// - Topology.hausdorff_limits_unique : Limits are unique in Hausdorff spaces
    /// - Topology.metric_hausdorff : Metric spaces are Hausdorff
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_hausdorff_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_hausdorff(&mut self) -> Result<(), EnvError> {
        if self.topology_hausdorff_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_iff()?;
        self.init_and()?;
        self.init_exists()?;
        self.init_true_false()?; // Provides Not
        self.init_eq()?;

        let include_compact = self.topology_compact_init;
        let include_metric = self.metric_space_init;
        self.add_init_decls(topology_hausdorff_decl_templates(
            include_compact,
            include_metric,
        ))?;

        self.topology_hausdorff_init = true;
        Ok(())
    }

    /// Check if Topology.Hausdorff has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_hausdorff_init == true`
    pub(crate) fn has_topology_hausdorff(&self) -> bool {
        self.topology_hausdorff_init
    }
}
