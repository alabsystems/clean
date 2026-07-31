// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compact and locally compact topological spaces

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr, ExprKind};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Build the sequence of declarations for `Topology.Compact` and related axioms.
///
/// Returns declarations in registration order. Requires that TopologicalSpace,
/// Continuous, Iff, And, and Exists are already initialized.
///
/// Pass `include_metric_iff=true` to include the `Topology.metric_compact_iff`
/// declaration (requires MetricSpace and Metric.Compact to be initialized).
#[cfg(test)]
pub(crate) fn topology_compact_decl_templates(include_metric_iff: bool) -> Vec<Declaration> {
    let mut decls = Vec::new();

    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let u_level = Level::param(u.clone());
    let v_level = Level::param(v.clone());
    let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)
    let type_v = Expr::sort(Level::succ(v_level.clone())); // Type v = Sort (v+1)
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let topological_space =
        |lvl: Level| Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl]);
    let is_closed = |lvl: Level| Expr::const_(Name::from_string("IsClosed"), vec![lvl]);
    let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);

    // ================================================================
    // Topology.Compact : {α : Type u} → [TopologicalSpace α] → Prop
    // ================================================================

    let compact_type = {
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
        name: Name::from_string("Topology.Compact"),
        level_params: vec![u.clone()],
        type_: compact_type,
    });

    let topology_compact =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Compact"), vec![lvl]);

    // ================================================================
    // Topology.compact_def : {α : Type u} → [TopologicalSpace α] →
    //   Iff (Topology.Compact) (Topology.Compact)
    //   (reflexive placeholder — proper characterization needs finite sets)
    // ================================================================

    let compact_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));

        let compact_inst = Expr::app(
            Expr::app(topology_compact(u_level.clone()), alpha.clone()),
            inst.clone(),
        );

        let iff_body = Expr::app(
            Expr::app(iff_const.clone(), compact_inst.clone()),
            compact_inst,
        );
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            iff_body,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.compact_def"),
        level_params: vec![u.clone()],
        type_: compact_def_type,
    });

    // ================================================================
    // Topology.IsCompactSet : {α : Type u} → [TopologicalSpace α] →
    //   (α → Prop) → Prop
    // ================================================================

    let is_compact_set_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, _inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let s_type = Expr::arrow(alpha.clone(), prop.clone());
        let (s_id, _s) = b.fresh_local(s_type.clone());
        let e = b.mk_pi(s_id, BinderInfo::Default, s_type, prop.clone());
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
        name: Name::from_string("Topology.IsCompactSet"),
        level_params: vec![u.clone()],
        type_: is_compact_set_type,
    });

    let is_compact_set =
        |lvl: Level| Expr::const_(Name::from_string("Topology.IsCompactSet"), vec![lvl]);

    // ================================================================
    // Topology.compact_iff_compact_univ : {α : Type u} → [TopologicalSpace α] →
    //   Iff (Topology.Compact) (Topology.IsCompactSet (fun _ : α => True))
    // ================================================================

    let compact_iff_compact_univ_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));

        let compact_space = Expr::app(
            Expr::app(topology_compact(u_level.clone()), alpha.clone()),
            inst.clone(),
        );

        let true_const = Expr::const_(Name::from_string("True"), vec![]);
        let univ_set = {
            let mut sub = EnvDeclBuilder::child_of(&b);
            let (x_id, _x) = sub.fresh_local(alpha.clone());
            sub.mk_lam(x_id, BinderInfo::Default, alpha.clone(), true_const)
        };

        let compact_univ = Expr::apps(
            is_compact_set(u_level.clone()),
            [alpha.clone(), inst.clone(), univ_set],
        );

        let iff_body = Expr::app(Expr::app(iff_const.clone(), compact_space), compact_univ);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            iff_body,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.compact_iff_compact_univ"),
        level_params: vec![u.clone()],
        type_: compact_iff_compact_univ_type,
    });

    // ================================================================
    // Topology.compact_closed : {α : Type u} → [TopologicalSpace α] →
    //   Topology.Compact → (s : α → Prop) → IsClosed s →
    //   Topology.IsCompactSet s
    // ================================================================

    let compact_closed_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let compact_ty = Expr::app(
            Expr::app(topology_compact(u_level.clone()), alpha.clone()),
            inst.clone(),
        );
        let (hc_id, _hc) = b.fresh_local(compact_ty.clone());
        let alpha_to_prop = Expr::arrow(alpha.clone(), prop.clone());
        let (s_id, s) = b.fresh_local(alpha_to_prop.clone());

        let closed_s = Expr::apps(
            is_closed(u_level.clone()),
            [alpha.clone(), inst.clone(), s.clone()],
        );
        let (hs_id, _hs) = b.fresh_local(closed_s.clone());

        let compact_set_s = Expr::apps(
            is_compact_set(u_level.clone()),
            [alpha.clone(), inst.clone(), s.clone()],
        );

        let e = b.mk_pi(hs_id, BinderInfo::Default, closed_s, compact_set_s);
        let e = b.mk_pi(s_id, BinderInfo::Default, alpha_to_prop, e);
        let e = b.mk_pi(hc_id, BinderInfo::Default, compact_ty, e);
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
        name: Name::from_string("Topology.compact_closed"),
        level_params: vec![u.clone()],
        type_: compact_closed_type,
    });

    // ================================================================
    // Topology.compact_image : {α : Type u} → {β : Type v} →
    //   [TopologicalSpace α] → [TopologicalSpace β] →
    //   (f : α → β) → Topology.Continuous f →
    //   Topology.Compact (α := α) → Topology.Compact (α := β)
    // ================================================================

    let topology_continuous_const = |u_lvl: Level, v_lvl: Level| {
        Expr::const_(Name::from_string("Topology.Continuous"), vec![u_lvl, v_lvl])
    };

    let compact_image_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let inst_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let inst_beta_ty = Expr::app(topological_space(v_level.clone()), beta.clone());
        let (inst_alpha_id, inst_alpha) = b.fresh_local(inst_alpha_ty.clone());
        let (inst_beta_id, inst_beta) = b.fresh_local(inst_beta_ty.clone());
        let f_ty = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, f) = b.fresh_local(f_ty.clone());

        let continuous_f = Expr::apps(
            topology_continuous_const(u_level.clone(), v_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_alpha.clone(),
                inst_beta.clone(),
                f.clone(),
            ],
        );
        let (hf_id, _hf) = b.fresh_local(continuous_f.clone());

        let compact_alpha = Expr::app(
            Expr::app(topology_compact(u_level.clone()), alpha.clone()),
            inst_alpha.clone(),
        );
        let (hc_id, _hc) = b.fresh_local(compact_alpha.clone());
        let compact_beta = Expr::app(
            Expr::app(topology_compact(v_level.clone()), beta.clone()),
            inst_beta.clone(),
        );

        let e = b.mk_pi(hc_id, BinderInfo::Default, compact_alpha, compact_beta);
        let e = b.mk_pi(hf_id, BinderInfo::Default, continuous_f, e);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
        let e = b.mk_pi(inst_beta_id, BinderInfo::InstImplicit, inst_beta_ty, e);
        let e = b.mk_pi(inst_alpha_id, BinderInfo::InstImplicit, inst_alpha_ty, e);
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.compact_image"),
        level_params: vec![u.clone(), v.clone()],
        type_: compact_image_type,
    });

    // ================================================================
    // Topology.compact_set_image : {α : Type u} → {β : Type v} →
    //   [TopologicalSpace α] → [TopologicalSpace β] →
    //   (f : α → β) → Topology.Continuous f →
    //   (s : α → Prop) → Topology.IsCompactSet s →
    //   Topology.IsCompactSet (fun y => ∃ x, s x ∧ f x = y)
    // ================================================================

    let exists_const = Expr::const_(
        Name::from_string("Exists"),
        vec![Level::succ(u_level.clone())],
    );
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(v_level.clone())]);

    let compact_set_image_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let inst_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let inst_beta_ty = Expr::app(topological_space(v_level.clone()), beta.clone());
        let (inst_alpha_id, inst_alpha) = b.fresh_local(inst_alpha_ty.clone());
        let (inst_beta_id, inst_beta) = b.fresh_local(inst_beta_ty.clone());

        let f_ty = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let continuous_f = Expr::apps(
            topology_continuous_const(u_level.clone(), v_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_alpha.clone(),
                inst_beta.clone(),
                f.clone(),
            ],
        );
        let (hf_id, _hf) = b.fresh_local(continuous_f.clone());

        let set_alpha_ty = Expr::pi(BinderInfo::Default, alpha.clone(), prop.clone());
        let (s_id, s) = b.fresh_local(set_alpha_ty.clone());
        let compact_set_s = Expr::apps(
            is_compact_set(u_level.clone()),
            [alpha.clone(), inst_alpha.clone(), s.clone()],
        );
        let (hs_id, _hs) = b.fresh_local(compact_set_s.clone());

        let (y_id, y) = b.fresh_local(beta.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let s_x = Expr::app(s.clone(), x.clone());
        let f_x = Expr::app(f.clone(), x);
        let eq_f_x_y = Expr::app(
            Expr::app(Expr::app(eq_const.clone(), beta.clone()), f_x),
            y.clone(),
        );
        let and_s_eq = Expr::app(Expr::app(and_const.clone(), s_x), eq_f_x_y);
        let exists_body = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), and_s_eq);
        let exists_x = Expr::app(Expr::app(exists_const.clone(), alpha.clone()), exists_body);
        let image_set = b.mk_lam(y_id, BinderInfo::Default, beta.clone(), exists_x);

        let compact_image_set = Expr::apps(
            is_compact_set(v_level.clone()),
            [beta.clone(), inst_beta.clone(), image_set],
        );

        let e = b.mk_pi(hs_id, BinderInfo::Default, compact_set_s, compact_image_set);
        let e = b.mk_pi(s_id, BinderInfo::Default, set_alpha_ty, e);
        let e = b.mk_pi(hf_id, BinderInfo::Default, continuous_f, e);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
        let e = b.mk_pi(inst_beta_id, BinderInfo::InstImplicit, inst_beta_ty, e);
        let e = b.mk_pi(inst_alpha_id, BinderInfo::InstImplicit, inst_alpha_ty, e);
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.compact_set_image"),
        level_params: vec![u.clone(), v.clone()],
        type_: compact_set_image_type,
    });

    // ================================================================
    // Topology.metric_compact_iff (conditional)
    // ================================================================

    if include_metric_iff {
        let metric_space_const =
            |lvl: Level| Expr::const_(Name::from_string("MetricSpace"), vec![lvl]);
        let metric_compact =
            |lvl: Level| Expr::const_(Name::from_string("Metric.Compact"), vec![lvl]);
        let metric_to_topology = Expr::const_(
            Name::from_string("Topology.metric_to_topology"),
            vec![u_level.clone()],
        );

        let metric_compact_iff_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (ms_id, ms) = b.fresh_local(Expr::app(
                metric_space_const(u_level.clone()),
                alpha.clone(),
            ));

            let mc_inst = Expr::app(
                Expr::app(metric_compact(u_level.clone()), alpha.clone()),
                ms.clone(),
            );
            let induced_topo = Expr::app(Expr::app(metric_to_topology, alpha.clone()), ms.clone());
            let tc_inst = Expr::app(
                Expr::app(topology_compact(u_level.clone()), alpha.clone()),
                induced_topo,
            );
            let iff_compact = Expr::app(Expr::app(iff_const.clone(), mc_inst), tc_inst);

            let e = b.mk_pi(
                ms_id,
                BinderInfo::InstImplicit,
                Expr::app(metric_space_const(u_level.clone()), alpha.clone()),
                iff_compact,
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        decls.push(Declaration::Axiom {
            name: Name::from_string("Topology.metric_compact_iff"),
            level_params: vec![u.clone()],
            type_: metric_compact_iff_type,
        });
    }

    decls
}

/// Builds LocallyCompact declaration templates.
///
/// Returns declarations in dependency order:
/// 1. `Topology.LocallyCompact` — the locally compact property
/// 2. `Topology.locally_compact_def` — iff characterization
/// 3. `Topology.locally_compact_of_compact` — compact implies locally compact
///
/// Prerequisites: TopologicalSpace, Continuous, IsCompactSet, And, Exists, Iff must
/// be present in the environment before adding these declarations.
#[cfg(test)]
pub(crate) fn topology_locally_compact_decl_templates() -> Vec<Declaration> {
    let mut decls = Vec::new();

    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let topological_space =
        |lvl: Level| Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl]);
    let is_open = |lvl: Level| Expr::const_(Name::from_string("IsOpen"), vec![lvl]);
    let is_compact_set =
        |lvl: Level| Expr::const_(Name::from_string("Topology.IsCompactSet"), vec![lvl]);
    let locally_compact =
        |lvl: Level| Expr::const_(Name::from_string("Topology.LocallyCompact"), vec![lvl]);
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    let exists_set_const = Expr::const_(
        Name::from_string("Exists"),
        vec![Level::succ(u_level.clone())],
    );

    // ================================================================
    // Topology.LocallyCompact : {α : Type u} → [TopologicalSpace α] → Prop
    // ================================================================

    let locally_compact_type = {
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
        name: Name::from_string("Topology.LocallyCompact"),
        level_params: vec![u.clone()],
        type_: locally_compact_type,
    });

    // ================================================================
    // Topology.locally_compact_def : {α : Type u} → [TopologicalSpace α] →
    //   Iff (Topology.LocallyCompact α inst)
    //       (∀ x : α, ∃ U : α → Prop, IsOpen α inst U ∧ U x ∧
    //         ∃ K : α → Prop, IsCompactSet α inst K ∧ ∀ y : α, K y → U y)
    // ================================================================

    let locally_compact_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));

        // LHS: LocallyCompact α inst
        let lc_inst = Expr::app(
            Expr::app(locally_compact(u_level.clone()), alpha.clone()),
            inst.clone(),
        );

        // Set type for this universe: α → Prop
        let set_ty = Expr::pi(BinderInfo::Default, alpha.clone(), prop.clone());

        // Build RHS inside-out: ∀ x, ∃ U, ... ∃ K, ...
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (big_u_id, big_u) = b.fresh_local(set_ty.clone());
        let (big_k_id, big_k) = b.fresh_local(set_ty.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());

        // K y → U y
        let k_y = Expr::app(big_k.clone(), y.clone());
        let u_y = Expr::app(big_u.clone(), y.clone());
        let k_implies_u = b.mk_pi(
            y_id,
            BinderInfo::Default,
            alpha.clone(),
            Expr::arrow(k_y, u_y),
        );

        // IsCompactSet α inst K
        let compact_k = Expr::app(
            Expr::app(
                Expr::app(is_compact_set(u_level.clone()), alpha.clone()),
                inst.clone(),
            ),
            big_k.clone(),
        );

        // IsCompactSet K ∧ ∀ y, K y → U y
        let and_compact_subset = Expr::app(Expr::app(and_const.clone(), compact_k), k_implies_u);

        // ∃ K : α → Prop, (IsCompactSet K ∧ ∀ y, K y → U y)
        let exists_k_body = b.mk_lam(
            big_k_id,
            BinderInfo::Default,
            set_ty.clone(),
            and_compact_subset,
        );
        let exists_k = Expr::app(
            Expr::app(exists_set_const.clone(), set_ty.clone()),
            exists_k_body,
        );

        // IsOpen α inst U
        let is_open_u = Expr::app(
            Expr::app(
                Expr::app(is_open(u_level.clone()), alpha.clone()),
                inst.clone(),
            ),
            big_u.clone(),
        );

        // U x
        let u_x = Expr::app(big_u.clone(), x.clone());

        // IsOpen U ∧ U x
        let and_open_contains = Expr::app(Expr::app(and_const.clone(), is_open_u), u_x);
        // (IsOpen U ∧ U x) ∧ ∃ K, ...
        let neighborhood_compact =
            Expr::app(Expr::app(and_const.clone(), and_open_contains), exists_k);

        // ∃ U : α → Prop, ...
        let exists_u_body = b.mk_lam(
            big_u_id,
            BinderInfo::Default,
            set_ty.clone(),
            neighborhood_compact,
        );
        let exists_u = Expr::app(
            Expr::app(exists_set_const.clone(), set_ty.clone()),
            exists_u_body,
        );

        // ∀ x : α, ∃ U, ...
        let forall_x = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), exists_u);

        // Iff (LocallyCompact α inst) (∀ x, ...)
        let iff_body = Expr::app(
            Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), lc_inst),
            forall_x,
        );

        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            iff_body,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.locally_compact_def"),
        level_params: vec![u.clone()],
        type_: locally_compact_def_type,
    });

    // ================================================================
    // Topology.locally_compact_of_compact : {α : Type u} → [TopologicalSpace α] →
    //   Topology.Compact α inst → Topology.LocallyCompact α inst
    //
    // Compact spaces are locally compact.
    // ================================================================

    let topology_compact =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Compact"), vec![lvl]);

    let locally_compact_of_compact_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));

        // Topology.Compact α inst
        let compact_inst = Expr::app(
            Expr::app(topology_compact(u_level.clone()), alpha.clone()),
            inst.clone(),
        );
        // Topology.LocallyCompact α inst
        let lc_inst = Expr::app(
            Expr::app(locally_compact(u_level.clone()), alpha.clone()),
            inst.clone(),
        );

        let (h_id, _h) = b.fresh_local(compact_inst.clone());
        let e = b.mk_pi(h_id, BinderInfo::Default, compact_inst, lc_inst);
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
        name: Name::from_string("Topology.locally_compact_of_compact"),
        level_params: vec![u.clone()],
        type_: locally_compact_of_compact_type,
    });

    decls
}

#[cfg(test)]
impl Environment {
    /// Initialize Topology.Compact for compact topological spaces.
    ///
    /// This adds:
    /// - `Topology.Compact` : {α : Type u} → [TopologicalSpace α] → Prop
    /// - `Topology.compact_def` : Characterization via open covers
    /// - `Topology.compact_closed` : Closed subsets of compact spaces are compact
    /// - `Topology.compact_image` : Continuous image of compact is compact
    /// - `Topology.compact_connected_closed` : Compact connected subsets of Hausdorff spaces are closed
    /// - `Topology.metric_compact_iff` : For metric spaces, metric compactness iff topological compactness
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_compact_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_topology_compact(&mut self) -> Result<(), EnvError> {
        if self.topology_compact_init {
            return Ok(());
        }

        // Dependencies
        self.init_topological_space()?;
        self.init_topology_continuous()?;
        self.init_iff()?;
        self.init_and()?;
        self.init_exists()?;

        let include_metric_iff = self.metric_compact_init;
        self.add_init_decls(topology_compact_decl_templates(include_metric_iff))?;

        self.topology_compact_init = true;
        Ok(())
    }

    /// Check if Topology.Compact has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_compact_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_compact(&self) -> bool {
        self.topology_compact_init
    }

    /// Initialize Topology.LocallyCompact for locally compact topological spaces.
    ///
    /// A space is locally compact if every point has a compact neighborhood.
    ///
    /// This adds:
    /// - `Topology.LocallyCompact : {α : Type u} → [TopologicalSpace α] → Prop`
    /// - `Topology.locally_compact_def` : Characterization via compact neighborhoods
    /// - `Topology.locally_compact_of_compact` : Compact → LocallyCompact
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_locally_compact_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    #[cfg(test)]
    pub(crate) fn init_topology_locally_compact(&mut self) -> Result<(), EnvError> {
        if self.topology_locally_compact_init {
            return Ok(());
        }

        // Dependencies
        self.init_topology_compact()?; // brings TopologicalSpace, Continuous, IsCompactSet
        self.init_and()?;
        self.init_exists()?;

        self.add_init_decls(topology_locally_compact_decl_templates())?;

        self.topology_locally_compact_init = true;
        Ok(())
    }

    /// Check if Topology.LocallyCompact has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_locally_compact_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_locally_compact(&self) -> bool {
        self.topology_locally_compact_init
    }
}
