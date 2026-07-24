// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated namespace overlay for #1444.
//!
//! Instead of hand-writing each declaration with manual binder arithmetic,
//! this module provides a declarative overlay system where declaration types
//! are built once using `EnvDeclBuilder`, captured as `ConstantInfo` records,
//! and then loaded via `extend_constants_unchecked`.
//!
//! This eliminates the bug class of off-by-one de Bruijn index errors in
//! declaration init code (see #1403, #1442, #1443, #1444).
//!
//! See `designs/2026-02-16-1444-olean-overlay-alternative.md`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared universe/type context for Topology.Manifold declarations.
struct ManifoldCtx {
    u: Name,
    v: Name,
    u_level: Level,
    v_level: Level,
    type_u: Expr,
    type_v: Expr,
    prop: Expr,
}

impl ManifoldCtx {
    fn new() -> Self {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        Self {
            type_u: Expr::sort(Level::succ(u_level.clone())),
            type_v: Expr::sort(Level::succ(v_level.clone())),
            prop: Expr::sort(Level::zero()),
            u,
            v,
            u_level,
            v_level,
        }
    }

    fn nat_const(&self) -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
    }

    fn topological_space(&self, level: Level) -> Expr {
        Expr::const_(Name::from_string("TopologicalSpace"), vec![level])
    }

    /// Build `Chart M ts_m n` application expression.
    fn chart_app(&self, m: Expr, ts_m: Expr, n: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Topology.Manifold.Chart"),
                        vec![self.u_level.clone()],
                    ),
                    m,
                ),
                ts_m,
            ),
            n,
        )
    }

    /// Build `Atlas M ts_m n` application expression.
    fn atlas_app(&self, m: Expr, ts_m: Expr, n: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Topology.Manifold.Atlas"),
                        vec![self.u_level.clone()],
                    ),
                    m,
                ),
                ts_m,
            ),
            n,
        )
    }

    /// Build `SmoothManifold M ts_m n` application expression.
    fn smooth_manifold_app_at(&self, level: Level, m: Expr, ts_m: Expr, n: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Topology.Manifold.SmoothManifold"),
                        vec![level],
                    ),
                    m,
                ),
                ts_m,
            ),
            n,
        )
    }

    /// Build `SmoothManifold M ts_m n` application expression at universe `u`.
    fn smooth_manifold_app(&self, m: Expr, ts_m: Expr, n: Expr) -> Expr {
        self.smooth_manifold_app_at(self.u_level.clone(), m, ts_m, n)
    }

    fn to_axiom_info(&self, name: &str, type_: Expr) -> ConstantInfo {
        self.to_axiom_info_with_levels(name, vec![self.u.clone()], type_)
    }

    fn to_axiom_info_with_levels(
        &self,
        name: &str,
        level_params: Vec<Name>,
        type_: Expr,
    ) -> ConstantInfo {
        ConstantInfo {
            name: Name::from_string(name),
            level_params,
            type_,
            value: None,
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            kind: ConstantKind::Axiom,
        }
    }
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → Nat → Type u`
fn build_chart_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, _) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, _) = b.fresh_local(nat_ty.clone());

    let e = ctx.type_u.clone();
    let e = b.mk_pi(n_id, BinderInfo::Default, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   Chart M n → M → Prop`
fn build_chart_domain_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let chart_m_n = ctx.chart_app(m.clone(), ts_m_inst, n);
    let (c_id, _) = b.fresh_local(chart_m_n.clone());
    let (x_id, _) = b.fresh_local(m.clone());

    let e = ctx.prop.clone();
    let e = b.mk_pi(x_id, BinderInfo::Default, m.clone(), e);
    let e = b.mk_pi(c_id, BinderInfo::Default, chart_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   Chart M n → M → (Fin n → Rat)`
fn build_chart_to_fun_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let chart_m_n = ctx.chart_app(m.clone(), ts_m_inst, n.clone());
    let (c_id, _) = b.fresh_local(chart_m_n.clone());
    let (x_id, _) = b.fresh_local(m.clone());

    let fin_to_rat_ty = Expr::pi(
        BinderInfo::Default,
        Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), n),
        Expr::const_(Name::from_string("Rat"), vec![]),
    );

    let e = fin_to_rat_ty;
    let e = b.mk_pi(x_id, BinderInfo::Default, m.clone(), e);
    let e = b.mk_pi(c_id, BinderInfo::Default, chart_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → Nat → Type u`
fn build_atlas_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, _) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, _) = b.fresh_local(nat_ty.clone());

    let e = ctx.type_u.clone();
    let e = b.mk_pi(n_id, BinderInfo::Default, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   Atlas M n → List (Chart M n)`
fn build_atlas_charts_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let atlas_m_n = ctx.atlas_app(m.clone(), ts_m_inst.clone(), n.clone());
    let (atlas_id, _) = b.fresh_local(atlas_m_n.clone());
    let list_chart_m_n = Expr::app(
        Expr::const_(Name::from_string("List"), vec![ctx.u_level.clone()]),
        ctx.chart_app(m, ts_m_inst, n),
    );

    let e = list_chart_m_n;
    let e = b.mk_pi(atlas_id, BinderInfo::Default, atlas_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   Atlas M n → Prop`
fn build_smooth_atlas_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let atlas_m_n = ctx.atlas_app(m, ts_m_inst, n);
    let (atlas_id, _) = b.fresh_local(atlas_m_n.clone());

    let e = ctx.prop.clone();
    let e = b.mk_pi(atlas_id, BinderInfo::Default, atlas_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → Nat → Prop`
fn build_smooth_manifold_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, _) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, _) = b.fresh_local(nat_ty.clone());

    let e = ctx.prop.clone();
    let e = b.mk_pi(n_id, BinderInfo::Default, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   [SmoothManifold M n] → M → Type u`
fn build_tangent_space_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let smooth_m_n = ctx.smooth_manifold_app(m.clone(), ts_m_inst, n);
    let (sm_id, _) = b.fresh_local(smooth_m_n.clone());
    let (x_id, _) = b.fresh_local(m.clone());

    let e = ctx.type_u.clone();
    let e = b.mk_pi(x_id, BinderInfo::Default, m.clone(), e);
    let e = b.mk_pi(sm_id, BinderInfo::InstImplicit, smooth_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   [SmoothManifold M n] → Type u`
fn build_tangent_bundle_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let smooth_m_n = ctx.smooth_manifold_app(m.clone(), ts_m_inst, n);
    let (sm_id, _) = b.fresh_local(smooth_m_n.clone());

    let e = ctx.type_u.clone();
    let e = b.mk_pi(sm_id, BinderInfo::InstImplicit, smooth_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   [SmoothManifold M n] → M → Type u`
fn build_cotangent_space_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let smooth_m_n = ctx.smooth_manifold_app(m.clone(), ts_m_inst, n);
    let (sm_id, _) = b.fresh_local(smooth_m_n.clone());
    let (x_id, _) = b.fresh_local(m.clone());

    let e = ctx.type_u.clone();
    let e = b.mk_pi(x_id, BinderInfo::Default, m.clone(), e);
    let e = b.mk_pi(sm_id, BinderInfo::InstImplicit, smooth_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build shape:
/// `{M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] →
///  {m n : Nat} → [SmoothManifold M m] → [SmoothManifold N n] → ...`
fn build_smooth_pair_type(ctx: &ManifoldCtx, result: Expr) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_type_id, m_type) = b.fresh_local(ctx.type_u.clone());
    let (n_type_id, n_type) = b.fresh_local(ctx.type_v.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m_type.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let ts_n_ty = Expr::app(ctx.topological_space(ctx.v_level.clone()), n_type.clone());
    let (ts_n_id, ts_n_inst) = b.fresh_local(ts_n_ty.clone());
    let nat_ty = ctx.nat_const();
    let (m_dim_id, m_dim) = b.fresh_local(nat_ty.clone());
    let (n_dim_id, n_dim) = b.fresh_local(nat_ty.clone());
    let smooth_m_ty =
        ctx.smooth_manifold_app_at(ctx.u_level.clone(), m_type.clone(), ts_m_inst, m_dim);
    let (sm_m_id, _) = b.fresh_local(smooth_m_ty.clone());
    let smooth_n_ty =
        ctx.smooth_manifold_app_at(ctx.v_level.clone(), n_type.clone(), ts_n_inst, n_dim);
    let (sm_n_id, _) = b.fresh_local(smooth_n_ty.clone());

    let e = b.mk_pi(sm_n_id, BinderInfo::InstImplicit, smooth_n_ty, result);
    let e = b.mk_pi(sm_m_id, BinderInfo::InstImplicit, smooth_m_ty, e);
    let e = b.mk_pi(n_dim_id, BinderInfo::Implicit, nat_ty.clone(), e);
    let e = b.mk_pi(m_dim_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_n_id, BinderInfo::InstImplicit, ts_n_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(n_type_id, BinderInfo::Implicit, ctx.type_v.clone(), e);
    let e = b.mk_pi(m_type_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type:
/// `{M : Type u} → {N : Type v} → [TopologicalSpace M] → [TopologicalSpace N] →
///  {m n : Nat} → [SmoothManifold M m] → [SmoothManifold N n] → (M → N) → Prop`
fn build_smooth_map_predicate_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_type_id, m_type) = b.fresh_local(ctx.type_u.clone());
    let (n_type_id, n_type) = b.fresh_local(ctx.type_v.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m_type.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let ts_n_ty = Expr::app(ctx.topological_space(ctx.v_level.clone()), n_type.clone());
    let (ts_n_id, ts_n_inst) = b.fresh_local(ts_n_ty.clone());
    let nat_ty = ctx.nat_const();
    let (m_dim_id, m_dim) = b.fresh_local(nat_ty.clone());
    let (n_dim_id, n_dim) = b.fresh_local(nat_ty.clone());
    let smooth_m_ty =
        ctx.smooth_manifold_app_at(ctx.u_level.clone(), m_type.clone(), ts_m_inst, m_dim);
    let (sm_m_id, _) = b.fresh_local(smooth_m_ty.clone());
    let smooth_n_ty =
        ctx.smooth_manifold_app_at(ctx.v_level.clone(), n_type.clone(), ts_n_inst, n_dim);
    let (sm_n_id, _) = b.fresh_local(smooth_n_ty.clone());
    let map_ty = Expr::pi(BinderInfo::Default, m_type, n_type);
    let (f_id, _) = b.fresh_local(map_ty.clone());

    let e = b.mk_pi(f_id, BinderInfo::Default, map_ty, ctx.prop.clone());
    let e = b.mk_pi(sm_n_id, BinderInfo::InstImplicit, smooth_n_ty, e);
    let e = b.mk_pi(sm_m_id, BinderInfo::InstImplicit, smooth_m_ty, e);
    let e = b.mk_pi(n_dim_id, BinderInfo::Implicit, nat_ty.clone(), e);
    let e = b.mk_pi(m_dim_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_n_id, BinderInfo::InstImplicit, ts_n_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(n_type_id, BinderInfo::Implicit, ctx.type_v.clone(), e);
    let e = b.mk_pi(m_type_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n k : Nat} →
///   [SmoothManifold M n] → Type u`
fn build_submanifold_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let (k_id, _k) = b.fresh_local(nat_ty.clone());
    let smooth_m_n = ctx.smooth_manifold_app(m.clone(), ts_m_inst, n);
    let (sm_id, _) = b.fresh_local(smooth_m_n.clone());

    let e = ctx.type_u.clone();
    let e = b.mk_pi(sm_id, BinderInfo::InstImplicit, smooth_m_n, e);
    let e = b.mk_pi(k_id, BinderInfo::Implicit, nat_ty.clone(), e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   [SmoothManifold M n] → Type u`
fn build_vector_field_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let smooth_m_n = ctx.smooth_manifold_app(m.clone(), ts_m_inst, n);
    let (sm_id, _) = b.fresh_local(smooth_m_n.clone());

    let e = ctx.type_u.clone();
    let e = b.mk_pi(sm_id, BinderInfo::InstImplicit, smooth_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   [SmoothManifold M n] → Nat → Type u`
fn build_differential_form_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let smooth_m_n = ctx.smooth_manifold_app(m.clone(), ts_m_inst, n);
    let (sm_id, _) = b.fresh_local(smooth_m_n.clone());
    let (k_id, _) = b.fresh_local(nat_ty.clone());

    let e = ctx.type_u.clone();
    let e = b.mk_pi(k_id, BinderInfo::Default, nat_ty.clone(), e);
    let e = b.mk_pi(sm_id, BinderInfo::InstImplicit, smooth_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build `DifferentialForm M ts_m n sm k` application expression.
fn differential_form_app(
    ctx: &ManifoldCtx,
    m: Expr,
    ts_m: Expr,
    n: Expr,
    sm: Expr,
    k: Expr,
) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Topology.Manifold.DifferentialForm"),
            vec![ctx.u_level.clone()],
        ),
        [m, ts_m, n, sm, k],
    )
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   [sm : SmoothManifold M n] → {k : Nat} →
///   DifferentialForm M n k → DifferentialForm M n (k + 1)`
fn build_exterior_derivative_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let smooth_m_n = ctx.smooth_manifold_app(m.clone(), ts_m_inst.clone(), n.clone());
    let (sm_id, sm) = b.fresh_local(smooth_m_n.clone());
    let (k_id, k) = b.fresh_local(nat_ty.clone());

    let form_m_n_k = differential_form_app(
        ctx,
        m.clone(),
        ts_m_inst.clone(),
        n.clone(),
        sm.clone(),
        k.clone(),
    );
    let (mathverse_id, _) = b.fresh_local(form_m_n_k.clone());

    let succ_k = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), k);
    let form_m_n_succ_k = differential_form_app(ctx, m, ts_m_inst, n, sm, succ_k);

    let e = form_m_n_succ_k;
    let e = b.mk_pi(mathverse_id, BinderInfo::Default, form_m_n_k, e);
    let e = b.mk_pi(k_id, BinderInfo::Implicit, nat_ty.clone(), e);
    let e = b.mk_pi(sm_id, BinderInfo::InstImplicit, smooth_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   [SmoothManifold M n] → Prop`
fn build_orientable_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let smooth_m_n = ctx.smooth_manifold_app(m.clone(), ts_m_inst, n);
    let (sm_id, _) = b.fresh_local(smooth_m_n.clone());

    let e = ctx.prop.clone();
    let e = b.mk_pi(sm_id, BinderInfo::Default, smooth_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   [sm : SmoothManifold M n] → Orientable sm → Type u`
fn build_orientation_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let smooth_m_n = ctx.smooth_manifold_app(m.clone(), ts_m_inst.clone(), n.clone());
    let (sm_id, sm) = b.fresh_local(smooth_m_n.clone());
    let orientable_sm = Expr::apps(
        Expr::const_(
            Name::from_string("Topology.Manifold.Orientable"),
            vec![ctx.u_level.clone()],
        ),
        [m.clone(), ts_m_inst, n, sm],
    );
    let (h_id, _) = b.fresh_local(orientable_sm.clone());

    let e = ctx.type_u.clone();
    let e = b.mk_pi(h_id, BinderInfo::Default, orientable_sm, e);
    let e = b.mk_pi(sm_id, BinderInfo::InstImplicit, smooth_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   [SmoothManifold M n] → Type u`
fn build_riemannian_metric_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let smooth_m_n = ctx.smooth_manifold_app(m.clone(), ts_m_inst, n);
    let (sm_id, _) = b.fresh_local(smooth_m_n.clone());

    let e = ctx.type_u.clone();
    let e = b.mk_pi(sm_id, BinderInfo::InstImplicit, smooth_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → Nat → Prop`
fn build_riemannian_manifold_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, _) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, _) = b.fresh_local(nat_ty.clone());

    let e = ctx.prop.clone();
    let e = b.mk_pi(n_id, BinderInfo::Default, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → Nat → Prop`
fn build_manifold_with_boundary_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, _) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, _) = b.fresh_local(nat_ty.clone());

    let e = ctx.prop.clone();
    let e = b.mk_pi(n_id, BinderInfo::Default, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   [ManifoldWithBoundary M n] → Type u`
fn build_boundary_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let mwb_m_n = Expr::apps(
        Expr::const_(
            Name::from_string("Topology.Manifold.ManifoldWithBoundary"),
            vec![ctx.u_level.clone()],
        ),
        [m.clone(), ts_m_inst, n],
    );
    let (mwb_id, _) = b.fresh_local(mwb_m_n.clone());

    let e = ctx.type_u.clone();
    let e = b.mk_pi(mwb_id, BinderInfo::InstImplicit, mwb_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `{M : Type u} → [TopologicalSpace M] → {n : Nat} →
///   [SmoothManifold M n] → Type u`
fn build_partition_of_unity_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let smooth_m_n = ctx.smooth_manifold_app(m.clone(), ts_m_inst, n);
    let (sm_id, _) = b.fresh_local(smooth_m_n.clone());

    let e = ctx.type_u.clone();
    let e = b.mk_pi(sm_id, BinderInfo::InstImplicit, smooth_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Build type: `∀ {M : Type u} [TopologicalSpace M] {n : Nat}
///   (sm : SmoothManifold M n), ∃ _ : PartitionOfUnity M n, True`
fn build_paracompact_type(ctx: &ManifoldCtx) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (m_id, m) = b.fresh_local(ctx.type_u.clone());
    let ts_m_ty = Expr::app(ctx.topological_space(ctx.u_level.clone()), m.clone());
    let (ts_m_id, ts_m_inst) = b.fresh_local(ts_m_ty.clone());
    let nat_ty = ctx.nat_const();
    let (n_id, n) = b.fresh_local(nat_ty.clone());
    let smooth_m_n = ctx.smooth_manifold_app(m.clone(), ts_m_inst.clone(), n.clone());
    let (sm_id, sm) = b.fresh_local(smooth_m_n.clone());

    let partition_of_unity = Expr::apps(
        Expr::const_(
            Name::from_string("Topology.Manifold.PartitionOfUnity"),
            vec![ctx.u_level.clone()],
        ),
        [m, ts_m_inst, n, sm],
    );
    let exists_partition_of_unity = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(ctx.u_level.clone())],
            ),
            partition_of_unity.clone(),
        ),
        Expr::lam(
            BinderInfo::Default,
            partition_of_unity,
            Expr::const_(Name::from_string("True"), vec![]),
        ),
    );

    let e = exists_partition_of_unity;
    let e = b.mk_pi(sm_id, BinderInfo::Default, smooth_m_n, e);
    let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
    let e = b.mk_pi(ts_m_id, BinderInfo::InstImplicit, ts_m_ty, e);
    let e = b.mk_pi(m_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    b.finish(e)
}

/// Slices 1-2: Chart/Atlas/SmoothManifold primitives (7 declarations).
fn build_chart_atlas_slice(ctx: &ManifoldCtx) -> Vec<ConstantInfo> {
    vec![
        ctx.to_axiom_info("Topology.Manifold.Chart", build_chart_type(ctx)),
        ctx.to_axiom_info(
            "Topology.Manifold.Chart.domain",
            build_chart_domain_type(ctx),
        ),
        ctx.to_axiom_info(
            "Topology.Manifold.Chart.toFun",
            build_chart_to_fun_type(ctx),
        ),
        ctx.to_axiom_info("Topology.Manifold.Atlas", build_atlas_type(ctx)),
        ctx.to_axiom_info(
            "Topology.Manifold.Atlas.charts",
            build_atlas_charts_type(ctx),
        ),
        ctx.to_axiom_info(
            "Topology.Manifold.SmoothAtlas",
            build_smooth_atlas_type(ctx),
        ),
        ctx.to_axiom_info(
            "Topology.Manifold.SmoothManifold",
            build_smooth_manifold_type(ctx),
        ),
    ]
}

/// Slices 3-4: Tangent geometry + smooth maps (10 declarations).
fn build_geometry_maps_slice(ctx: &ManifoldCtx) -> Vec<ConstantInfo> {
    let uv = vec![ctx.u.clone(), ctx.v.clone()];
    vec![
        ctx.to_axiom_info(
            "Topology.Manifold.TangentSpace",
            build_tangent_space_type(ctx),
        ),
        ctx.to_axiom_info(
            "Topology.Manifold.TangentBundle",
            build_tangent_bundle_type(ctx),
        ),
        ctx.to_axiom_info(
            "Topology.Manifold.CotangentSpace",
            build_cotangent_space_type(ctx),
        ),
        ctx.to_axiom_info_with_levels(
            "Topology.Manifold.SmoothMap",
            uv.clone(),
            build_smooth_map_predicate_type(ctx),
        ),
        ctx.to_axiom_info_with_levels(
            "Topology.Manifold.Diffeomorphism",
            uv.clone(),
            build_smooth_pair_type(
                ctx,
                Expr::sort(Level::max(
                    Level::succ(ctx.u_level.clone()),
                    Level::succ(ctx.v_level.clone()),
                )),
            ),
        ),
        ctx.to_axiom_info_with_levels(
            "Topology.Manifold.IsDiffeomorphic",
            uv.clone(),
            build_smooth_pair_type(ctx, ctx.prop.clone()),
        ),
        ctx.to_axiom_info_with_levels(
            "Topology.Manifold.Immersion",
            uv.clone(),
            build_smooth_map_predicate_type(ctx),
        ),
        ctx.to_axiom_info_with_levels(
            "Topology.Manifold.Submersion",
            uv.clone(),
            build_smooth_map_predicate_type(ctx),
        ),
        ctx.to_axiom_info_with_levels(
            "Topology.Manifold.Embedding",
            uv.clone(),
            build_smooth_map_predicate_type(ctx),
        ),
        ctx.to_axiom_info_with_levels(
            "Topology.Manifold.LocalDiffeomorphism",
            uv,
            build_smooth_map_predicate_type(ctx),
        ),
    ]
}

/// Slices 5-6: Differential forms, Riemannian geometry, boundaries (12 declarations).
fn build_diff_riemannian_slice(ctx: &ManifoldCtx) -> Vec<ConstantInfo> {
    vec![
        ctx.to_axiom_info("Topology.Manifold.Submanifold", build_submanifold_type(ctx)),
        ctx.to_axiom_info(
            "Topology.Manifold.VectorField",
            build_vector_field_type(ctx),
        ),
        ctx.to_axiom_info(
            "Topology.Manifold.DifferentialForm",
            build_differential_form_type(ctx),
        ),
        ctx.to_axiom_info(
            "Topology.Manifold.ExteriorDerivative",
            build_exterior_derivative_type(ctx),
        ),
        ctx.to_axiom_info("Topology.Manifold.Orientable", build_orientable_type(ctx)),
        ctx.to_axiom_info("Topology.Manifold.Orientation", build_orientation_type(ctx)),
        ctx.to_axiom_info(
            "Topology.Manifold.RiemannianMetric",
            build_riemannian_metric_type(ctx),
        ),
        ctx.to_axiom_info(
            "Topology.Manifold.RiemannianManifold",
            build_riemannian_manifold_type(ctx),
        ),
        ctx.to_axiom_info(
            "Topology.Manifold.ManifoldWithBoundary",
            build_manifold_with_boundary_type(ctx),
        ),
        ctx.to_axiom_info("Topology.Manifold.Boundary", build_boundary_type(ctx)),
        ctx.to_axiom_info(
            "Topology.Manifold.PartitionOfUnity",
            build_partition_of_unity_type(ctx),
        ),
        ctx.to_axiom_info(
            "Topology.Manifold.paracompact_smooth_manifold",
            build_paracompact_type(ctx),
        ),
    ]
}

/// Build the complete overlay payload for `Topology.Manifold` namespace (29 declarations).
///
/// Composed from three slice builders to stay within function size limits.
pub(crate) fn build_topology_manifold_payload() -> Vec<ConstantInfo> {
    let ctx = ManifoldCtx::new();
    let mut payload = build_chart_atlas_slice(&ctx);
    payload.extend(build_geometry_maps_slice(&ctx));
    payload.extend(build_diff_riemannian_slice(&ctx));
    payload
}

/// Build the complete overlay payload for `Topology.LieGroup` namespace (20 declarations).
pub(crate) fn build_topology_lie_group_payload() -> Vec<ConstantInfo> {
    let mut payload = Vec::with_capacity(20);
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let u_level = Level::param(u.clone());
    let v_level = Level::param(v.clone());
    let type_u = Expr::sort(Level::succ(u_level.clone()));
    let type_v = Expr::sort(Level::succ(v_level.clone()));
    let prop = Expr::sort(Level::zero());

    let nat_const = || Expr::const_(Name::from_string("Nat"), vec![]);
    let rat_const = || Expr::const_(Name::from_string("Rat"), vec![]);
    let topological_space =
        |lvl: Level| Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl]);
    let group = |lvl: Level| Expr::const_(Name::from_string("Group"), vec![lvl]);
    let _smooth_manifold = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.Manifold.SmoothManifold"),
            vec![lvl],
        )
    };

    // ================================================================
    // Topology.LieGroup.LieGroup :
    //   (G : Type u) → [TopologicalSpace G] → [Group G] → Nat → Prop
    // A group that is also a smooth manifold where multiplication and inverse are smooth
    // ================================================================

    let lie_group_type = {
        let mut b = EnvDeclBuilder::new();
        let (g_id, g) = b.fresh_local(type_u.clone());
        let ts_g_ty = Expr::app(topological_space(u_level.clone()), g.clone());
        let (ts_g_id, _ts_g_inst) = b.fresh_local(ts_g_ty.clone());
        let group_g_ty = Expr::app(group(u_level.clone()), g);
        let (group_g_id, _group_g_inst) = b.fresh_local(group_g_ty.clone());
        let nat_ty = nat_const();
        let (n_id, _n) = b.fresh_local(nat_ty.clone());

        let e = prop.clone();
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_ty, e);
        let e = b.mk_pi(group_g_id, BinderInfo::InstImplicit, group_g_ty, e);
        let e = b.mk_pi(ts_g_id, BinderInfo::InstImplicit, ts_g_ty, e);
        let e = b.mk_pi(g_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.LieGroup"),
        level_params: vec![u.clone()],
        type_: lie_group_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.LieAlgebra :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   LieGroup G n → Type u
    // The tangent space at the identity, with Lie bracket
    // ================================================================

    let lie_algebra_type = {
        let mut b = EnvDeclBuilder::new();
        let (g_id, g) = b.fresh_local(type_u.clone());
        let ts_g_ty = Expr::app(topological_space(u_level.clone()), g.clone());
        let (ts_g_id, ts_g) = b.fresh_local(ts_g_ty.clone());
        let group_g_ty = Expr::app(group(u_level.clone()), g.clone());
        let (group_g_id, group_g) = b.fresh_local(group_g_ty.clone());
        let nat_ty = nat_const();
        let (n_id, n) = b.fresh_local(nat_ty.clone());
        let lg_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.LieGroup.LieGroup"),
                            vec![u_level.clone()],
                        ),
                        g.clone(),
                    ),
                    ts_g,
                ),
                group_g,
            ),
            n,
        );
        let (lg_id, _) = b.fresh_local(lg_ty.clone());

        let e = type_u.clone();
        let e = b.mk_pi(lg_id, BinderInfo::InstImplicit, lg_ty, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(group_g_id, BinderInfo::InstImplicit, group_g_ty, e);
        let e = b.mk_pi(ts_g_id, BinderInfo::InstImplicit, ts_g_ty, e);
        let e = b.mk_pi(g_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.LieAlgebra"),
        level_params: vec![u.clone()],
        type_: lie_algebra_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.LieBracket :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   [lg : LieGroup G n] → LieAlgebra G n → LieAlgebra G n → LieAlgebra G n
    // ================================================================

    let lie_bracket_type = {
        let mut b = EnvDeclBuilder::new();
        let (g_id, g) = b.fresh_local(type_u.clone());
        let ts_g_ty = Expr::app(topological_space(u_level.clone()), g.clone());
        let (ts_g_id, ts_g) = b.fresh_local(ts_g_ty.clone());
        let group_g_ty = Expr::app(group(u_level.clone()), g.clone());
        let (group_g_id, group_g) = b.fresh_local(group_g_ty.clone());
        let nat_ty = nat_const();
        let (n_id, n) = b.fresh_local(nat_ty.clone());
        let lg_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.LieGroup.LieGroup"),
                            vec![u_level.clone()],
                        ),
                        g.clone(),
                    ),
                    ts_g.clone(),
                ),
                group_g.clone(),
            ),
            n.clone(),
        );
        let (lg_id, lg) = b.fresh_local(lg_ty.clone());
        let lie_alg = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Topology.LieGroup.LieAlgebra"),
                                vec![u_level.clone()],
                            ),
                            g,
                        ),
                        ts_g,
                    ),
                    group_g,
                ),
                n,
            ),
            lg,
        );
        let (x_id, _) = b.fresh_local(lie_alg.clone());
        let (y_id, _) = b.fresh_local(lie_alg.clone());

        let e = lie_alg.clone();
        let e = b.mk_pi(y_id, BinderInfo::Default, lie_alg.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Default, lie_alg, e);
        let e = b.mk_pi(lg_id, BinderInfo::InstImplicit, lg_ty, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(group_g_id, BinderInfo::InstImplicit, group_g_ty, e);
        let e = b.mk_pi(ts_g_id, BinderInfo::InstImplicit, ts_g_ty, e);
        let e = b.mk_pi(g_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.LieBracket"),
        level_params: vec![u.clone()],
        type_: lie_bracket_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.ExpMap :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   [lg : LieGroup G n] → LieAlgebra G n → G
    // The exponential map from Lie algebra to Lie group
    // ================================================================

    let exp_map_type = {
        let mut b = EnvDeclBuilder::new();
        let (g_id, g) = b.fresh_local(type_u.clone());
        let ts_g_ty = Expr::app(topological_space(u_level.clone()), g.clone());
        let (ts_g_id, ts_g) = b.fresh_local(ts_g_ty.clone());
        let group_g_ty = Expr::app(group(u_level.clone()), g.clone());
        let (group_g_id, group_g) = b.fresh_local(group_g_ty.clone());
        let nat_ty = nat_const();
        let (n_id, n) = b.fresh_local(nat_ty.clone());
        let lg_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.LieGroup.LieGroup"),
                            vec![u_level.clone()],
                        ),
                        g.clone(),
                    ),
                    ts_g.clone(),
                ),
                group_g.clone(),
            ),
            n.clone(),
        );
        let (lg_id, lg) = b.fresh_local(lg_ty.clone());
        let lie_alg = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Topology.LieGroup.LieAlgebra"),
                                vec![u_level.clone()],
                            ),
                            g.clone(),
                        ),
                        ts_g,
                    ),
                    group_g,
                ),
                n,
            ),
            lg,
        );
        let (x_id, _) = b.fresh_local(lie_alg.clone());

        let e = g;
        let e = b.mk_pi(x_id, BinderInfo::Default, lie_alg, e);
        let e = b.mk_pi(lg_id, BinderInfo::InstImplicit, lg_ty, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(group_g_id, BinderInfo::InstImplicit, group_g_ty, e);
        let e = b.mk_pi(ts_g_id, BinderInfo::InstImplicit, ts_g_ty, e);
        let e = b.mk_pi(g_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.ExpMap"),
        level_params: vec![u.clone()],
        type_: exp_map_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.LieGroupHom :
    //   {G : Type u} → {H : Type v} → [TopologicalSpace G] → [TopologicalSpace H] →
    //   [Group G] → [Group H] → {m n : Nat} → LieGroup G m → LieGroup H n → (G → H) → Prop
    // A group homomorphism that is also smooth
    // ================================================================

    let lie_group_hom_type = {
        let mut b = EnvDeclBuilder::new();
        let (g_id, g) = b.fresh_local(type_u.clone());
        let (h_id, h) = b.fresh_local(type_v.clone());
        let ts_g_ty = Expr::app(topological_space(u_level.clone()), g.clone());
        let (ts_g_id, ts_g) = b.fresh_local(ts_g_ty.clone());
        let ts_h_ty = Expr::app(topological_space(v_level.clone()), h.clone());
        let (ts_h_id, ts_h) = b.fresh_local(ts_h_ty.clone());
        let group_g_ty = Expr::app(group(u_level.clone()), g.clone());
        let (group_g_id, group_g) = b.fresh_local(group_g_ty.clone());
        let group_h_ty = Expr::app(group(v_level.clone()), h.clone());
        let (group_h_id, group_h) = b.fresh_local(group_h_ty.clone());
        let nat_ty = nat_const();
        let (m_id, m) = b.fresh_local(nat_ty.clone());
        let (n_id, n) = b.fresh_local(nat_ty.clone());
        let lg_g_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.LieGroup.LieGroup"),
                            vec![u_level.clone()],
                        ),
                        g.clone(),
                    ),
                    ts_g,
                ),
                group_g,
            ),
            m,
        );
        let (lg_g_id, _) = b.fresh_local(lg_g_ty.clone());
        let lg_h_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.LieGroup.LieGroup"),
                            vec![v_level.clone()],
                        ),
                        h.clone(),
                    ),
                    ts_h,
                ),
                group_h,
            ),
            n,
        );
        let (lg_h_id, _) = b.fresh_local(lg_h_ty.clone());
        let f_ty = Expr::arrow(g, h);
        let (f_id, _) = b.fresh_local(f_ty.clone());

        let e = prop.clone();
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
        let e = b.mk_pi(lg_h_id, BinderInfo::InstImplicit, lg_h_ty, e);
        let e = b.mk_pi(lg_g_id, BinderInfo::InstImplicit, lg_g_ty, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty.clone(), e);
        let e = b.mk_pi(m_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(group_h_id, BinderInfo::InstImplicit, group_h_ty, e);
        let e = b.mk_pi(group_g_id, BinderInfo::InstImplicit, group_g_ty, e);
        let e = b.mk_pi(ts_h_id, BinderInfo::InstImplicit, ts_h_ty, e);
        let e = b.mk_pi(ts_g_id, BinderInfo::InstImplicit, ts_g_ty, e);
        let e = b.mk_pi(h_id, BinderInfo::Implicit, type_v.clone(), e);
        let e = b.mk_pi(g_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.LieGroupHom"),
        level_params: vec![u.clone(), v.clone()],
        type_: lie_group_hom_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.LieSubgroup :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   LieGroup G n → Type u
    // A subgroup that is also a submanifold
    // ================================================================

    let lie_subgroup_type = {
        let mut b = EnvDeclBuilder::new();
        let (g_id, g) = b.fresh_local(type_u.clone());
        let ts_g_ty = Expr::app(topological_space(u_level.clone()), g.clone());
        let (ts_g_id, ts_g) = b.fresh_local(ts_g_ty.clone());
        let group_g_ty = Expr::app(group(u_level.clone()), g.clone());
        let (group_g_id, group_g) = b.fresh_local(group_g_ty.clone());
        let nat_ty = nat_const();
        let (n_id, n) = b.fresh_local(nat_ty.clone());
        let lg_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.LieGroup.LieGroup"),
                            vec![u_level.clone()],
                        ),
                        g,
                    ),
                    ts_g,
                ),
                group_g,
            ),
            n,
        );
        let (lg_id, _) = b.fresh_local(lg_ty.clone());

        let e = type_u.clone();
        let e = b.mk_pi(lg_id, BinderInfo::InstImplicit, lg_ty, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(group_g_id, BinderInfo::InstImplicit, group_g_ty, e);
        let e = b.mk_pi(ts_g_id, BinderInfo::InstImplicit, ts_g_ty, e);
        let e = b.mk_pi(g_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.LieSubgroup"),
        level_params: vec![u.clone()],
        type_: lie_subgroup_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.OneParameterSubgroup :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   LieGroup G n → (Rat → G) → Prop
    // A smooth homomorphism from (Rat, +) to G
    // ================================================================

    let one_param_subgroup_type = {
        let mut b = EnvDeclBuilder::new();
        let (g_id, g) = b.fresh_local(type_u.clone());
        let ts_g = Expr::app(topological_space(u_level.clone()), g.clone());
        let (ts_g_id, ts_g_inst) = b.fresh_local(ts_g.clone());
        let group_g = Expr::app(group(u_level.clone()), g.clone());
        let (group_g_id, group_g_inst) = b.fresh_local(group_g.clone());
        let (n_id, n) = b.fresh_local(nat_const());

        let lie_group_g_n = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.LieGroup.LieGroup"),
                            vec![u_level.clone()],
                        ),
                        g.clone(),
                    ),
                    ts_g_inst.clone(),
                ),
                group_g_inst.clone(),
            ),
            n.clone(),
        );
        let (lie_group_id, _lie_group_inst) = b.fresh_local(lie_group_g_n.clone());

        let gamma_ty = Expr::arrow(rat_const(), g.clone());
        let (gamma_id, _gamma) = b.fresh_local(gamma_ty.clone());

        let e = prop.clone();
        let e = b.mk_pi(gamma_id, BinderInfo::Default, gamma_ty, e);
        let e = b.mk_pi(lie_group_id, BinderInfo::InstImplicit, lie_group_g_n, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_const(), e);
        let e = b.mk_pi(group_g_id, BinderInfo::InstImplicit, group_g, e);
        let e = b.mk_pi(ts_g_id, BinderInfo::InstImplicit, ts_g, e);
        let e = b.mk_pi(g_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.OneParameterSubgroup"),
        level_params: vec![u.clone()],
        type_: one_param_subgroup_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.AdjointRep :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   [lg : LieGroup G n] → G → (LieAlgebra G n → LieAlgebra G n)
    // The adjoint representation Ad_g : 𝔤 → 𝔤
    // ================================================================

    let adjoint_rep_type = {
        let mut b = EnvDeclBuilder::new();
        let (g_ty_id, g_ty) = b.fresh_local(type_u.clone());
        let ts_g = Expr::app(topological_space(u_level.clone()), g_ty.clone());
        let (ts_g_id, ts_g_inst) = b.fresh_local(ts_g.clone());
        let group_g = Expr::app(group(u_level.clone()), g_ty.clone());
        let (group_g_id, group_g_inst) = b.fresh_local(group_g.clone());
        let (n_id, n) = b.fresh_local(nat_const());

        let lie_group_g_n = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.LieGroup.LieGroup"),
                            vec![u_level.clone()],
                        ),
                        g_ty.clone(),
                    ),
                    ts_g_inst.clone(),
                ),
                group_g_inst.clone(),
            ),
            n.clone(),
        );
        let (lie_group_id, lie_group_inst) = b.fresh_local(lie_group_g_n.clone());

        let lie_algebra_g_n = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Topology.LieGroup.LieAlgebra"),
                                vec![u_level.clone()],
                            ),
                            g_ty.clone(),
                        ),
                        ts_g_inst.clone(),
                    ),
                    group_g_inst.clone(),
                ),
                n.clone(),
            ),
            lie_group_inst.clone(),
        );

        let (g_elem_id, _g_elem) = b.fresh_local(g_ty.clone());
        let (x_id, _x) = b.fresh_local(lie_algebra_g_n.clone());

        let e = lie_algebra_g_n.clone();
        let e = b.mk_pi(x_id, BinderInfo::Default, lie_algebra_g_n.clone(), e);
        let e = b.mk_pi(g_elem_id, BinderInfo::Default, g_ty.clone(), e);
        let e = b.mk_pi(
            lie_group_id,
            BinderInfo::InstImplicit,
            lie_group_g_n.clone(),
            e,
        );
        let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_const(), e);
        let e = b.mk_pi(group_g_id, BinderInfo::InstImplicit, group_g.clone(), e);
        let e = b.mk_pi(ts_g_id, BinderInfo::InstImplicit, ts_g.clone(), e);
        let e = b.mk_pi(g_ty_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.AdjointRep"),
        level_params: vec![u.clone()],
        type_: adjoint_rep_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.adjoint_rep :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   [lg : LieGroup G n] → LieAlgebra G n → (LieAlgebra G n → LieAlgebra G n)
    // The infinitesimal adjoint representation ad_X : 𝔤 → 𝔤
    // ================================================================

    let little_adjoint_type = {
        let mut b = EnvDeclBuilder::new();
        let (g_ty_id, g_ty) = b.fresh_local(type_u.clone());
        let ts_g = Expr::app(topological_space(u_level.clone()), g_ty.clone());
        let (ts_g_id, ts_g_inst) = b.fresh_local(ts_g.clone());
        let group_g = Expr::app(group(u_level.clone()), g_ty.clone());
        let (group_g_id, group_g_inst) = b.fresh_local(group_g.clone());
        let (n_id, n) = b.fresh_local(nat_const());

        let lie_group_g_n = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.LieGroup.LieGroup"),
                            vec![u_level.clone()],
                        ),
                        g_ty.clone(),
                    ),
                    ts_g_inst.clone(),
                ),
                group_g_inst.clone(),
            ),
            n.clone(),
        );
        let (lie_group_id, lie_group_inst) = b.fresh_local(lie_group_g_n.clone());

        let lie_algebra_g_n = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Topology.LieGroup.LieAlgebra"),
                                vec![u_level.clone()],
                            ),
                            g_ty.clone(),
                        ),
                        ts_g_inst.clone(),
                    ),
                    group_g_inst.clone(),
                ),
                n.clone(),
            ),
            lie_group_inst.clone(),
        );

        let (x_id, _x) = b.fresh_local(lie_algebra_g_n.clone());
        let (y_id, _y) = b.fresh_local(lie_algebra_g_n.clone());

        let e = lie_algebra_g_n.clone();
        let e = b.mk_pi(y_id, BinderInfo::Default, lie_algebra_g_n.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Default, lie_algebra_g_n.clone(), e);
        let e = b.mk_pi(
            lie_group_id,
            BinderInfo::InstImplicit,
            lie_group_g_n.clone(),
            e,
        );
        let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_const(), e);
        let e = b.mk_pi(group_g_id, BinderInfo::InstImplicit, group_g.clone(), e);
        let e = b.mk_pi(ts_g_id, BinderInfo::InstImplicit, ts_g.clone(), e);
        let e = b.mk_pi(g_ty_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.adjoint_rep"),
        level_params: vec![u.clone()],
        type_: little_adjoint_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.IsConnected :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   LieGroup G n → Prop
    // ================================================================

    // Helper: build `{G : Type u} → [TS G] → [Group G] → {n : Nat} → LieGroup G n → result`
    // with configurable binder info for the LieGroup arg and configurable result type.
    let build_lie_group_predicate = |lg_binder: BinderInfo, result: Expr| -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (g_id, g) = b.fresh_local(type_u.clone());
        let ts_g_ty = Expr::app(topological_space(u_level.clone()), g.clone());
        let (ts_g_id, ts_g) = b.fresh_local(ts_g_ty.clone());
        let group_g_ty = Expr::app(group(u_level.clone()), g.clone());
        let (group_g_id, group_g) = b.fresh_local(group_g_ty.clone());
        let nat_ty = nat_const();
        let (n_id, n) = b.fresh_local(nat_ty.clone());
        let lg_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.LieGroup.LieGroup"),
                            vec![u_level.clone()],
                        ),
                        g,
                    ),
                    ts_g,
                ),
                group_g,
            ),
            n,
        );
        let (lg_id, _) = b.fresh_local(lg_ty.clone());

        let e = result;
        let e = b.mk_pi(lg_id, lg_binder, lg_ty, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(group_g_id, BinderInfo::InstImplicit, group_g_ty, e);
        let e = b.mk_pi(ts_g_id, BinderInfo::InstImplicit, ts_g_ty, e);
        let e = b.mk_pi(g_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    let is_connected_type = build_lie_group_predicate(BinderInfo::Default, prop.clone());

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.IsConnected"),
        level_params: vec![u.clone()],
        type_: is_connected_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.IsSimplyConnected :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   LieGroup G n → Prop
    // ================================================================

    let is_simply_connected_type = build_lie_group_predicate(BinderInfo::Default, prop.clone());

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.IsSimplyConnected"),
        level_params: vec![u.clone()],
        type_: is_simply_connected_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.IsCompact :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   LieGroup G n → Prop
    // ================================================================

    let is_compact_type = build_lie_group_predicate(BinderInfo::Default, prop.clone());

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.IsCompact"),
        level_params: vec![u.clone()],
        type_: is_compact_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.IsSemisimple :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   LieGroup G n → Prop
    // No non-trivial connected solvable normal subgroups
    // ================================================================

    let is_semisimple_type = build_lie_group_predicate(BinderInfo::Default, prop.clone());

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.IsSemisimple"),
        level_params: vec![u.clone()],
        type_: is_semisimple_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.IsSimple :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   LieGroup G n → Prop
    // No non-trivial connected normal subgroups
    // ================================================================

    let is_simple_type = build_lie_group_predicate(BinderInfo::Default, prop.clone());

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.IsSimple"),
        level_params: vec![u.clone()],
        type_: is_simple_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.IsAbelian :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   LieGroup G n → Prop
    // ================================================================

    let is_abelian_type = build_lie_group_predicate(BinderInfo::Default, prop.clone());

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.IsAbelian"),
        level_params: vec![u.clone()],
        type_: is_abelian_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.UniversalCover :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   LieGroup G n → Type u
    // The simply connected covering Lie group
    // ================================================================

    let universal_cover_type = build_lie_group_predicate(BinderInfo::InstImplicit, type_u.clone());

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.UniversalCover"),
        level_params: vec![u.clone()],
        type_: universal_cover_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.KillingForm :
    //   {G : Type u} → [TopologicalSpace G] → [Group G] → {n : Nat} →
    //   [lg : LieGroup G n] → LieAlgebra G n → LieAlgebra G n → Rat
    // The Killing form B(X, Y) = tr(ad_X ∘ ad_Y)
    // ================================================================

    let killing_form_type = {
        let mut b = EnvDeclBuilder::new();
        let (g_id, g) = b.fresh_local(type_u.clone());
        let ts_g_ty = Expr::app(topological_space(u_level.clone()), g.clone());
        let (ts_g_id, ts_g) = b.fresh_local(ts_g_ty.clone());
        let group_g_ty = Expr::app(group(u_level.clone()), g.clone());
        let (group_g_id, group_g) = b.fresh_local(group_g_ty.clone());
        let nat_ty = nat_const();
        let (n_id, n) = b.fresh_local(nat_ty.clone());
        let lg_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.LieGroup.LieGroup"),
                            vec![u_level.clone()],
                        ),
                        g.clone(),
                    ),
                    ts_g.clone(),
                ),
                group_g.clone(),
            ),
            n.clone(),
        );
        let (lg_id, lg) = b.fresh_local(lg_ty.clone());
        let lie_alg = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Topology.LieGroup.LieAlgebra"),
                                vec![u_level.clone()],
                            ),
                            g,
                        ),
                        ts_g,
                    ),
                    group_g,
                ),
                n,
            ),
            lg,
        );
        let (x_id, _) = b.fresh_local(lie_alg.clone());
        let (y_id, _) = b.fresh_local(lie_alg.clone());

        let e = rat_const();
        let e = b.mk_pi(y_id, BinderInfo::Default, lie_alg.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Default, lie_alg, e);
        let e = b.mk_pi(lg_id, BinderInfo::InstImplicit, lg_ty, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(group_g_id, BinderInfo::InstImplicit, group_g_ty, e);
        let e = b.mk_pi(ts_g_id, BinderInfo::InstImplicit, ts_g_ty, e);
        let e = b.mk_pi(g_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.KillingForm"),
        level_params: vec![u.clone()],
        type_: killing_form_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.killing_form_semisimple :
    //   ∀ {G : Type u} [TopologicalSpace G] [Group G] {n : Nat} (lg : LieGroup G n),
    //   IsSemisimple lg ↔ (∀ X Y, KillingForm X Y = 0 → X = 0 ∨ Y = 0)
    // The Cartan criterion (simplified)
    // ================================================================

    // Simplified version
    let killing_semisimple_type = build_lie_group_predicate(BinderInfo::Default, prop.clone());

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.killing_form_semisimple"),
        level_params: vec![u.clone()],
        type_: killing_semisimple_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.exp_one_param :
    //   ∀ {G : Type u} [TopologicalSpace G] [Group G] {n : Nat} [lg : LieGroup G n]
    //   (X : LieAlgebra G n), OneParameterSubgroup lg (fun t => ExpMap (t • X))
    // One-parameter subgroups are exactly exponentials of Lie algebra elements
    // ================================================================

    let exp_one_param_type = {
        let mut b = EnvDeclBuilder::new();
        let (g_id, g) = b.fresh_local(type_u.clone());
        let ts_g_ty = Expr::app(topological_space(u_level.clone()), g.clone());
        let (ts_g_id, ts_g) = b.fresh_local(ts_g_ty.clone());
        let group_g_ty = Expr::app(group(u_level.clone()), g.clone());
        let (group_g_id, group_g) = b.fresh_local(group_g_ty.clone());
        let nat_ty = nat_const();
        let (n_id, n) = b.fresh_local(nat_ty.clone());
        let lg_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.LieGroup.LieGroup"),
                            vec![u_level.clone()],
                        ),
                        g.clone(),
                    ),
                    ts_g.clone(),
                ),
                group_g.clone(),
            ),
            n.clone(),
        );
        let (lg_id, lg) = b.fresh_local(lg_ty.clone());
        let lie_alg = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Topology.LieGroup.LieAlgebra"),
                                vec![u_level.clone()],
                            ),
                            g,
                        ),
                        ts_g,
                    ),
                    group_g,
                ),
                n,
            ),
            lg,
        );
        let (x_id, _) = b.fresh_local(lie_alg.clone());

        let e = prop.clone();
        let e = b.mk_pi(x_id, BinderInfo::Default, lie_alg, e);
        let e = b.mk_pi(lg_id, BinderInfo::InstImplicit, lg_ty, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(group_g_id, BinderInfo::InstImplicit, group_g_ty, e);
        let e = b.mk_pi(ts_g_id, BinderInfo::InstImplicit, ts_g_ty, e);
        let e = b.mk_pi(g_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.exp_one_param"),
        level_params: vec![u.clone()],
        type_: exp_one_param_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    // ================================================================
    // Topology.LieGroup.LieAlgebraHom :
    //   {G : Type u} → {H : Type v} → [TopologicalSpace G] → [TopologicalSpace H] →
    //   [Group G] → [Group H] → {m n : Nat} → LieGroup G m → LieGroup H n →
    //   (LieAlgebra G m → LieAlgebra H n) → Prop
    // A linear map preserving the Lie bracket
    // ================================================================

    let lie_algebra_hom_type = {
        let mut b = EnvDeclBuilder::new();
        let (g_id, g) = b.fresh_local(type_u.clone());
        let (h_id, h) = b.fresh_local(type_v.clone());
        let ts_g_ty = Expr::app(topological_space(u_level.clone()), g.clone());
        let (ts_g_id, ts_g) = b.fresh_local(ts_g_ty.clone());
        let ts_h_ty = Expr::app(topological_space(v_level.clone()), h.clone());
        let (ts_h_id, ts_h) = b.fresh_local(ts_h_ty.clone());
        let group_g_ty = Expr::app(group(u_level.clone()), g.clone());
        let (group_g_id, group_g) = b.fresh_local(group_g_ty.clone());
        let group_h_ty = Expr::app(group(v_level.clone()), h.clone());
        let (group_h_id, group_h) = b.fresh_local(group_h_ty.clone());
        let nat_ty = nat_const();
        let (m_id, m) = b.fresh_local(nat_ty.clone());
        let (n_id, n) = b.fresh_local(nat_ty.clone());
        let lg_g_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.LieGroup.LieGroup"),
                            vec![u_level.clone()],
                        ),
                        g.clone(),
                    ),
                    ts_g.clone(),
                ),
                group_g.clone(),
            ),
            m.clone(),
        );
        let (lg_g_id, lg_g) = b.fresh_local(lg_g_ty.clone());
        let lg_h_ty = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(
                            Name::from_string("Topology.LieGroup.LieGroup"),
                            vec![v_level.clone()],
                        ),
                        h.clone(),
                    ),
                    ts_h.clone(),
                ),
                group_h.clone(),
            ),
            n.clone(),
        );
        let (lg_h_id, lg_h) = b.fresh_local(lg_h_ty.clone());
        let lie_alg_g = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Topology.LieGroup.LieAlgebra"),
                                vec![u_level.clone()],
                            ),
                            g,
                        ),
                        ts_g,
                    ),
                    group_g,
                ),
                m,
            ),
            lg_g,
        );
        let lie_alg_h = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(
                                Name::from_string("Topology.LieGroup.LieAlgebra"),
                                vec![v_level.clone()],
                            ),
                            h,
                        ),
                        ts_h,
                    ),
                    group_h,
                ),
                n,
            ),
            lg_h,
        );
        let phi_ty = Expr::arrow(lie_alg_g, lie_alg_h);
        let (phi_id, _) = b.fresh_local(phi_ty.clone());

        let e = prop.clone();
        let e = b.mk_pi(phi_id, BinderInfo::Default, phi_ty, e);
        let e = b.mk_pi(lg_h_id, BinderInfo::InstImplicit, lg_h_ty, e);
        let e = b.mk_pi(lg_g_id, BinderInfo::InstImplicit, lg_g_ty, e);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty.clone(), e);
        let e = b.mk_pi(m_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(group_h_id, BinderInfo::InstImplicit, group_h_ty, e);
        let e = b.mk_pi(group_g_id, BinderInfo::InstImplicit, group_g_ty, e);
        let e = b.mk_pi(ts_h_id, BinderInfo::InstImplicit, ts_h_ty, e);
        let e = b.mk_pi(ts_g_id, BinderInfo::InstImplicit, ts_g_ty, e);
        let e = b.mk_pi(h_id, BinderInfo::Implicit, type_v.clone(), e);
        let e = b.mk_pi(g_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    payload.push(ConstantInfo {
        name: Name::from_string("Topology.LieGroup.LieAlgebraHom"),
        level_params: vec![u.clone(), v.clone()],
        type_: lie_algebra_hom_type,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    });

    payload
}
