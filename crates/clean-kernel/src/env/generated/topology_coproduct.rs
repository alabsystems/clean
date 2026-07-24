// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.CoproductTopology namespace (#1444).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.CoproductTopology";
pub(crate) const DECL_COUNT: usize = 14;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.CoproductTopology",
    "Topology.CoproductTopology.isOpen_iff",
    "Topology.CoproductTopology.isClosed_iff",
    "Topology.CoproductTopology.inl_continuous",
    "Topology.CoproductTopology.inr_continuous",
    "Topology.CoproductTopology.elim_continuous",
    "Topology.CoproductTopology.universal",
    "Topology.CoproductTopology.swap_homeomorphism",
    "Topology.CoproductTopology.assoc_homeomorphism",
    "Topology.CoproductTopology.connected_iff",
    "Topology.CoproductTopology.compact_iff",
    "Topology.CoproductTopology.sum_map_continuous",
    "Topology.CoproductTopology.cover_by_components",
    "Topology.CoproductTopology.disjoint_union_subspace",
];

struct CoprodCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl CoprodCtx {
    fn new() -> Self {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        Self {
            type_u: Expr::sort(Level::succ(u_level.clone())),
            prop: Expr::sort(Level::zero()),
            u,
            u_level,
        }
    }

    fn topological_space(&self, x: Expr) -> Expr {
        Expr::app(
            Expr::const_(
                Name::from_string("TopologicalSpace"),
                vec![self.u_level.clone()],
            ),
            x,
        )
    }

    fn sum_type(&self, x: Expr, y: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Sum"),
                    vec![self.u_level.clone(), self.u_level.clone()],
                ),
                x,
            ),
            y,
        )
    }

    fn continuous(&self, dom: Expr, cod: Expr, ts_dom: Expr, ts_cod: Expr, f: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                Name::from_string("Topology.Continuous"),
                vec![self.u_level.clone(), self.u_level.clone()],
            ),
            [dom, cod, ts_dom, ts_cod, f],
        )
    }

    fn to_axiom(&self, name: &str, type_: Expr) -> ConstantInfo {
        ConstantInfo {
            name: Name::from_string(name),
            level_params: vec![self.u.clone()],
            type_,
            value: None,
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            kind: ConstantKind::Axiom,
        }
    }

    /// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] → Prop
    fn build_xy_ts_prop(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (y_id, y) = b.fresh_local(self.type_u.clone());
        let tsx_ty = self.topological_space(x);
        let (tsx_id, _) = b.fresh_local(tsx_ty.clone());
        let tsy_ty = self.topological_space(y);
        let (tsy_id, _) = b.fresh_local(tsy_ty.clone());
        let e = b.mk_pi(tsy_id, BinderInfo::InstImplicit, tsy_ty, self.prop.clone());
        let e = b.mk_pi(tsx_id, BinderInfo::InstImplicit, tsx_ty, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, self.type_u.clone(), e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// {X Y : Type u} → [TS X] → [TS Y] → [TS (Sum X Y)] → (Sum X Y → Prop) → Prop
    fn build_xy_sum_ts_set_prop(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (y_id, y) = b.fresh_local(self.type_u.clone());
        let tsx_ty = self.topological_space(x.clone());
        let (tsx_id, _) = b.fresh_local(tsx_ty.clone());
        let tsy_ty = self.topological_space(y.clone());
        let (tsy_id, _) = b.fresh_local(tsy_ty.clone());
        let sum_xy = self.sum_type(x, y);
        let tsxy_ty = self.topological_space(sum_xy.clone());
        let (tsxy_id, _) = b.fresh_local(tsxy_ty.clone());
        let s_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (a_id, _) = c.fresh_local(sum_xy.clone());
            let r = c.mk_pi(a_id, BinderInfo::Default, sum_xy, self.prop.clone());
            c.finish_child(r)
        };
        let (s_id, _) = b.fresh_local(s_ty.clone());
        let e = b.mk_pi(s_id, BinderInfo::Default, s_ty, self.prop.clone());
        let e = b.mk_pi(tsxy_id, BinderInfo::InstImplicit, tsxy_ty, e);
        let e = b.mk_pi(tsy_id, BinderInfo::InstImplicit, tsy_ty, e);
        let e = b.mk_pi(tsx_id, BinderInfo::InstImplicit, tsx_ty, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, self.type_u.clone(), e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = CoprodCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    // CoproductTopology : {X Y : Type u} → [TS X] → [TS Y] → TopologicalSpace (Sum X Y)
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(ctx.type_u.clone());
        let (y_id, y) = b.fresh_local(ctx.type_u.clone());
        let tsx_ty = ctx.topological_space(x.clone());
        let (tsx_id, _) = b.fresh_local(tsx_ty.clone());
        let tsy_ty = ctx.topological_space(y.clone());
        let (tsy_id, _) = b.fresh_local(tsy_ty.clone());
        let sum_xy = ctx.sum_type(x, y);
        let body = ctx.topological_space(sum_xy);
        let e = b.mk_pi(tsy_id, BinderInfo::InstImplicit, tsy_ty, body);
        let e = b.mk_pi(tsx_id, BinderInfo::InstImplicit, tsx_ty, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom("Topology.CoproductTopology", b.finish(e)));
    }

    // isOpen_iff, isClosed_iff: {X Y} → [TS X] → [TS Y] → [TS (Sum X Y)] → (Sum X Y → Prop) → Prop
    let sum_set_prop = ctx.build_xy_sum_ts_set_prop();
    decls.push(ctx.to_axiom(
        "Topology.CoproductTopology.isOpen_iff",
        sum_set_prop.clone(),
    ));
    decls.push(ctx.to_axiom("Topology.CoproductTopology.isClosed_iff", sum_set_prop));

    // inl_continuous: {X Y} → [tsx] → [tsy] → [tsxy] → Continuous X (Sum X Y) tsx tsxy (Sum.inl)
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(ctx.type_u.clone());
        let (y_id, y) = b.fresh_local(ctx.type_u.clone());
        let tsx_ty = ctx.topological_space(x.clone());
        let (tsx_id, tsx) = b.fresh_local(tsx_ty.clone());
        let tsy_ty = ctx.topological_space(y.clone());
        let (tsy_id, _) = b.fresh_local(tsy_ty.clone());
        let sum_xy = ctx.sum_type(x.clone(), y.clone());
        let tsxy_ty = ctx.topological_space(sum_xy.clone());
        let (tsxy_id, tsxy) = b.fresh_local(tsxy_ty.clone());
        let inl_fn = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Sum.inl"),
                    vec![ctx.u_level.clone(), ctx.u_level.clone()],
                ),
                x.clone(),
            ),
            y,
        );
        let body = ctx.continuous(x, sum_xy, tsx, tsxy, inl_fn);
        let e = b.mk_pi(tsxy_id, BinderInfo::InstImplicit, tsxy_ty, body);
        let e = b.mk_pi(tsy_id, BinderInfo::InstImplicit, tsy_ty, e);
        let e = b.mk_pi(tsx_id, BinderInfo::InstImplicit, tsx_ty, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom("Topology.CoproductTopology.inl_continuous", b.finish(e)));
    }

    // inr_continuous: {X Y} → [tsx] → [tsy] → [tsxy] → Continuous Y (Sum X Y) tsy tsxy (Sum.inr)
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(ctx.type_u.clone());
        let (y_id, y) = b.fresh_local(ctx.type_u.clone());
        let tsx_ty = ctx.topological_space(x.clone());
        let (tsx_id, _) = b.fresh_local(tsx_ty.clone());
        let tsy_ty = ctx.topological_space(y.clone());
        let (tsy_id, tsy) = b.fresh_local(tsy_ty.clone());
        let sum_xy = ctx.sum_type(x.clone(), y.clone());
        let tsxy_ty = ctx.topological_space(sum_xy.clone());
        let (tsxy_id, tsxy) = b.fresh_local(tsxy_ty.clone());
        let inr_fn = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Sum.inr"),
                    vec![ctx.u_level.clone(), ctx.u_level.clone()],
                ),
                x,
            ),
            y.clone(),
        );
        let body = ctx.continuous(y, sum_xy, tsy, tsxy, inr_fn);
        let e = b.mk_pi(tsxy_id, BinderInfo::InstImplicit, tsxy_ty, body);
        let e = b.mk_pi(tsy_id, BinderInfo::InstImplicit, tsy_ty, e);
        let e = b.mk_pi(tsx_id, BinderInfo::InstImplicit, tsx_ty, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom("Topology.CoproductTopology.inr_continuous", b.finish(e)));
    }

    // elim_continuous: {X Y Z} → [TS X] → [TS Y] → [TS Z] → [TS (Sum X Y)] → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(ctx.type_u.clone());
        let (y_id, y) = b.fresh_local(ctx.type_u.clone());
        let (z_id, z) = b.fresh_local(ctx.type_u.clone());
        let tsx_ty = ctx.topological_space(x.clone());
        let (tsx_id, _) = b.fresh_local(tsx_ty.clone());
        let tsy_ty = ctx.topological_space(y.clone());
        let (tsy_id, _) = b.fresh_local(tsy_ty.clone());
        let tsz_ty = ctx.topological_space(z);
        let (tsz_id, _) = b.fresh_local(tsz_ty.clone());
        let sum_xy = ctx.sum_type(x, y);
        let tsxy_ty = ctx.topological_space(sum_xy);
        let (tsxy_id, _) = b.fresh_local(tsxy_ty.clone());
        let e = b.mk_pi(tsxy_id, BinderInfo::InstImplicit, tsxy_ty, ctx.prop.clone());
        let e = b.mk_pi(tsz_id, BinderInfo::InstImplicit, tsz_ty, e);
        let e = b.mk_pi(tsy_id, BinderInfo::InstImplicit, tsy_ty, e);
        let e = b.mk_pi(tsx_id, BinderInfo::InstImplicit, tsx_ty, e);
        let e = b.mk_pi(z_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom("Topology.CoproductTopology.elim_continuous", b.finish(e)));
    }

    // universal: {X Y} → [TS X] → [TS Y] → Prop
    decls.push(ctx.to_axiom(
        "Topology.CoproductTopology.universal",
        ctx.build_xy_ts_prop(),
    ));

    // swap_homeomorphism: {X Y} → [TS X] → [TS Y] → [TS (Sum X Y)] → [TS (Sum Y X)] →
    //   (Sum X Y → Sum Y X) → (Sum Y X → Sum X Y) →
    //   Homeomorphism (Sum X Y) (Sum Y X) inst_xy inst_yx swap inv
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(ctx.type_u.clone());
        let (y_id, y) = b.fresh_local(ctx.type_u.clone());
        let ix_ty = ctx.topological_space(x.clone());
        let (ix_id, _) = b.fresh_local(ix_ty.clone());
        let iy_ty = ctx.topological_space(y.clone());
        let (iy_id, _) = b.fresh_local(iy_ty.clone());
        let sum_xy = ctx.sum_type(x.clone(), y.clone());
        let sum_yx = ctx.sum_type(y, x);
        let ixy_ty = ctx.topological_space(sum_xy.clone());
        let (ixy_id, ixy) = b.fresh_local(ixy_ty.clone());
        let iyx_ty = ctx.topological_space(sum_yx.clone());
        let (iyx_id, iyx) = b.fresh_local(iyx_ty.clone());
        let swap_ty = Expr::arrow(sum_xy.clone(), sum_yx.clone());
        let inv_swap_ty = Expr::arrow(sum_yx.clone(), sum_xy.clone());
        let (swap_id, swap) = b.fresh_local(swap_ty.clone());
        let (inv_id, inv) = b.fresh_local(inv_swap_ty.clone());
        let body = Expr::apps(
            Expr::const_(
                Name::from_string("Topology.Homeomorphism"),
                vec![ctx.u_level.clone(), ctx.u_level.clone()],
            ),
            [sum_xy, sum_yx, ixy, iyx, swap, inv],
        );
        let e = b.mk_pi(inv_id, BinderInfo::Default, inv_swap_ty, body);
        let e = b.mk_pi(swap_id, BinderInfo::Default, swap_ty, e);
        let e = b.mk_pi(iyx_id, BinderInfo::InstImplicit, iyx_ty, e);
        let e = b.mk_pi(ixy_id, BinderInfo::InstImplicit, ixy_ty, e);
        let e = b.mk_pi(iy_id, BinderInfo::InstImplicit, iy_ty, e);
        let e = b.mk_pi(ix_id, BinderInfo::InstImplicit, ix_ty, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom("Topology.CoproductTopology.swap_homeomorphism", b.finish(e)));
    }

    // assoc_homeomorphism: {X Y Z} → [TS X] → [TS Y] → [TS Z] → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(ctx.type_u.clone());
        let (y_id, y) = b.fresh_local(ctx.type_u.clone());
        let (z_id, z) = b.fresh_local(ctx.type_u.clone());
        let tsx_ty = ctx.topological_space(x);
        let (tsx_id, _) = b.fresh_local(tsx_ty.clone());
        let tsy_ty = ctx.topological_space(y);
        let (tsy_id, _) = b.fresh_local(tsy_ty.clone());
        let tsz_ty = ctx.topological_space(z);
        let (tsz_id, _) = b.fresh_local(tsz_ty.clone());
        let e = b.mk_pi(tsz_id, BinderInfo::InstImplicit, tsz_ty, ctx.prop.clone());
        let e = b.mk_pi(tsy_id, BinderInfo::InstImplicit, tsy_ty, e);
        let e = b.mk_pi(tsx_id, BinderInfo::InstImplicit, tsx_ty, e);
        let e = b.mk_pi(z_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
        decls.push(ctx.to_axiom(
            "Topology.CoproductTopology.assoc_homeomorphism",
            b.finish(e),
        ));
    }

    // connected_iff, compact_iff, sum_map_continuous, cover_by_components, disjoint_union_subspace:
    // all {X Y} → [TS X] → [TS Y] → Prop
    let xy_ts_prop = ctx.build_xy_ts_prop();
    for name in [
        "Topology.CoproductTopology.connected_iff",
        "Topology.CoproductTopology.compact_iff",
        "Topology.CoproductTopology.sum_map_continuous",
        "Topology.CoproductTopology.cover_by_components",
        "Topology.CoproductTopology.disjoint_union_subspace",
    ] {
        decls.push(ctx.to_axiom(name, xy_ts_prop.clone()));
    }

    debug_assert_eq!(
        decls.len(),
        DECL_COUNT,
        "payload size mismatch for {NAMESPACE}"
    );
    debug_assert_eq!(
        decls.iter().map(|c| c.name.to_string()).collect::<Vec<_>>(),
        DECL_NAMES.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
        "payload names mismatch for {NAMESPACE}"
    );

    decls
}
