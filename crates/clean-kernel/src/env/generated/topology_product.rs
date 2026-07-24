// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.ProductTopology cluster declarations (#1444).
//!
//! This module covers the 16 product topology declarations from `init_topology_product`:
//!
//! Dual-universe [u, v]:
//! - Topology.ProductTopology
//! - Topology.ProductTopology.fst_continuous
//! - Topology.ProductTopology.snd_continuous
//! - Topology.ProductTopology.isOpen_prod
//! - Topology.ProductTopology.isClosed_prod
//!
//! Single-universe [u]:
//! - Topology.ProductTopology.continuous_prod_mk
//! - Topology.ProductTopology.prod_continuous
//! - Topology.ProductTopology.prod_homeomorphism
//! - Topology.ProductTopology.isOpen_iff
//! - Topology.ProductTopology.induced_eq
//! - Topology.ProductTopology.isCoarsest
//! - Topology.ProductTopology.prod_assoc
//! - Topology.ProductTopology.prod_connected
//! - Topology.ProductTopology.prod_compact
//! - Topology.ProductTopology.prod_hausdorff
//! - Topology.ProductTopology.diagonal_closed

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.Product";
pub(crate) const DECL_COUNT: usize = 16;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.ProductTopology",
    "Topology.ProductTopology.fst_continuous",
    "Topology.ProductTopology.snd_continuous",
    "Topology.ProductTopology.isOpen_prod",
    "Topology.ProductTopology.isClosed_prod",
    "Topology.ProductTopology.continuous_prod_mk",
    "Topology.ProductTopology.prod_continuous",
    "Topology.ProductTopology.prod_homeomorphism",
    "Topology.ProductTopology.isOpen_iff",
    "Topology.ProductTopology.induced_eq",
    "Topology.ProductTopology.isCoarsest",
    "Topology.ProductTopology.prod_assoc",
    "Topology.ProductTopology.prod_connected",
    "Topology.ProductTopology.prod_compact",
    "Topology.ProductTopology.prod_hausdorff",
    "Topology.ProductTopology.diagonal_closed",
];

/// Shared context for dual-universe product declarations {X : Type u} {Y : Type v}
struct DualCtx {
    u: Name,
    v: Name,
    u_level: Level,
    v_level: Level,
    type_u: Expr,
    type_v: Expr,
    prop: Expr,
}

impl DualCtx {
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

    fn topological_space(&self, lvl: Level) -> Expr {
        Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl])
    }

    fn continuous(&self, lvl1: Level, lvl2: Level) -> Expr {
        Expr::const_(Name::from_string("Topology.Continuous"), vec![lvl1, lvl2])
    }

    fn is_open(&self, lvl: Level) -> Expr {
        Expr::const_(Name::from_string("IsOpen"), vec![lvl])
    }

    fn is_closed(&self, lvl: Level) -> Expr {
        Expr::const_(Name::from_string("IsClosed"), vec![lvl])
    }

    fn prod_type(&self, lvl1: Level, lvl2: Level) -> Expr {
        Expr::const_(Name::from_string("Prod"), vec![lvl1, lvl2])
    }

    fn max_uv(&self) -> Level {
        Level::max(self.u_level.clone(), self.v_level.clone())
    }

    fn prod_xy(&self, x: &Expr, y: &Expr) -> Expr {
        Expr::app(
            Expr::app(
                self.prod_type(self.u_level.clone(), self.v_level.clone()),
                x.clone(),
            ),
            y.clone(),
        )
    }

    fn and_const(&self) -> Expr {
        Expr::const_(Name::from_string("And"), vec![])
    }
}

/// Shared context for single-universe product declarations {X Y : Type u}
struct SingleCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl SingleCtx {
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

    fn topological_space(&self) -> Expr {
        Expr::const_(
            Name::from_string("TopologicalSpace"),
            vec![self.u_level.clone()],
        )
    }

    fn continuous(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Continuous"),
            vec![self.u_level.clone(), self.u_level.clone()],
        )
    }

    fn is_open(&self) -> Expr {
        Expr::const_(Name::from_string("IsOpen"), vec![self.u_level.clone()])
    }

    fn is_closed(&self) -> Expr {
        Expr::const_(Name::from_string("IsClosed"), vec![self.u_level.clone()])
    }

    fn prod_type(&self) -> Expr {
        Expr::const_(
            Name::from_string("Prod"),
            vec![self.u_level.clone(), self.u_level.clone()],
        )
    }

    fn prod_uu(&self, x: &Expr, y: &Expr) -> Expr {
        Expr::app(Expr::app(self.prod_type(), x.clone()), y.clone())
    }

    fn iff_const(&self) -> Expr {
        Expr::const_(Name::from_string("Iff"), vec![])
    }

    fn prod_fst(&self) -> Expr {
        Expr::const_(
            Name::from_string("Prod.fst"),
            vec![self.u_level.clone(), self.u_level.clone()],
        )
    }

    fn prod_snd(&self) -> Expr {
        Expr::const_(
            Name::from_string("Prod.snd"),
            vec![self.u_level.clone(), self.u_level.clone()],
        )
    }

    fn prod_mk(&self) -> Expr {
        Expr::const_(
            Name::from_string("Prod.mk"),
            vec![self.u_level.clone(), self.u_level.clone()],
        )
    }

    fn ts_app(&self, x: &Expr) -> Expr {
        Expr::app(self.topological_space(), x.clone())
    }
}

// ============================================================================
// Dual-universe declarations [u, v]
// ============================================================================

/// Topology.ProductTopology : {X : Type u} → {Y : Type v} →
///   [TopologicalSpace X] → [TopologicalSpace Y] → TopologicalSpace (X × Y)
fn build_product_topology(ctx: &DualCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_v.clone());
    let (ix_id, _) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        x.clone(),
    ));
    let (iy_id, _) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.v_level.clone()),
        y.clone(),
    ));
    let prod_xy = ctx.prod_xy(&x, &y);
    let body = Expr::app(ctx.topological_space(ctx.max_uv()), prod_xy);
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.v_level.clone()), y.clone()),
        body,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_v.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ConstantInfo {
        name: Name::from_string("Topology.ProductTopology"),
        level_params: vec![ctx.u.clone(), ctx.v.clone()],
        type_: b.finish(r),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

/// Topology.ProductTopology.fst_continuous : {X : Type u} → {Y : Type v} →
///   [TopologicalSpace X] → [TopologicalSpace Y] → [TopologicalSpace (X × Y)] →
///   Continuous Prod.fst
fn build_fst_continuous(ctx: &DualCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_v.clone());
    let (ix_id, ix) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        x.clone(),
    ));
    let (iy_id, _) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.v_level.clone()),
        y.clone(),
    ));
    let prod_xy = ctx.prod_xy(&x, &y);
    let (ip_id, ip) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.max_uv()),
        prod_xy.clone(),
    ));
    let fst = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Prod.fst"),
                vec![ctx.u_level.clone(), ctx.v_level.clone()],
            ),
            x.clone(),
        ),
        y.clone(),
    );
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        ctx.continuous(ctx.max_uv(), ctx.u_level.clone()),
                        prod_xy.clone(),
                    ),
                    x.clone(),
                ),
                ip,
            ),
            ix.clone(),
        ),
        fst,
    );
    let r = b.mk_pi(
        ip_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.max_uv()), prod_xy),
        body,
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.v_level.clone()), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_v.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ConstantInfo {
        name: Name::from_string("Topology.ProductTopology.fst_continuous"),
        level_params: vec![ctx.u.clone(), ctx.v.clone()],
        type_: b.finish(r),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

/// Topology.ProductTopology.snd_continuous : {X : Type u} → {Y : Type v} →
///   [TopologicalSpace X] → [TopologicalSpace Y] → [TopologicalSpace (X × Y)] →
///   Continuous Prod.snd
fn build_snd_continuous(ctx: &DualCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_v.clone());
    let (ix_id, _) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        x.clone(),
    ));
    let (iy_id, iy) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.v_level.clone()),
        y.clone(),
    ));
    let prod_xy = ctx.prod_xy(&x, &y);
    let (ip_id, ip) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.max_uv()),
        prod_xy.clone(),
    ));
    let snd = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Prod.snd"),
                vec![ctx.u_level.clone(), ctx.v_level.clone()],
            ),
            x.clone(),
        ),
        y.clone(),
    );
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        ctx.continuous(ctx.max_uv(), ctx.v_level.clone()),
                        prod_xy.clone(),
                    ),
                    y.clone(),
                ),
                ip,
            ),
            iy.clone(),
        ),
        snd,
    );
    let r = b.mk_pi(
        ip_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.max_uv()), prod_xy),
        body,
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.v_level.clone()), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_v.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ConstantInfo {
        name: Name::from_string("Topology.ProductTopology.snd_continuous"),
        level_params: vec![ctx.u.clone(), ctx.v.clone()],
        type_: b.finish(r),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

/// Topology.ProductTopology.isOpen_prod : {X : Type u} → {Y : Type v} →
///   [TopologicalSpace X] → [TopologicalSpace Y] → [TopologicalSpace (X × Y)] →
///   (U : X → Prop) → (V : Y → Prop) → IsOpen U → IsOpen V →
///   IsOpen (fun p => U p.1 ∧ V p.2)
fn build_is_open_prod(ctx: &DualCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_v.clone());
    let (ix_id, ix) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        x.clone(),
    ));
    let (iy_id, iy) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.v_level.clone()),
        y.clone(),
    ));
    let prod_xy = ctx.prod_xy(&x, &y);
    let (ip_id, ip) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.max_uv()),
        prod_xy.clone(),
    ));
    let (uset_id, uset) = b.fresh_local(Expr::arrow(x.clone(), ctx.prop.clone()));
    let (vset_id, vset) = b.fresh_local(Expr::arrow(y.clone(), ctx.prop.clone()));
    let (hu_id, _) = b.fresh_local(Expr::app(
        Expr::app(
            Expr::app(ctx.is_open(ctx.u_level.clone()), x.clone()),
            ix.clone(),
        ),
        uset.clone(),
    ));
    let (hv_id, _) = b.fresh_local(Expr::app(
        Expr::app(
            Expr::app(ctx.is_open(ctx.v_level.clone()), y.clone()),
            iy.clone(),
        ),
        vset.clone(),
    ));
    // Build body: IsOpen (fun p => U p.1 ∧ V p.2)
    let (p_id, p) = b.fresh_local(prod_xy.clone());
    let p_fst = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Prod.fst"),
                    vec![ctx.u_level.clone(), ctx.v_level.clone()],
                ),
                x.clone(),
            ),
            y.clone(),
        ),
        p.clone(),
    );
    let p_snd = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Prod.snd"),
                    vec![ctx.u_level.clone(), ctx.v_level.clone()],
                ),
                x.clone(),
            ),
            y.clone(),
        ),
        p.clone(),
    );
    let u_p_fst = Expr::app(uset.clone(), p_fst);
    let v_p_snd = Expr::app(vset.clone(), p_snd);
    let lam_body = Expr::app(Expr::app(ctx.and_const(), u_p_fst), v_p_snd);
    let prod_set = b.mk_lam(p_id, BinderInfo::Default, prod_xy.clone(), lam_body);
    let body = Expr::app(
        Expr::app(
            Expr::app(ctx.is_open(ctx.max_uv()), prod_xy.clone()),
            ip.clone(),
        ),
        prod_set,
    );
    let r = b.mk_pi(
        hv_id,
        BinderInfo::Default,
        Expr::app(
            Expr::app(
                Expr::app(ctx.is_open(ctx.v_level.clone()), y.clone()),
                iy.clone(),
            ),
            vset.clone(),
        ),
        body,
    );
    let r = b.mk_pi(
        hu_id,
        BinderInfo::Default,
        Expr::app(
            Expr::app(
                Expr::app(ctx.is_open(ctx.u_level.clone()), x.clone()),
                ix.clone(),
            ),
            uset.clone(),
        ),
        r,
    );
    let r = b.mk_pi(
        vset_id,
        BinderInfo::Default,
        Expr::arrow(y.clone(), ctx.prop.clone()),
        r,
    );
    let r = b.mk_pi(
        uset_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), ctx.prop.clone()),
        r,
    );
    let r = b.mk_pi(
        ip_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.max_uv()), prod_xy),
        r,
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.v_level.clone()), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_v.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ConstantInfo {
        name: Name::from_string("Topology.ProductTopology.isOpen_prod"),
        level_params: vec![ctx.u.clone(), ctx.v.clone()],
        type_: b.finish(r),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

/// Topology.ProductTopology.isClosed_prod : {X : Type u} → {Y : Type v} →
///   [TopologicalSpace X] → [TopologicalSpace Y] → [TopologicalSpace (X × Y)] →
///   (C : X → Prop) → (D : Y → Prop) → IsClosed C → IsClosed D →
///   IsClosed (fun p => C p.1 ∧ D p.2)
fn build_is_closed_prod(ctx: &DualCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_v.clone());
    let (ix_id, ix) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        x.clone(),
    ));
    let (iy_id, iy) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.v_level.clone()),
        y.clone(),
    ));
    let prod_xy = ctx.prod_xy(&x, &y);
    let (ip_id, ip) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.max_uv()),
        prod_xy.clone(),
    ));
    let (cset_id, cset) = b.fresh_local(Expr::arrow(x.clone(), ctx.prop.clone()));
    let (dset_id, dset) = b.fresh_local(Expr::arrow(y.clone(), ctx.prop.clone()));
    let (hc_id, _) = b.fresh_local(Expr::app(
        Expr::app(
            Expr::app(ctx.is_closed(ctx.u_level.clone()), x.clone()),
            ix.clone(),
        ),
        cset.clone(),
    ));
    let (hd_id, _) = b.fresh_local(Expr::app(
        Expr::app(
            Expr::app(ctx.is_closed(ctx.v_level.clone()), y.clone()),
            iy.clone(),
        ),
        dset.clone(),
    ));
    // Build body: IsClosed (fun p => C p.1 ∧ D p.2)
    let (p_id, p) = b.fresh_local(prod_xy.clone());
    let p_fst = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Prod.fst"),
                    vec![ctx.u_level.clone(), ctx.v_level.clone()],
                ),
                x.clone(),
            ),
            y.clone(),
        ),
        p.clone(),
    );
    let p_snd = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Prod.snd"),
                    vec![ctx.u_level.clone(), ctx.v_level.clone()],
                ),
                x.clone(),
            ),
            y.clone(),
        ),
        p.clone(),
    );
    let c_p_fst = Expr::app(cset.clone(), p_fst);
    let d_p_snd = Expr::app(dset.clone(), p_snd);
    let lam_body = Expr::app(Expr::app(ctx.and_const(), c_p_fst), d_p_snd);
    let prod_set = b.mk_lam(p_id, BinderInfo::Default, prod_xy.clone(), lam_body);
    let body = Expr::app(
        Expr::app(
            Expr::app(ctx.is_closed(ctx.max_uv()), prod_xy.clone()),
            ip.clone(),
        ),
        prod_set,
    );
    let r = b.mk_pi(
        hd_id,
        BinderInfo::Default,
        Expr::app(
            Expr::app(
                Expr::app(ctx.is_closed(ctx.v_level.clone()), y.clone()),
                iy.clone(),
            ),
            dset.clone(),
        ),
        body,
    );
    let r = b.mk_pi(
        hc_id,
        BinderInfo::Default,
        Expr::app(
            Expr::app(
                Expr::app(ctx.is_closed(ctx.u_level.clone()), x.clone()),
                ix.clone(),
            ),
            cset.clone(),
        ),
        r,
    );
    let r = b.mk_pi(
        dset_id,
        BinderInfo::Default,
        Expr::arrow(y.clone(), ctx.prop.clone()),
        r,
    );
    let r = b.mk_pi(
        cset_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), ctx.prop.clone()),
        r,
    );
    let r = b.mk_pi(
        ip_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.max_uv()), prod_xy),
        r,
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.v_level.clone()), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_v.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ConstantInfo {
        name: Name::from_string("Topology.ProductTopology.isClosed_prod"),
        level_params: vec![ctx.u.clone(), ctx.v.clone()],
        type_: b.finish(r),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

// ============================================================================
// Single-universe declarations [u]
// ============================================================================

/// Topology.ProductTopology.continuous_prod_mk : {X Y Z : Type u} →
///   [TopologicalSpace X] → [TopologicalSpace Y] → [TopologicalSpace Z] →
///   [TopologicalSpace (Y × Z)] →
///   (f : X → Y) → (g : X → Z) →
///   Continuous f → Continuous g → Continuous (fun x => (f x, g x))
fn build_continuous_prod_mk(ctx: &SingleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (z_id, z) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(ctx.ts_app(&x));
    let (iy_id, iy) = b.fresh_local(ctx.ts_app(&y));
    let (iz_id, iz) = b.fresh_local(ctx.ts_app(&z));
    let prod_yz = ctx.prod_uu(&y, &z);
    let (iyz_id, iyz) = b.fresh_local(ctx.ts_app(&prod_yz));
    let (f_id, f) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));
    let (g_id, g) = b.fresh_local(Expr::arrow(x.clone(), z.clone()));
    let (hf_id, _) = b.fresh_local(Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.continuous(), x.clone()), y.clone()),
                ix.clone(),
            ),
            iy.clone(),
        ),
        f.clone(),
    ));
    let (hg_id, _) = b.fresh_local(Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.continuous(), x.clone()), z.clone()),
                ix.clone(),
            ),
            iz.clone(),
        ),
        g.clone(),
    ));
    // Build pair function: fun x_arg => (f x_arg, g x_arg)
    let (xa_id, xa) = b.fresh_local(x.clone());
    let fx = Expr::app(f.clone(), xa.clone());
    let gx = Expr::app(g.clone(), xa.clone());
    let pair_body = Expr::app(
        Expr::app(
            Expr::app(Expr::app(ctx.prod_mk(), y.clone()), z.clone()),
            fx,
        ),
        gx,
    );
    let pair_fn = b.mk_lam(xa_id, BinderInfo::Default, x.clone(), pair_body);
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.continuous(), x.clone()), prod_yz.clone()),
                ix.clone(),
            ),
            iyz.clone(),
        ),
        pair_fn,
    );
    let r = b.mk_pi(
        hg_id,
        BinderInfo::Default,
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(ctx.continuous(), x.clone()), z.clone()),
                    ix.clone(),
                ),
                iz.clone(),
            ),
            g.clone(),
        ),
        body,
    );
    let r = b.mk_pi(
        hf_id,
        BinderInfo::Default,
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(ctx.continuous(), x.clone()), y.clone()),
                    ix.clone(),
                ),
                iy.clone(),
            ),
            f.clone(),
        ),
        r,
    );
    let r = b.mk_pi(
        g_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), z.clone()),
        r,
    );
    let r = b.mk_pi(
        f_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), y.clone()),
        r,
    );
    let r = b.mk_pi(iyz_id, BinderInfo::InstImplicit, ctx.ts_app(&prod_yz), r);
    let r = b.mk_pi(iz_id, BinderInfo::InstImplicit, ctx.ts_app(&z), r);
    let r = b.mk_pi(iy_id, BinderInfo::InstImplicit, ctx.ts_app(&y), r);
    let r = b.mk_pi(ix_id, BinderInfo::InstImplicit, ctx.ts_app(&x), r);
    let r = b.mk_pi(z_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ConstantInfo {
        name: Name::from_string("Topology.ProductTopology.continuous_prod_mk"),
        level_params: vec![ctx.u.clone()],
        type_: b.finish(r),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

/// Topology.ProductTopology.prod_continuous : {X Y X' Y' : Type u} →
///   [inst...] → (f : X → X') → (g : Y → Y') →
///   Continuous f → Continuous g → Continuous (Prod.map f g)
fn build_prod_continuous(ctx: &SingleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (xp_id, xp) = b.fresh_local(ctx.type_u.clone()); // X'
    let (yp_id, yp) = b.fresh_local(ctx.type_u.clone()); // Y'
    let (ix_id, ix) = b.fresh_local(ctx.ts_app(&x));
    let (iy_id, iy) = b.fresh_local(ctx.ts_app(&y));
    let (ixp_id, ixp) = b.fresh_local(ctx.ts_app(&xp));
    let (iyp_id, iyp) = b.fresh_local(ctx.ts_app(&yp));
    let prod_xy = ctx.prod_uu(&x, &y);
    let prod_xpyp = ctx.prod_uu(&xp, &yp);
    let (ixy_id, ixy) = b.fresh_local(ctx.ts_app(&prod_xy));
    let (ixpyp_id, ixpyp) = b.fresh_local(ctx.ts_app(&prod_xpyp));
    let (f_id, f) = b.fresh_local(Expr::arrow(x.clone(), xp.clone()));
    let (g_id, g) = b.fresh_local(Expr::arrow(y.clone(), yp.clone()));
    let (hf_id, _) = b.fresh_local(Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.continuous(), x.clone()), xp.clone()),
                ix.clone(),
            ),
            ixp.clone(),
        ),
        f.clone(),
    ));
    let (hg_id, _) = b.fresh_local(Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.continuous(), y.clone()), yp.clone()),
                iy.clone(),
            ),
            iyp.clone(),
        ),
        g.clone(),
    ));
    // Build prod_map: fun p => (f p.fst, g p.snd)
    let (p_id, p) = b.fresh_local(prod_xy.clone());
    let p_fst = Expr::app(
        Expr::app(Expr::app(ctx.prod_fst(), x.clone()), y.clone()),
        p.clone(),
    );
    let p_snd = Expr::app(
        Expr::app(Expr::app(ctx.prod_snd(), x.clone()), y.clone()),
        p.clone(),
    );
    let f_fst = Expr::app(f.clone(), p_fst);
    let g_snd = Expr::app(g.clone(), p_snd);
    let map_body = Expr::app(
        Expr::app(
            Expr::app(Expr::app(ctx.prod_mk(), xp.clone()), yp.clone()),
            f_fst,
        ),
        g_snd,
    );
    let prod_map = b.mk_lam(p_id, BinderInfo::Default, prod_xy.clone(), map_body);
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(ctx.continuous(), prod_xy.clone()),
                    prod_xpyp.clone(),
                ),
                ixy.clone(),
            ),
            ixpyp.clone(),
        ),
        prod_map,
    );
    let r = b.mk_pi(
        hg_id,
        BinderInfo::Default,
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(ctx.continuous(), y.clone()), yp.clone()),
                    iy.clone(),
                ),
                iyp.clone(),
            ),
            g.clone(),
        ),
        body,
    );
    let r = b.mk_pi(
        hf_id,
        BinderInfo::Default,
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(ctx.continuous(), x.clone()), xp.clone()),
                    ix.clone(),
                ),
                ixp.clone(),
            ),
            f.clone(),
        ),
        r,
    );
    let r = b.mk_pi(
        g_id,
        BinderInfo::Default,
        Expr::arrow(y.clone(), yp.clone()),
        r,
    );
    let r = b.mk_pi(
        f_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), xp.clone()),
        r,
    );
    let r = b.mk_pi(
        ixpyp_id,
        BinderInfo::InstImplicit,
        ctx.ts_app(&prod_xpyp),
        r,
    );
    let r = b.mk_pi(ixy_id, BinderInfo::InstImplicit, ctx.ts_app(&prod_xy), r);
    let r = b.mk_pi(iyp_id, BinderInfo::InstImplicit, ctx.ts_app(&yp), r);
    let r = b.mk_pi(ixp_id, BinderInfo::InstImplicit, ctx.ts_app(&xp), r);
    let r = b.mk_pi(iy_id, BinderInfo::InstImplicit, ctx.ts_app(&y), r);
    let r = b.mk_pi(ix_id, BinderInfo::InstImplicit, ctx.ts_app(&x), r);
    let r = b.mk_pi(yp_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(xp_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ConstantInfo {
        name: Name::from_string("Topology.ProductTopology.prod_continuous"),
        level_params: vec![ctx.u.clone()],
        type_: b.finish(r),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

/// Topology.ProductTopology.prod_homeomorphism : {X Y : Type u} →
///   [inst...] → (f : X×Y → Y×X) → (g : Y×X → X×Y) →
///   Homeomorphism (X × Y) (Y × X) f g
fn build_prod_homeomorphism(ctx: &SingleCtx) -> ConstantInfo {
    let homeomorphism = Expr::const_(
        Name::from_string("Topology.Homeomorphism"),
        vec![ctx.u_level.clone(), ctx.u_level.clone()],
    );
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, _) = b.fresh_local(ctx.ts_app(&x));
    let (iy_id, _) = b.fresh_local(ctx.ts_app(&y));
    let prod_xy = ctx.prod_uu(&x, &y);
    let prod_yx = ctx.prod_uu(&y, &x);
    let (ixy_id, ixy) = b.fresh_local(ctx.ts_app(&prod_xy));
    let (iyx_id, iyx) = b.fresh_local(ctx.ts_app(&prod_yx));
    let f_ty = Expr::arrow(prod_xy.clone(), prod_yx.clone());
    let g_ty = Expr::arrow(prod_yx.clone(), prod_xy.clone());
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(homeomorphism, prod_xy.clone()), prod_yx.clone()),
                    ixy.clone(),
                ),
                iyx.clone(),
            ),
            f,
        ),
        g,
    );
    let r = b.mk_pi(g_id, BinderInfo::Default, g_ty, body);
    let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
    let r = b.mk_pi(iyx_id, BinderInfo::InstImplicit, ctx.ts_app(&prod_yx), r);
    let r = b.mk_pi(ixy_id, BinderInfo::InstImplicit, ctx.ts_app(&prod_xy), r);
    let r = b.mk_pi(iy_id, BinderInfo::InstImplicit, ctx.ts_app(&y), r);
    let r = b.mk_pi(ix_id, BinderInfo::InstImplicit, ctx.ts_app(&x), r);
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ConstantInfo {
        name: Name::from_string("Topology.ProductTopology.prod_homeomorphism"),
        level_params: vec![ctx.u.clone()],
        type_: b.finish(r),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

/// Topology.ProductTopology.isOpen_iff : {X Y : Type u} →
///   [TopologicalSpace X] → [TopologicalSpace Y] → [TopologicalSpace (X × Y)] →
///   (W : X × Y → Prop) → Iff (IsOpen W) (IsOpen W)
fn build_is_open_iff(ctx: &SingleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, _) = b.fresh_local(ctx.ts_app(&x));
    let (iy_id, _) = b.fresh_local(ctx.ts_app(&y));
    let prod_xy = ctx.prod_uu(&x, &y);
    let (ip_id, ip) = b.fresh_local(ctx.ts_app(&prod_xy));
    let (w_id, w) = b.fresh_local(Expr::arrow(prod_xy.clone(), ctx.prop.clone()));
    let is_open_w = Expr::app(
        Expr::app(Expr::app(ctx.is_open(), prod_xy.clone()), ip.clone()),
        w.clone(),
    );
    let body = Expr::app(Expr::app(ctx.iff_const(), is_open_w.clone()), is_open_w);
    let r = b.mk_pi(
        w_id,
        BinderInfo::Default,
        Expr::arrow(prod_xy.clone(), ctx.prop.clone()),
        body,
    );
    let r = b.mk_pi(ip_id, BinderInfo::InstImplicit, ctx.ts_app(&prod_xy), r);
    let r = b.mk_pi(iy_id, BinderInfo::InstImplicit, ctx.ts_app(&y), r);
    let r = b.mk_pi(ix_id, BinderInfo::InstImplicit, ctx.ts_app(&x), r);
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ConstantInfo {
        name: Name::from_string("Topology.ProductTopology.isOpen_iff"),
        level_params: vec![ctx.u.clone()],
        type_: b.finish(r),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

/// Topology.ProductTopology.induced_eq : {X Y : Type u} →
///   [TopologicalSpace X] → [TopologicalSpace Y] →
///   Eq (ProductTopology X Y ix iy) (ProductTopology X Y ix iy)
fn build_induced_eq(ctx: &SingleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(ctx.ts_app(&x));
    let (iy_id, iy) = b.fresh_local(ctx.ts_app(&y));
    let prod_xy = ctx.prod_uu(&x, &y);
    let prod_topology = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Topology.ProductTopology"),
                        vec![ctx.u_level.clone(), ctx.u_level.clone()],
                    ),
                    x.clone(),
                ),
                y.clone(),
            ),
            ix.clone(),
        ),
        iy.clone(),
    );
    let ts_prod = Expr::app(ctx.topological_space(), prod_xy);
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Eq"),
                    vec![Level::succ(ctx.u_level.clone())],
                ),
                ts_prod,
            ),
            prod_topology.clone(),
        ),
        prod_topology,
    );
    let r = b.mk_pi(iy_id, BinderInfo::InstImplicit, ctx.ts_app(&y), body);
    let r = b.mk_pi(ix_id, BinderInfo::InstImplicit, ctx.ts_app(&x), r);
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ConstantInfo {
        name: Name::from_string("Topology.ProductTopology.induced_eq"),
        level_params: vec![ctx.u.clone()],
        type_: b.finish(r),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

/// Topology.ProductTopology.isCoarsest : {X Y : Type u} →
///   [TopologicalSpace X] → [TopologicalSpace Y] →
///   (τ : TopologicalSpace (X × Y)) → Prop → Prop → Prop
fn build_is_coarsest(ctx: &SingleCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, _) = b.fresh_local(ctx.ts_app(&x));
    let (iy_id, _) = b.fresh_local(ctx.ts_app(&y));
    let prod_xy = ctx.prod_uu(&x, &y);
    let (tau_id, _) = b.fresh_local(ctx.ts_app(&prod_xy));
    let (h1_id, _) = b.fresh_local(ctx.prop.clone());
    let (h2_id, _) = b.fresh_local(ctx.prop.clone());
    let body = ctx.prop.clone();
    let r = b.mk_pi(h2_id, BinderInfo::Default, ctx.prop.clone(), body);
    let r = b.mk_pi(h1_id, BinderInfo::Default, ctx.prop.clone(), r);
    let prod_xy2 = ctx.prod_uu(&x, &y);
    let r = b.mk_pi(tau_id, BinderInfo::Default, ctx.ts_app(&prod_xy2), r);
    let r = b.mk_pi(iy_id, BinderInfo::InstImplicit, ctx.ts_app(&y), r);
    let r = b.mk_pi(ix_id, BinderInfo::InstImplicit, ctx.ts_app(&x), r);
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ConstantInfo {
        name: Name::from_string("Topology.ProductTopology.isCoarsest"),
        level_params: vec![ctx.u.clone()],
        type_: b.finish(r),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

/// Topology.ProductTopology.prod_assoc : {X Y Z : Type u} →
///   [inst...] → (f : (X×Y)×Z → X×(Y×Z)) → (g : X×(Y×Z) → (X×Y)×Z) →
///   Homeomorphism ((X × Y) × Z) (X × (Y × Z)) f g
fn build_prod_assoc(ctx: &SingleCtx) -> ConstantInfo {
    let homeomorphism = Expr::const_(
        Name::from_string("Topology.Homeomorphism"),
        vec![ctx.u_level.clone(), ctx.u_level.clone()],
    );
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (z_id, z) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, _) = b.fresh_local(ctx.ts_app(&x));
    let (iy_id, _) = b.fresh_local(ctx.ts_app(&y));
    let (iz_id, _) = b.fresh_local(ctx.ts_app(&z));
    let prod_xy = ctx.prod_uu(&x, &y);
    let prod_yz = ctx.prod_uu(&y, &z);
    let (ixy_id, _) = b.fresh_local(ctx.ts_app(&prod_xy));
    let (iyz_id, _) = b.fresh_local(ctx.ts_app(&prod_yz));
    let prod_xyz_left = ctx.prod_uu(&prod_xy, &z);
    let prod_xyz_right = ctx.prod_uu(&x, &prod_yz);
    let (ixyz_id, ixyz) = b.fresh_local(ctx.ts_app(&prod_xyz_left));
    let (ix_yz_id, ix_yz) = b.fresh_local(ctx.ts_app(&prod_xyz_right));
    let f_ty = Expr::arrow(prod_xyz_left.clone(), prod_xyz_right.clone());
    let g_ty = Expr::arrow(prod_xyz_right.clone(), prod_xyz_left.clone());
    let (f_id, f) = b.fresh_local(f_ty.clone());
    let (g_id, g) = b.fresh_local(g_ty.clone());
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(homeomorphism, prod_xyz_left.clone()),
                        prod_xyz_right.clone(),
                    ),
                    ixyz.clone(),
                ),
                ix_yz.clone(),
            ),
            f,
        ),
        g,
    );
    let r = b.mk_pi(g_id, BinderInfo::Default, g_ty, body);
    let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
    let r = b.mk_pi(
        ix_yz_id,
        BinderInfo::InstImplicit,
        ctx.ts_app(&prod_xyz_right),
        r,
    );
    let r = b.mk_pi(
        ixyz_id,
        BinderInfo::InstImplicit,
        ctx.ts_app(&prod_xyz_left),
        r,
    );
    let r = b.mk_pi(iyz_id, BinderInfo::InstImplicit, ctx.ts_app(&prod_yz), r);
    let r = b.mk_pi(ixy_id, BinderInfo::InstImplicit, ctx.ts_app(&prod_xy), r);
    let r = b.mk_pi(iz_id, BinderInfo::InstImplicit, ctx.ts_app(&z), r);
    let r = b.mk_pi(iy_id, BinderInfo::InstImplicit, ctx.ts_app(&y), r);
    let r = b.mk_pi(ix_id, BinderInfo::InstImplicit, ctx.ts_app(&x), r);
    let r = b.mk_pi(z_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ConstantInfo {
        name: Name::from_string("Topology.ProductTopology.prod_assoc"),
        level_params: vec![ctx.u.clone()],
        type_: b.finish(r),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

/// Helper for prod_connected/compact/hausdorff which share the same shape:
///   {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] →
///   [TopologicalSpace (X × Y)] → Property X → Property Y → Property (X × Y)
fn build_property_preserving(ctx: &SingleCtx, name: &str, property_name: &str) -> ConstantInfo {
    let property = |lvl: Level| Expr::const_(Name::from_string(property_name), vec![lvl]);
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(ctx.ts_app(&x));
    let (iy_id, iy) = b.fresh_local(ctx.ts_app(&y));
    let prod_xy = ctx.prod_uu(&x, &y);
    let (ip_id, ip) = b.fresh_local(ctx.ts_app(&prod_xy));
    let (hx_id, _) = b.fresh_local(Expr::app(
        Expr::app(property(ctx.u_level.clone()), x.clone()),
        ix.clone(),
    ));
    let (hy_id, _) = b.fresh_local(Expr::app(
        Expr::app(property(ctx.u_level.clone()), y.clone()),
        iy.clone(),
    ));
    let body = Expr::app(
        Expr::app(property(ctx.u_level.clone()), prod_xy.clone()),
        ip.clone(),
    );
    let r = b.mk_pi(
        hy_id,
        BinderInfo::Default,
        Expr::app(
            Expr::app(property(ctx.u_level.clone()), y.clone()),
            iy.clone(),
        ),
        body,
    );
    let r = b.mk_pi(
        hx_id,
        BinderInfo::Default,
        Expr::app(
            Expr::app(property(ctx.u_level.clone()), x.clone()),
            ix.clone(),
        ),
        r,
    );
    let r = b.mk_pi(ip_id, BinderInfo::InstImplicit, ctx.ts_app(&prod_xy), r);
    let r = b.mk_pi(iy_id, BinderInfo::InstImplicit, ctx.ts_app(&y), r);
    let r = b.mk_pi(ix_id, BinderInfo::InstImplicit, ctx.ts_app(&x), r);
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ConstantInfo {
        name: Name::from_string(name),
        level_params: vec![ctx.u.clone()],
        type_: b.finish(r),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

/// Topology.ProductTopology.diagonal_closed : {X : Type u} →
///   [TopologicalSpace X] → [TopologicalSpace (X × X)] →
///   Hausdorff X → IsClosed (diagonal X)
fn build_diagonal_closed(ctx: &SingleCtx) -> ConstantInfo {
    let hausdorff = Expr::const_(
        Name::from_string("Topology.Hausdorff"),
        vec![ctx.u_level.clone()],
    );
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(ctx.ts_app(&x));
    let prod_xx = ctx.prod_uu(&x, &x);
    let (ixx_id, ixx) = b.fresh_local(ctx.ts_app(&prod_xx));
    let (h_id, _) = b.fresh_local(Expr::app(
        Expr::app(hausdorff.clone(), x.clone()),
        ix.clone(),
    ));
    // Build diagonal predicate: fun p => p.1 = p.2
    let (p_id, p) = b.fresh_local(prod_xx.clone());
    let p_fst = Expr::app(
        Expr::app(Expr::app(ctx.prod_fst(), x.clone()), x.clone()),
        p.clone(),
    );
    let p_snd = Expr::app(
        Expr::app(Expr::app(ctx.prod_snd(), x.clone()), x.clone()),
        p.clone(),
    );
    let eq_body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Eq"),
                    vec![Level::succ(ctx.u_level.clone())],
                ),
                x.clone(),
            ),
            p_fst,
        ),
        p_snd,
    );
    let diagonal = b.mk_lam(p_id, BinderInfo::Default, prod_xx.clone(), eq_body);
    let body = Expr::app(
        Expr::app(Expr::app(ctx.is_closed(), prod_xx.clone()), ixx.clone()),
        diagonal,
    );
    let r = b.mk_pi(
        h_id,
        BinderInfo::Default,
        Expr::app(Expr::app(hausdorff, x.clone()), ix.clone()),
        body,
    );
    let r = b.mk_pi(ixx_id, BinderInfo::InstImplicit, ctx.ts_app(&prod_xx), r);
    let r = b.mk_pi(ix_id, BinderInfo::InstImplicit, ctx.ts_app(&x), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ConstantInfo {
        name: Name::from_string("Topology.ProductTopology.diagonal_closed"),
        level_params: vec![ctx.u.clone()],
        type_: b.finish(r),
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

/// Build the complete payload of 16 product topology declarations.
pub(crate) fn payload() -> Vec<ConstantInfo> {
    let dual = DualCtx::new();
    let single = SingleCtx::new();

    let p = vec![
        // Dual-universe [u, v]
        build_product_topology(&dual),
        build_fst_continuous(&dual),
        build_snd_continuous(&dual),
        build_is_open_prod(&dual),
        build_is_closed_prod(&dual),
        // Single-universe [u]
        build_continuous_prod_mk(&single),
        build_prod_continuous(&single),
        build_prod_homeomorphism(&single),
        build_is_open_iff(&single),
        build_induced_eq(&single),
        build_is_coarsest(&single),
        build_prod_assoc(&single),
        build_property_preserving(
            &single,
            "Topology.ProductTopology.prod_connected",
            "Topology.Connected",
        ),
        build_property_preserving(
            &single,
            "Topology.ProductTopology.prod_compact",
            "Topology.Compact",
        ),
        build_property_preserving(
            &single,
            "Topology.ProductTopology.prod_hausdorff",
            "Topology.Hausdorff",
        ),
        build_diagonal_closed(&single),
    ];
    debug_assert_eq!(p.len(), DECL_COUNT, "payload size mismatch for {NAMESPACE}");
    debug_assert_eq!(
        p.iter().map(|c| c.name.to_string()).collect::<Vec<_>>(),
        DECL_NAMES.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
        "payload names mismatch for {NAMESPACE}"
    );
    p
}
