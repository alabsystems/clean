// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.QuotientTopology namespace (#1444).
//!
//! Migrated from handwritten `add_decl` calls in `topology_construct.rs`.
//! All 15 declarations use `EnvDeclBuilder` to avoid raw de Bruijn index arithmetic.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.QuotientTopology";
pub(crate) const DECL_COUNT: usize = 15;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.QuotientTopology",
    "Topology.QuotientTopology.isOpen_iff",
    "Topology.QuotientTopology.isClosed_iff",
    "Topology.IsQuotientMap",
    "Topology.IsQuotientMap.continuous",
    "Topology.IsQuotientMap.isOpen_preimage",
    "Topology.QuotientTopology.continuous_iff",
    "Topology.QuotientTopology.mk_continuous",
    "Topology.IsQuotientMap.comp",
    "Topology.quotient_map_of_surjective_continuous_open",
    "Topology.IsOpenMap",
    "Topology.IsClosedMap",
    "Topology.quotient_map_of_surjective_continuous_closed",
    "Topology.QuotientTopology.coinduced_eq",
    "Topology.QuotientTopology.isFinest",
];

/// Shared universe/type context for quotient topology declarations.
struct QuotientCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl QuotientCtx {
    fn new() -> Self {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let prop = Expr::sort(Level::zero());
        Self {
            u,
            u_level,
            type_u,
            prop,
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

    fn iff_const(&self) -> Expr {
        Expr::const_(Name::from_string("Iff"), vec![])
    }

    fn is_quotient_map(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.IsQuotientMap"),
            vec![self.u_level.clone()],
        )
    }

    fn to_axiom_info(&self, name: &str, type_: Expr) -> ConstantInfo {
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
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = QuotientCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    decls.push(build_quotient_topology_type(&ctx));
    decls.push(build_is_open_iff_type(&ctx));
    decls.push(build_is_closed_iff_type(&ctx));
    decls.push(build_is_quotient_map_type(&ctx));
    decls.push(build_qm_continuous_type(&ctx));
    decls.push(build_qm_is_open_preimage_type(&ctx));
    decls.push(build_continuous_iff_type(&ctx));
    decls.push(build_mk_continuous_type(&ctx));
    decls.push(build_qm_comp_type(&ctx));
    decls.push(build_qm_of_surj_open_type(&ctx));
    decls.push(build_is_open_map_type(&ctx));
    decls.push(build_is_closed_map_type(&ctx));
    decls.push(build_qm_of_surj_closed_type(&ctx));
    decls.push(build_coinduced_eq_type(&ctx));
    decls.push(build_is_finest_type(&ctx));

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

// {X Y : Type u} → [TopologicalSpace X] → (X → Y) → TopologicalSpace Y
fn build_quotient_topology_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, _) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (q_id, _) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));
    let r = Expr::app(ctx.topological_space(), y.clone());
    let r = b.mk_pi(
        q_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.QuotientTopology", b.finish(r))
}

// {X Y : Type u} → [TopologicalSpace X] → (q : X → Y) → [TopologicalSpace Y] →
//   (U : Y → Prop) → Iff (IsOpen U) (IsOpen (fun x => U (q x)))
fn build_is_open_iff_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (q_id, q) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));
    let (iy_id, iy) = b.fresh_local(Expr::app(ctx.topological_space(), y.clone()));
    let (us_id, us) = b.fresh_local(Expr::arrow(y.clone(), ctx.prop.clone()));
    let open_u = Expr::app(
        Expr::app(Expr::app(ctx.is_open(), y.clone()), iy.clone()),
        us.clone(),
    );
    let (px_id, px) = b.fresh_local(x.clone());
    let pre = b.mk_lam(
        px_id,
        BinderInfo::Default,
        x.clone(),
        Expr::app(us.clone(), Expr::app(q.clone(), px.clone())),
    );
    let open_pre = Expr::app(
        Expr::app(Expr::app(ctx.is_open(), x.clone()), ix.clone()),
        pre,
    );
    let body = Expr::app(Expr::app(ctx.iff_const(), open_u), open_pre);
    let r = b.mk_pi(
        us_id,
        BinderInfo::Default,
        Expr::arrow(y.clone(), ctx.prop.clone()),
        body,
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        q_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.QuotientTopology.isOpen_iff", b.finish(r))
}

// {X Y : Type u} → [TopologicalSpace X] → (q : X → Y) → [TopologicalSpace Y] →
//   (C : Y → Prop) → Iff (IsClosed C) (IsClosed (fun x => C (q x)))
fn build_is_closed_iff_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (q_id, q) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));
    let (iy_id, iy) = b.fresh_local(Expr::app(ctx.topological_space(), y.clone()));
    let (cs_id, cs) = b.fresh_local(Expr::arrow(y.clone(), ctx.prop.clone()));
    let closed_c = Expr::app(
        Expr::app(Expr::app(ctx.is_closed(), y.clone()), iy.clone()),
        cs.clone(),
    );
    let (px_id, px) = b.fresh_local(x.clone());
    let pre = b.mk_lam(
        px_id,
        BinderInfo::Default,
        x.clone(),
        Expr::app(cs.clone(), Expr::app(q.clone(), px.clone())),
    );
    let closed_pre = Expr::app(
        Expr::app(Expr::app(ctx.is_closed(), x.clone()), ix.clone()),
        pre,
    );
    let body = Expr::app(Expr::app(ctx.iff_const(), closed_c), closed_pre);
    let r = b.mk_pi(
        cs_id,
        BinderInfo::Default,
        Expr::arrow(y.clone(), ctx.prop.clone()),
        body,
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        q_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.QuotientTopology.isClosed_iff", b.finish(r))
}

// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] → (X → Y) → Prop
fn build_is_quotient_map_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, _) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (iy_id, _) = b.fresh_local(Expr::app(ctx.topological_space(), y.clone()));
    let (q_id, _) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));
    let r = b.mk_pi(
        q_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), y.clone()),
        ctx.prop.clone(),
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.IsQuotientMap", b.finish(r))
}

// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] → {q : X → Y} →
//   IsQuotientMap q → Continuous q
fn build_qm_continuous_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (iy_id, iy) = b.fresh_local(Expr::app(ctx.topological_space(), y.clone()));
    let (q_id, q) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));

    let is_qm_q = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.is_quotient_map(), x.clone()), y.clone()),
                ix.clone(),
            ),
            iy.clone(),
        ),
        q.clone(),
    );

    let (h_id, _) = b.fresh_local(is_qm_q.clone());

    let continuous_q = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.continuous(), x.clone()), y.clone()),
                ix.clone(),
            ),
            iy.clone(),
        ),
        q.clone(),
    );

    let r = b.mk_pi(h_id, BinderInfo::Default, is_qm_q, continuous_q);
    let r = b.mk_pi(
        q_id,
        BinderInfo::Implicit,
        Expr::arrow(x.clone(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.IsQuotientMap.continuous", b.finish(r))
}

// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] → {q : X → Y} →
//   IsQuotientMap q → (U : Y → Prop) → Iff (IsOpen U) (IsOpen (fun x => U (q x)))
fn build_qm_is_open_preimage_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (iy_id, iy) = b.fresh_local(Expr::app(ctx.topological_space(), y.clone()));
    let (q_id, q) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));

    let is_qm_q = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.is_quotient_map(), x.clone()), y.clone()),
                ix.clone(),
            ),
            iy.clone(),
        ),
        q.clone(),
    );

    let (h_id, _) = b.fresh_local(is_qm_q.clone());
    let (us_id, us) = b.fresh_local(Expr::arrow(y.clone(), ctx.prop.clone()));

    let is_open_u = Expr::app(
        Expr::app(Expr::app(ctx.is_open(), y.clone()), iy.clone()),
        us.clone(),
    );

    let (px_id, px) = b.fresh_local(x.clone());
    let preimage_body = Expr::app(us.clone(), Expr::app(q.clone(), px.clone()));
    let preimage = b.mk_lam(px_id, BinderInfo::Default, x.clone(), preimage_body);

    let is_open_preimage = Expr::app(
        Expr::app(Expr::app(ctx.is_open(), x.clone()), ix.clone()),
        preimage,
    );

    let body = Expr::app(Expr::app(ctx.iff_const(), is_open_u), is_open_preimage);
    let r = b.mk_pi(
        us_id,
        BinderInfo::Default,
        Expr::arrow(y.clone(), ctx.prop.clone()),
        body,
    );
    let r = b.mk_pi(h_id, BinderInfo::Default, is_qm_q, r);
    let r = b.mk_pi(
        q_id,
        BinderInfo::Implicit,
        Expr::arrow(x.clone(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.IsQuotientMap.isOpen_preimage", b.finish(r))
}

// {X Y Z : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] → [TopologicalSpace Z] →
//   (q : X → Y) → (f : Y → Z) → Iff (Continuous f) (Continuous (fun x => f (q x)))
fn build_continuous_iff_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (z_id, z) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (iy_id, iy) = b.fresh_local(Expr::app(ctx.topological_space(), y.clone()));
    let (iz_id, iz) = b.fresh_local(Expr::app(ctx.topological_space(), z.clone()));
    let (q_id, q) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));
    let (f_id, f) = b.fresh_local(Expr::arrow(y.clone(), z.clone()));

    let continuous_f = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.continuous(), y.clone()), z.clone()),
                iy.clone(),
            ),
            iz.clone(),
        ),
        f.clone(),
    );

    let (px_id, px) = b.fresh_local(x.clone());
    let f_comp_q = b.mk_lam(
        px_id,
        BinderInfo::Default,
        x.clone(),
        Expr::app(f.clone(), Expr::app(q.clone(), px.clone())),
    );

    let continuous_fq = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.continuous(), x.clone()), z.clone()),
                ix.clone(),
            ),
            iz.clone(),
        ),
        f_comp_q,
    );

    let body = Expr::app(Expr::app(ctx.iff_const(), continuous_f), continuous_fq);
    let r = b.mk_pi(
        f_id,
        BinderInfo::Default,
        Expr::arrow(y.clone(), z.clone()),
        body,
    );
    let r = b.mk_pi(
        q_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        iz_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), z.clone()),
        r,
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(z_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.QuotientTopology.continuous_iff", b.finish(r))
}

// {X : Type u} → [TopologicalSpace X] → Prop
fn build_mk_continuous_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, _) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let r = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        ctx.prop.clone(),
    );
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.QuotientTopology.mk_continuous", b.finish(r))
}

// {X Y Z : Type u} → [...] → {p : Y → Z} → {q : X → Y} →
//   IsQuotientMap p → IsQuotientMap q → IsQuotientMap (fun x => p (q x))
fn build_qm_comp_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (z_id, z) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (iy_id, iy) = b.fresh_local(Expr::app(ctx.topological_space(), y.clone()));
    let (iz_id, iz) = b.fresh_local(Expr::app(ctx.topological_space(), z.clone()));
    let (p_id, p) = b.fresh_local(Expr::arrow(y.clone(), z.clone()));
    let (q_id, q) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));

    let is_qm_p = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.is_quotient_map(), y.clone()), z.clone()),
                iy.clone(),
            ),
            iz.clone(),
        ),
        p.clone(),
    );

    let is_qm_q = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.is_quotient_map(), x.clone()), y.clone()),
                ix.clone(),
            ),
            iy.clone(),
        ),
        q.clone(),
    );

    let (hp_id, _) = b.fresh_local(is_qm_p.clone());
    let (hq_id, _) = b.fresh_local(is_qm_q.clone());

    let (px_id, px) = b.fresh_local(x.clone());
    let comp_body = Expr::app(p.clone(), Expr::app(q.clone(), px.clone()));
    let p_comp_q = b.mk_lam(px_id, BinderInfo::Default, x.clone(), comp_body);

    let is_qm_comp = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.is_quotient_map(), x.clone()), z.clone()),
                ix.clone(),
            ),
            iz.clone(),
        ),
        p_comp_q,
    );

    let r = b.mk_pi(hq_id, BinderInfo::Default, is_qm_q, is_qm_comp);
    let r = b.mk_pi(hp_id, BinderInfo::Default, is_qm_p, r);
    let r = b.mk_pi(
        q_id,
        BinderInfo::Implicit,
        Expr::arrow(x.clone(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        p_id,
        BinderInfo::Implicit,
        Expr::arrow(y.clone(), z.clone()),
        r,
    );
    let r = b.mk_pi(
        iz_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), z.clone()),
        r,
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(z_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.IsQuotientMap.comp", b.finish(r))
}

// {X Y : Type u} → [...] → {q : X → Y} →
//   Prop → Prop → Prop → IsQuotientMap q
fn build_qm_of_surj_open_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (iy_id, iy) = b.fresh_local(Expr::app(ctx.topological_space(), y.clone()));
    let (q_id, q) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));
    let (hs_id, _) = b.fresh_local(ctx.prop.clone());
    let (hc_id, _) = b.fresh_local(ctx.prop.clone());
    let (ho_id, _) = b.fresh_local(ctx.prop.clone());
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.is_quotient_map(), x.clone()), y.clone()),
                ix.clone(),
            ),
            iy.clone(),
        ),
        q.clone(),
    );
    let r = b.mk_pi(ho_id, BinderInfo::Default, ctx.prop.clone(), body);
    let r = b.mk_pi(hc_id, BinderInfo::Default, ctx.prop.clone(), r);
    let r = b.mk_pi(hs_id, BinderInfo::Default, ctx.prop.clone(), r);
    let r = b.mk_pi(
        q_id,
        BinderInfo::Implicit,
        Expr::arrow(x.clone(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info(
        "Topology.quotient_map_of_surjective_continuous_open",
        b.finish(r),
    )
}

// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] → (X → Y) → Prop
fn build_is_open_map_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, _) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (iy_id, _) = b.fresh_local(Expr::app(ctx.topological_space(), y.clone()));
    let (f_id, _) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));
    let r = b.mk_pi(
        f_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), y.clone()),
        ctx.prop.clone(),
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.IsOpenMap", b.finish(r))
}

// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] → (X → Y) → Prop
fn build_is_closed_map_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, _) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (iy_id, _) = b.fresh_local(Expr::app(ctx.topological_space(), y.clone()));
    let (f_id, _) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));
    let r = b.mk_pi(
        f_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), y.clone()),
        ctx.prop.clone(),
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.IsClosedMap", b.finish(r))
}

// {X Y : Type u} → [...] → {q : X → Y} →
//   Prop → Prop → Prop → IsQuotientMap q
fn build_qm_of_surj_closed_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (iy_id, iy) = b.fresh_local(Expr::app(ctx.topological_space(), y.clone()));
    let (q_id, q) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));
    let (hs_id, _) = b.fresh_local(ctx.prop.clone());
    let (hc_id, _) = b.fresh_local(ctx.prop.clone());
    let (hcl_id, _) = b.fresh_local(ctx.prop.clone());
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.is_quotient_map(), x.clone()), y.clone()),
                ix.clone(),
            ),
            iy.clone(),
        ),
        q.clone(),
    );
    let r = b.mk_pi(hcl_id, BinderInfo::Default, ctx.prop.clone(), body);
    let r = b.mk_pi(hc_id, BinderInfo::Default, ctx.prop.clone(), r);
    let r = b.mk_pi(hs_id, BinderInfo::Default, ctx.prop.clone(), r);
    let r = b.mk_pi(
        q_id,
        BinderInfo::Implicit,
        Expr::arrow(x.clone(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        iy_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info(
        "Topology.quotient_map_of_surjective_continuous_closed",
        b.finish(r),
    )
}

// {X Y : Type u} → [TopologicalSpace X] → (X → Y) → Prop
fn build_coinduced_eq_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, _) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (q_id, _) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));
    let r = b.mk_pi(
        q_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), y.clone()),
        ctx.prop.clone(),
    );
    let r = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.QuotientTopology.coinduced_eq", b.finish(r))
}

// {X Y : Type u} → [TopologicalSpace X] → (X → Y) → TopologicalSpace Y → Prop
fn build_is_finest_type(ctx: &QuotientCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, _) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (q_id, _) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));
    let (tau_id, _) = b.fresh_local(Expr::app(ctx.topological_space(), y.clone()));
    let r = b.mk_pi(
        tau_id,
        BinderInfo::Default,
        Expr::app(ctx.topological_space(), y.clone()),
        ctx.prop.clone(),
    );
    let r = b.mk_pi(
        q_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), y.clone()),
        r,
    );
    let r = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.QuotientTopology.isFinest", b.finish(r))
}
