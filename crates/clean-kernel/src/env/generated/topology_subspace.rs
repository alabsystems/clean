// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.Subspace cluster declarations (#1444).
//!
//! This module covers the migrated Subspace declarations from
//! `init_topology_subspace`:
//! - Topology.SubspaceTopology
//! - Topology.SubspaceTopology.isOpen_iff
//! - Topology.SubspaceTopology.isClosed_iff
//! - Topology.inclusion_continuous
//! - Topology.SubspaceTopology.induced_eq
//! - Topology.SubspaceTopology.restrict_continuous
//! - Topology.SubspaceTopology.isCoarsest

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.SubspaceTopology";
pub(crate) const DECL_COUNT: usize = 7;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.SubspaceTopology",
    "Topology.SubspaceTopology.isOpen_iff",
    "Topology.SubspaceTopology.isClosed_iff",
    "Topology.inclusion_continuous",
    "Topology.SubspaceTopology.induced_eq",
    "Topology.SubspaceTopology.restrict_continuous",
    "Topology.SubspaceTopology.isCoarsest",
];

struct SubspaceCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl SubspaceCtx {
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

    fn and_const(&self) -> Expr {
        Expr::const_(Name::from_string("And"), vec![])
    }

    fn exists_const(&self, lvl: Level) -> Expr {
        Expr::const_(Name::from_string("Exists"), vec![lvl])
    }

    fn subtype(&self, x: Expr, a: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Subtype"),
                    vec![Level::succ(self.u_level.clone())],
                ),
                x,
            ),
            a,
        )
    }

    fn subtype_val(&self, x: Expr, a: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Subtype.val"),
                    vec![Level::succ(self.u_level.clone())],
                ),
                x,
            ),
            a,
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
    let ctx = SubspaceCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    decls.push(build_subspace_topology_type(&ctx));
    decls.push(build_subspace_is_open_iff_type(&ctx));
    decls.push(build_subspace_is_closed_iff_type(&ctx));
    decls.push(build_inclusion_continuous_type(&ctx));
    decls.push(build_subspace_induced_eq_type(&ctx));
    decls.push(build_subspace_restrict_continuous_type(&ctx));
    decls.push(build_subspace_is_coarsest_type(&ctx));

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

// {X : Type u} → [TopologicalSpace X] → (A : X → Prop) → TopologicalSpace (Subtype A)
fn build_subspace_topology_type(ctx: &SubspaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, _) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (a_id, a) = b.fresh_local(Expr::arrow(x.clone(), ctx.prop.clone()));
    let subtype_a = ctx.subtype(x.clone(), a.clone());
    let result = Expr::app(ctx.topological_space(), subtype_a);
    let result = b.mk_pi(
        a_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), ctx.prop.clone()),
        result,
    );
    let result = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        result,
    );
    let result = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), result);
    ctx.to_axiom_info("Topology.SubspaceTopology", b.finish(result))
}

// {X : Type u} → [TopologicalSpace X] → (A : X → Prop) → [TopologicalSpace (Subtype A)] →
//   (U : Subtype A → Prop) → Iff (IsOpen U) (∃ V, IsOpen V ∧ ∀ s, Iff (U s) (V (Subtype.val s)))
fn build_subspace_is_open_iff_type(ctx: &SubspaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (inst_x_id, inst_x) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (a_id, a) = b.fresh_local(Expr::arrow(x.clone(), ctx.prop.clone()));
    let subtype_a = ctx.subtype(x.clone(), a.clone());
    let (inst_sub_id, inst_sub) =
        b.fresh_local(Expr::app(ctx.topological_space(), subtype_a.clone()));
    let (u_id, u_var) = b.fresh_local(Expr::arrow(subtype_a.clone(), ctx.prop.clone()));
    let is_open_u = Expr::app(
        Expr::app(
            Expr::app(ctx.is_open(), subtype_a.clone()),
            inst_sub.clone(),
        ),
        u_var.clone(),
    );

    let set_x = Expr::arrow(x.clone(), ctx.prop.clone());
    let (v_id, v) = b.fresh_local(set_x.clone());
    let is_open_v = Expr::app(
        Expr::app(Expr::app(ctx.is_open(), x.clone()), inst_x.clone()),
        v.clone(),
    );

    let subtype_val_app = ctx.subtype_val(x.clone(), a.clone());
    let (s_id, s) = b.fresh_local(subtype_a.clone());
    let u_s = Expr::app(u_var.clone(), s.clone());
    let v_val_s = Expr::app(v.clone(), Expr::app(subtype_val_app, s.clone()));
    let iff_u_v = Expr::app(Expr::app(ctx.iff_const(), u_s), v_val_s);
    let eq_conjunct = b.mk_pi(s_id, BinderInfo::Default, subtype_a.clone(), iff_u_v);
    let exists_body_inner = Expr::app(Expr::app(ctx.and_const(), is_open_v), eq_conjunct);
    let exists_body = b.mk_lam(v_id, BinderInfo::Default, set_x.clone(), exists_body_inner);
    let rhs = Expr::app(
        Expr::app(ctx.exists_const(Level::succ(ctx.u_level.clone())), set_x),
        exists_body,
    );
    let body = Expr::app(Expr::app(ctx.iff_const(), is_open_u), rhs);

    let result = b.mk_pi(
        u_id,
        BinderInfo::Default,
        Expr::arrow(subtype_a.clone(), ctx.prop.clone()),
        body,
    );
    let result = b.mk_pi(
        inst_sub_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), subtype_a.clone()),
        result,
    );
    let result = b.mk_pi(
        a_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), ctx.prop.clone()),
        result,
    );
    let result = b.mk_pi(
        inst_x_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        result,
    );
    let result = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), result);
    ctx.to_axiom_info("Topology.SubspaceTopology.isOpen_iff", b.finish(result))
}

// {X : Type u} → [TopologicalSpace X] → (A : X → Prop) → [TopologicalSpace (Subtype A)] →
//   (C : Subtype A → Prop) → Iff (IsClosed C) (∃ K, IsClosed K ∧ ∀ s, Iff (C s) (K (Subtype.val s)))
fn build_subspace_is_closed_iff_type(ctx: &SubspaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (inst_x_id, inst_x) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (a_id, a) = b.fresh_local(Expr::arrow(x.clone(), ctx.prop.clone()));
    let subtype_a = ctx.subtype(x.clone(), a.clone());
    let (inst_sub_id, inst_sub) =
        b.fresh_local(Expr::app(ctx.topological_space(), subtype_a.clone()));
    let (c_id, c_var) = b.fresh_local(Expr::arrow(subtype_a.clone(), ctx.prop.clone()));
    let is_closed_c = Expr::app(
        Expr::app(
            Expr::app(ctx.is_closed(), subtype_a.clone()),
            inst_sub.clone(),
        ),
        c_var.clone(),
    );

    let set_x = Expr::arrow(x.clone(), ctx.prop.clone());
    let (v_id, v) = b.fresh_local(set_x.clone());
    let is_closed_v = Expr::app(
        Expr::app(Expr::app(ctx.is_closed(), x.clone()), inst_x.clone()),
        v.clone(),
    );

    let subtype_val_app = ctx.subtype_val(x.clone(), a.clone());
    let (s_id, s) = b.fresh_local(subtype_a.clone());
    let c_s = Expr::app(c_var.clone(), s.clone());
    let v_val_s = Expr::app(v.clone(), Expr::app(subtype_val_app, s.clone()));
    let iff_c_v = Expr::app(Expr::app(ctx.iff_const(), c_s), v_val_s);
    let eq_conjunct = b.mk_pi(s_id, BinderInfo::Default, subtype_a.clone(), iff_c_v);
    let exists_body_inner = Expr::app(Expr::app(ctx.and_const(), is_closed_v), eq_conjunct);
    let exists_body = b.mk_lam(v_id, BinderInfo::Default, set_x.clone(), exists_body_inner);
    let rhs = Expr::app(
        Expr::app(ctx.exists_const(Level::succ(ctx.u_level.clone())), set_x),
        exists_body,
    );
    let body = Expr::app(Expr::app(ctx.iff_const(), is_closed_c), rhs);

    let result = b.mk_pi(
        c_id,
        BinderInfo::Default,
        Expr::arrow(subtype_a.clone(), ctx.prop.clone()),
        body,
    );
    let result = b.mk_pi(
        inst_sub_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), subtype_a.clone()),
        result,
    );
    let result = b.mk_pi(
        a_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), ctx.prop.clone()),
        result,
    );
    let result = b.mk_pi(
        inst_x_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        result,
    );
    let result = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), result);
    ctx.to_axiom_info("Topology.SubspaceTopology.isClosed_iff", b.finish(result))
}

// {X : Type u} → [TopologicalSpace X] → (A : X → Prop) → [TopologicalSpace (Subtype A)] →
//   Continuous (Subtype.val : Subtype A → X)
fn build_inclusion_continuous_type(ctx: &SubspaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (inst_x_id, inst_x) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (a_id, a) = b.fresh_local(Expr::arrow(x.clone(), ctx.prop.clone()));
    let subtype_a = ctx.subtype(x.clone(), a.clone());
    let (inst_sub_id, inst_sub) =
        b.fresh_local(Expr::app(ctx.topological_space(), subtype_a.clone()));
    let subtype_val_applied = ctx.subtype_val(x.clone(), a.clone());
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.continuous(), subtype_a.clone()), x.clone()),
                inst_sub.clone(),
            ),
            inst_x.clone(),
        ),
        subtype_val_applied,
    );

    let result = b.mk_pi(
        inst_sub_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), subtype_a),
        body,
    );
    let result = b.mk_pi(
        a_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), ctx.prop.clone()),
        result,
    );
    let result = b.mk_pi(
        inst_x_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        result,
    );
    let result = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), result);
    ctx.to_axiom_info("Topology.inclusion_continuous", b.finish(result))
}

// {X : Type u} → [TopologicalSpace X] → (A : X → Prop) →
//   Eq (SubspaceTopology A) (SubspaceTopology A)
fn build_subspace_induced_eq_type(ctx: &SubspaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (inst_x_id, inst_x) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (a_id, a) = b.fresh_local(Expr::arrow(x.clone(), ctx.prop.clone()));
    let subtype_a = ctx.subtype(x.clone(), a.clone());
    let subspace_topology = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Topology.SubspaceTopology"),
                    vec![ctx.u_level.clone()],
                ),
                x.clone(),
            ),
            inst_x.clone(),
        ),
        a.clone(),
    );
    let topo_type = Expr::app(ctx.topological_space(), subtype_a);
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Eq"),
                    vec![Level::succ(ctx.u_level.clone())],
                ),
                topo_type,
            ),
            subspace_topology.clone(),
        ),
        subspace_topology,
    );

    let result = b.mk_pi(
        a_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), ctx.prop.clone()),
        body,
    );
    let result = b.mk_pi(
        inst_x_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        result,
    );
    let result = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), result);
    ctx.to_axiom_info("Topology.SubspaceTopology.induced_eq", b.finish(result))
}

// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] →
//   {f : X → Y} → Continuous f → (A : X → Prop) → [TopologicalSpace (Subtype A)] →
//   Continuous (fun x => f x.val)
fn build_subspace_restrict_continuous_type(ctx: &SubspaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (y_id, y) = b.fresh_local(ctx.type_u.clone());
    let (inst_x_id, inst_x) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (inst_y_id, inst_y) = b.fresh_local(Expr::app(ctx.topological_space(), y.clone()));
    let (f_id, f) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));
    let cont_f = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.continuous(), x.clone()), y.clone()),
                inst_x.clone(),
            ),
            inst_y.clone(),
        ),
        f.clone(),
    );
    let (hf_id, _) = b.fresh_local(cont_f.clone());
    let (a_id, a) = b.fresh_local(Expr::arrow(x.clone(), ctx.prop.clone()));
    let subtype_a = ctx.subtype(x.clone(), a.clone());
    let (inst_sub_id, inst_sub) =
        b.fresh_local(Expr::app(ctx.topological_space(), subtype_a.clone()));
    let (s_id, s) = b.fresh_local(subtype_a.clone());
    let subtype_val_app = ctx.subtype_val(x.clone(), a.clone());
    let restricted_f = b.mk_lam(
        s_id,
        BinderInfo::Default,
        subtype_a.clone(),
        Expr::app(f.clone(), Expr::app(subtype_val_app, s.clone())),
    );
    let cont_restricted = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.continuous(), subtype_a.clone()), y.clone()),
                inst_sub.clone(),
            ),
            inst_y.clone(),
        ),
        restricted_f,
    );

    let result = b.mk_pi(
        inst_sub_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), subtype_a),
        cont_restricted,
    );
    let result = b.mk_pi(
        a_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), ctx.prop.clone()),
        result,
    );
    let result = b.mk_pi(hf_id, BinderInfo::Default, cont_f, result);
    let result = b.mk_pi(
        f_id,
        BinderInfo::Implicit,
        Expr::arrow(x.clone(), y.clone()),
        result,
    );
    let result = b.mk_pi(
        inst_y_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), y.clone()),
        result,
    );
    let result = b.mk_pi(
        inst_x_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        result,
    );
    let result = b.mk_pi(y_id, BinderInfo::Implicit, ctx.type_u.clone(), result);
    let result = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), result);
    ctx.to_axiom_info(
        "Topology.SubspaceTopology.restrict_continuous",
        b.finish(result),
    )
}

// {X : Type u} → [TopologicalSpace X] → (A : X → Prop) →
//   [TopologicalSpace (Subtype A)] → Continuous (Subtype.val : Subtype A → X) → Prop
fn build_subspace_is_coarsest_type(ctx: &SubspaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (inst_x_id, inst_x) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (a_id, a) = b.fresh_local(Expr::arrow(x.clone(), ctx.prop.clone()));
    let subtype_a = ctx.subtype(x.clone(), a.clone());
    let (inst_sub_id, inst_sub) =
        b.fresh_local(Expr::app(ctx.topological_space(), subtype_a.clone()));
    let subtype_val = ctx.subtype_val(x.clone(), a.clone());
    let cont_subtype_val = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(ctx.continuous(), subtype_a.clone()), x.clone()),
                inst_sub,
            ),
            inst_x.clone(),
        ),
        subtype_val,
    );
    let (cont_id, _) = b.fresh_local(cont_subtype_val.clone());
    let result = b.mk_pi(
        cont_id,
        BinderInfo::Default,
        cont_subtype_val,
        ctx.prop.clone(),
    );
    let result = b.mk_pi(
        inst_sub_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), subtype_a),
        result,
    );
    let result = b.mk_pi(
        a_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), ctx.prop.clone()),
        result,
    );
    let result = b.mk_pi(
        inst_x_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x),
        result,
    );
    let result = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), result);
    ctx.to_axiom_info("Topology.SubspaceTopology.isCoarsest", b.finish(result))
}
