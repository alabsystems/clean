// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for TopologicalSpace namespace (#1444).
//!
//! Migrated from handwritten `add_decl` calls in `topology_basic.rs:init_topological_space`.
//! All 12 unconditional declarations use `EnvDeclBuilder` to avoid raw de Bruijn
//! index arithmetic. The conditional `Topology.metric_to_topology` declaration
//! remains inline in `init_topological_space` (gated on `has_metric_space()`).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "TopologicalSpace";
pub(crate) const DECL_COUNT: usize = 12;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "TopologicalSpace",
    "IsOpen",
    "IsClosed",
    "IsOpen.univ",
    "IsOpen.empty",
    "IsOpen.inter",
    "IsOpen.union",
    "IsClosed.compl",
    "Topology.Interior",
    "Topology.Closure",
    "Topology.interior_spec",
    "Topology.closure_spec",
];

/// Shared universe/type context for TopologicalSpace declarations.
struct TopSpaceCtx {
    u: Name,
    v: Name,
    u_level: Level,
    v_level: Level,
    type_u: Expr,
    type_v: Expr,
    prop: Expr,
}

impl TopSpaceCtx {
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

    fn is_open(&self) -> Expr {
        Expr::const_(Name::from_string("IsOpen"), vec![self.u_level.clone()])
    }

    fn is_closed(&self) -> Expr {
        Expr::const_(Name::from_string("IsClosed"), vec![self.u_level.clone()])
    }

    fn and_const(&self) -> Expr {
        Expr::const_(Name::from_string("And"), vec![])
    }

    fn iff_const(&self) -> Expr {
        Expr::const_(Name::from_string("Iff"), vec![])
    }

    fn true_const(&self) -> Expr {
        Expr::const_(Name::from_string("True"), vec![])
    }

    fn false_const(&self) -> Expr {
        Expr::const_(Name::from_string("False"), vec![])
    }

    fn interior_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Interior"),
            vec![self.u_level.clone()],
        )
    }

    fn closure_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Closure"),
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

    fn to_axiom_info_with_levels(
        &self,
        name: &str,
        levels: Vec<Name>,
        type_: Expr,
    ) -> ConstantInfo {
        ConstantInfo {
            name: Name::from_string(name),
            level_params: levels,
            type_,
            value: None,
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            kind: ConstantKind::Axiom,
        }
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = TopSpaceCtx::new();
    let decls = vec![
        build_topological_space_type(&ctx),
        build_is_open_type(&ctx),
        build_is_closed_type(&ctx),
        build_is_open_univ_type(&ctx),
        build_is_open_empty_type(&ctx),
        build_is_open_inter_type(&ctx),
        build_is_open_union_type(&ctx),
        build_is_closed_compl_type(&ctx),
        build_interior_type(&ctx),
        build_closure_type(&ctx),
        build_interior_spec_type(&ctx),
        build_closure_spec_type(&ctx),
    ];
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

// TopologicalSpace : Type u → Type u
fn build_topological_space_type(ctx: &TopSpaceCtx) -> ConstantInfo {
    let type_ = Expr::pi(BinderInfo::Default, ctx.type_u.clone(), ctx.type_u.clone());
    ctx.to_axiom_info("TopologicalSpace", type_)
}

// IsOpen : {α : Type u} → [TopologicalSpace α] → (α → Prop) → Prop
fn build_is_open_type(ctx: &TopSpaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, _) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        alpha.clone(),
    ));
    let alpha_to_prop = Expr::arrow(alpha.clone(), ctx.prop.clone());
    let (s_id, _) = b.fresh_local(alpha_to_prop.clone());

    let e = b.mk_pi(s_id, BinderInfo::Default, alpha_to_prop, ctx.prop.clone());
    let e = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), alpha.clone()),
        e,
    );
    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    ctx.to_axiom_info("IsOpen", b.finish(e))
}

// IsClosed : {α : Type u} → [TopologicalSpace α] → (α → Prop) → Prop
fn build_is_closed_type(ctx: &TopSpaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, _) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        alpha.clone(),
    ));
    let alpha_to_prop = Expr::arrow(alpha.clone(), ctx.prop.clone());
    let (s_id, _) = b.fresh_local(alpha_to_prop.clone());

    let e = b.mk_pi(s_id, BinderInfo::Default, alpha_to_prop, ctx.prop.clone());
    let e = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), alpha.clone()),
        e,
    );
    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    ctx.to_axiom_info("IsClosed", b.finish(e))
}

// IsOpen.univ : {α : Type u} → [TopologicalSpace α] → IsOpen (fun _ => True)
fn build_is_open_univ_type(ctx: &TopSpaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, inst) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        alpha.clone(),
    ));

    let (x_id, _) = b.fresh_local(alpha.clone());
    let univ_set = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), ctx.true_const());

    let result = Expr::apps(ctx.is_open(), [alpha.clone(), inst.clone(), univ_set]);

    let e = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), alpha.clone()),
        result,
    );
    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    ctx.to_axiom_info("IsOpen.univ", b.finish(e))
}

// IsOpen.empty : {α : Type u} → [TopologicalSpace α] → IsOpen (fun _ => False)
fn build_is_open_empty_type(ctx: &TopSpaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, inst) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        alpha.clone(),
    ));

    let (x_id, _) = b.fresh_local(alpha.clone());
    let empty_set = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), ctx.false_const());

    let result = Expr::apps(ctx.is_open(), [alpha.clone(), inst.clone(), empty_set]);

    let e = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), alpha.clone()),
        result,
    );
    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    ctx.to_axiom_info("IsOpen.empty", b.finish(e))
}

// IsOpen.inter : {α : Type u} → [TopologicalSpace α] →
//   {s t : α → Prop} → IsOpen s → IsOpen t → IsOpen (fun x => s x ∧ t x)
fn build_is_open_inter_type(ctx: &TopSpaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, inst) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        alpha.clone(),
    ));
    let alpha_to_prop = Expr::arrow(alpha.clone(), ctx.prop.clone());
    let (s_id, s) = b.fresh_local(alpha_to_prop.clone());
    let (t_id, t) = b.fresh_local(alpha_to_prop.clone());
    let is_open_s = Expr::apps(ctx.is_open(), [alpha.clone(), inst.clone(), s.clone()]);
    let is_open_t = Expr::apps(ctx.is_open(), [alpha.clone(), inst.clone(), t.clone()]);
    let (hs_id, _) = b.fresh_local(is_open_s.clone());
    let (ht_id, _) = b.fresh_local(is_open_t.clone());

    let (x_id, x) = b.fresh_local(alpha.clone());
    let s_x_and_t_x = Expr::app(
        Expr::app(ctx.and_const(), Expr::app(s.clone(), x.clone())),
        Expr::app(t.clone(), x.clone()),
    );
    let inter_set = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), s_x_and_t_x);

    let result = Expr::apps(ctx.is_open(), [alpha.clone(), inst.clone(), inter_set]);

    let e = b.mk_pi(ht_id, BinderInfo::Default, is_open_t, result);
    let e = b.mk_pi(hs_id, BinderInfo::Default, is_open_s, e);
    let e = b.mk_pi(t_id, BinderInfo::Implicit, alpha_to_prop.clone(), e);
    let e = b.mk_pi(s_id, BinderInfo::Implicit, alpha_to_prop, e);
    let e = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), alpha.clone()),
        e,
    );
    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    ctx.to_axiom_info("IsOpen.inter", b.finish(e))
}

// IsOpen.union : {α : Type u} → [TopologicalSpace α] →
//   {ι : Type v} → {U : ι → α → Prop} → (∀ i, IsOpen (U i)) →
//   IsOpen (fun x => ∃ i, U i x)
fn build_is_open_union_type(ctx: &TopSpaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, inst) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        alpha.clone(),
    ));
    let (iota_id, iota) = b.fresh_local(ctx.type_v.clone());
    let u_fn_type = Expr::arrow(iota.clone(), Expr::arrow(alpha.clone(), ctx.prop.clone()));
    let (u_fn_id, u_fn) = b.fresh_local(u_fn_type.clone());

    // ∀ i : ι, IsOpen (U i)
    let (i_id, i_var) = b.fresh_local(iota.clone());
    let u_i = Expr::app(u_fn.clone(), i_var.clone());
    let is_open_u_i = Expr::apps(ctx.is_open(), [alpha.clone(), inst.clone(), u_i]);
    let forall_i_is_open = b.mk_pi(i_id, BinderInfo::Default, iota.clone(), is_open_u_i);

    let (hu_id, _) = b.fresh_local(forall_i_is_open.clone());

    // fun x : α => ∃ i : ι, U i x
    let (x_id, x) = b.fresh_local(alpha.clone());
    let (i2_id, i2) = b.fresh_local(iota.clone());
    let u_i_x = Expr::app(Expr::app(u_fn.clone(), i2.clone()), x.clone());
    let exists_body = b.mk_lam(i2_id, BinderInfo::Default, iota.clone(), u_i_x);
    let exists_i_u_i_x = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(ctx.v_level.clone())],
            ),
            iota.clone(),
        ),
        exists_body,
    );
    let union_set = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), exists_i_u_i_x);

    let result = Expr::apps(ctx.is_open(), [alpha.clone(), inst.clone(), union_set]);

    let e = b.mk_pi(hu_id, BinderInfo::Default, forall_i_is_open, result);
    let e = b.mk_pi(u_fn_id, BinderInfo::Implicit, u_fn_type, e);
    let e = b.mk_pi(iota_id, BinderInfo::Implicit, ctx.type_v.clone(), e);
    let e = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), alpha.clone()),
        e,
    );
    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    ctx.to_axiom_info_with_levels(
        "IsOpen.union",
        vec![ctx.u.clone(), ctx.v.clone()],
        b.finish(e),
    )
}

// IsClosed.compl : {α : Type u} → [TopologicalSpace α] →
//   {s : α → Prop} → IsClosed s ↔ IsOpen (fun x => ¬ s x)
fn build_is_closed_compl_type(ctx: &TopSpaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, inst) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        alpha.clone(),
    ));
    let alpha_to_prop = Expr::arrow(alpha.clone(), ctx.prop.clone());
    let (s_id, s) = b.fresh_local(alpha_to_prop.clone());

    let is_closed_s = Expr::apps(ctx.is_closed(), [alpha.clone(), inst.clone(), s.clone()]);

    let (x_id, x) = b.fresh_local(alpha.clone());
    let not_s_x = Expr::arrow(Expr::app(s.clone(), x.clone()), ctx.false_const());
    let compl_set = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), not_s_x);

    let is_open_compl = Expr::apps(ctx.is_open(), [alpha.clone(), inst.clone(), compl_set]);

    let result = Expr::app(Expr::app(ctx.iff_const(), is_closed_s), is_open_compl);

    let e = b.mk_pi(s_id, BinderInfo::Implicit, alpha_to_prop, result);
    let e = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), alpha.clone()),
        e,
    );
    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    ctx.to_axiom_info("IsClosed.compl", b.finish(e))
}

// Topology.Interior : {α : Type u} → [TopologicalSpace α] → (α → Prop) → (α → Prop)
fn build_interior_type(ctx: &TopSpaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, _) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        alpha.clone(),
    ));
    let alpha_to_prop = Expr::arrow(alpha.clone(), ctx.prop.clone());
    let (s_id, _) = b.fresh_local(alpha_to_prop.clone());
    let result = Expr::arrow(alpha.clone(), ctx.prop.clone());

    let e = b.mk_pi(s_id, BinderInfo::Default, alpha_to_prop, result);
    let e = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), alpha.clone()),
        e,
    );
    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    ctx.to_axiom_info("Topology.Interior", b.finish(e))
}

// Topology.Closure : {α : Type u} → [TopologicalSpace α] → (α → Prop) → (α → Prop)
fn build_closure_type(ctx: &TopSpaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, _) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        alpha.clone(),
    ));
    let alpha_to_prop = Expr::arrow(alpha.clone(), ctx.prop.clone());
    let (s_id, _) = b.fresh_local(alpha_to_prop.clone());
    let result = Expr::arrow(alpha.clone(), ctx.prop.clone());

    let e = b.mk_pi(s_id, BinderInfo::Default, alpha_to_prop, result);
    let e = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), alpha.clone()),
        e,
    );
    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    ctx.to_axiom_info("Topology.Closure", b.finish(e))
}

// Topology.interior_spec : {α : Type u} → [TopologicalSpace α] →
//   {s : α → Prop} → (x : α) →
//   Interior s x ↔ ∃ U, IsOpen U ∧ U x ∧ (∀ y, U y → s y)
fn build_interior_spec_type(ctx: &TopSpaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, inst) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        alpha.clone(),
    ));
    let s_type = Expr::arrow(alpha.clone(), ctx.prop.clone());
    let (s_id, s) = b.fresh_local(s_type.clone());
    let (x_id, x) = b.fresh_local(alpha.clone());

    let interior_s_x = Expr::apps(
        ctx.interior_const(),
        [alpha.clone(), inst.clone(), s.clone(), x.clone()],
    );

    let exists_rhs = {
        let mut sub = EnvDeclBuilder::child_of(&b);
        let (u_id, u_var) = sub.fresh_local(s_type.clone());

        let is_open_u = Expr::apps(ctx.is_open(), [alpha.clone(), inst.clone(), u_var.clone()]);
        let u_x = Expr::app(u_var.clone(), x.clone());

        let forall_y = {
            let mut sub2 = EnvDeclBuilder::child_of(&sub);
            let (y_id, y) = sub2.fresh_local(alpha.clone());
            let u_y = Expr::app(u_var.clone(), y.clone());
            let s_y = Expr::app(s.clone(), y.clone());
            let (h_id, _) = sub2.fresh_local(u_y.clone());
            let e = sub2.mk_pi(h_id, BinderInfo::Default, u_y, s_y);
            sub2.mk_pi(y_id, BinderInfo::Default, alpha.clone(), e)
        };

        let u_x_and_subset = Expr::app(Expr::app(ctx.and_const(), u_x), forall_y);
        let conjunction = Expr::app(Expr::app(ctx.and_const(), is_open_u), u_x_and_subset);

        let exists_body = sub.mk_lam(u_id, BinderInfo::Default, s_type.clone(), conjunction);

        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Exists"),
                    vec![Level::succ(ctx.u_level.clone())],
                ),
                s_type.clone(),
            ),
            exists_body,
        )
    };

    let iff_body = Expr::app(Expr::app(ctx.iff_const(), interior_s_x), exists_rhs);

    let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), iff_body);
    let e = b.mk_pi(s_id, BinderInfo::Implicit, s_type, e);
    let e = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), alpha.clone()),
        e,
    );
    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    ctx.to_axiom_info("Topology.interior_spec", b.finish(e))
}

// Topology.closure_spec : {α : Type u} → [TopologicalSpace α] →
//   {s : α → Prop} → (x : α) →
//   Closure s x ↔ ∀ U, IsOpen U → U x → ∃ y, U y ∧ s y
fn build_closure_spec_type(ctx: &TopSpaceCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (alpha_id, alpha) = b.fresh_local(ctx.type_u.clone());
    let (inst_id, inst) = b.fresh_local(Expr::app(
        ctx.topological_space(ctx.u_level.clone()),
        alpha.clone(),
    ));
    let s_type = Expr::arrow(alpha.clone(), ctx.prop.clone());
    let (s_id, s) = b.fresh_local(s_type.clone());
    let (x_id, x) = b.fresh_local(alpha.clone());

    let closure_s_x = Expr::apps(
        ctx.closure_const(),
        [alpha.clone(), inst.clone(), s.clone(), x.clone()],
    );

    let forall_u_rhs = {
        let mut sub = EnvDeclBuilder::child_of(&b);
        let (u_id, u_var) = sub.fresh_local(s_type.clone());

        let is_open_u = Expr::apps(ctx.is_open(), [alpha.clone(), inst.clone(), u_var.clone()]);
        let (hopen_id, _) = sub.fresh_local(is_open_u.clone());

        let u_x = Expr::app(u_var.clone(), x.clone());
        let (hux_id, _) = sub.fresh_local(u_x.clone());

        let exists_y = {
            let mut sub2 = EnvDeclBuilder::child_of(&sub);
            let (y_id, y) = sub2.fresh_local(alpha.clone());
            let u_y = Expr::app(u_var.clone(), y.clone());
            let s_y = Expr::app(s.clone(), y.clone());
            let conjunction = Expr::app(Expr::app(ctx.and_const(), u_y), s_y);
            let exists_body = sub2.mk_lam(y_id, BinderInfo::Default, alpha.clone(), conjunction);
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Exists"),
                        vec![Level::succ(ctx.u_level.clone())],
                    ),
                    alpha.clone(),
                ),
                exists_body,
            )
        };

        let e = sub.mk_pi(hux_id, BinderInfo::Default, u_x, exists_y);
        let e = sub.mk_pi(hopen_id, BinderInfo::Default, is_open_u, e);
        sub.mk_pi(u_id, BinderInfo::Default, s_type.clone(), e)
    };

    let iff_body = Expr::app(Expr::app(ctx.iff_const(), closure_s_x), forall_u_rhs);

    let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), iff_body);
    let e = b.mk_pi(s_id, BinderInfo::Implicit, s_type, e);
    let e = b.mk_pi(
        inst_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(ctx.u_level.clone()), alpha.clone()),
        e,
    );
    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, ctx.type_u.clone(), e);
    ctx.to_axiom_info("Topology.closure_spec", b.finish(e))
}
