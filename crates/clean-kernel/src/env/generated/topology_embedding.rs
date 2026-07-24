// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.Embedding cluster declarations (#1444).
//!
//! This module covers the embedding declarations from `init_topology_subspace`
//! that remained handwritten after the SubspaceTopology overlay was loaded:
//!
//! - Topology.IsEmbedding
//! - Topology.IsEmbedding.continuous
//! - Function.Injective (Definition with value)
//! - Topology.IsEmbedding.injective
//! - Topology.inclusion_embedding
//! - Topology.IsOpenEmbedding
//! - Topology.IsClosedEmbedding
//! - Topology.IsOpenEmbedding.toIsEmbedding
//! - Topology.IsClosedEmbedding.toIsEmbedding
//! - Topology.open_embedding_of_open_inclusion
//! - Topology.closed_embedding_of_closed_inclusion

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.Embedding";
pub(crate) const DECL_COUNT: usize = 11;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.IsEmbedding",
    "Topology.IsEmbedding.continuous",
    "Function.Injective",
    "Topology.IsEmbedding.injective",
    "Topology.inclusion_embedding",
    "Topology.IsOpenEmbedding",
    "Topology.IsClosedEmbedding",
    "Topology.IsOpenEmbedding.toIsEmbedding",
    "Topology.IsClosedEmbedding.toIsEmbedding",
    "Topology.open_embedding_of_open_inclusion",
    "Topology.closed_embedding_of_closed_inclusion",
];

struct EmbeddingCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl EmbeddingCtx {
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

    fn is_embedding_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.IsEmbedding"),
            vec![self.u_level.clone()],
        )
    }

    fn is_open_embedding_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.IsOpenEmbedding"),
            vec![self.u_level.clone()],
        )
    }

    fn is_closed_embedding_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.IsClosedEmbedding"),
            vec![self.u_level.clone()],
        )
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

    /// Build a 5-binder prefix: {X Y : Type u} → [TopologicalSpace X] →
    /// [TopologicalSpace Y] → (f : X → Y) → ...
    ///
    /// Returns (builder, x, y, ix, iy, f, ids for each binder).
    fn xy_topo_f_prefix(
        &self,
    ) -> (
        EnvDeclBuilder,
        Expr,
        Expr,
        Expr,
        Expr,
        Expr,
        crate::expr::FVarId,
        crate::expr::FVarId,
        crate::expr::FVarId,
        crate::expr::FVarId,
        crate::expr::FVarId,
    ) {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (y_id, y) = b.fresh_local(self.type_u.clone());
        let (ix_id, ix) = b.fresh_local(Expr::app(self.topological_space(), x.clone()));
        let (iy_id, iy) = b.fresh_local(Expr::app(self.topological_space(), y.clone()));
        let (f_id, f) = b.fresh_local(Expr::arrow(x.clone(), y.clone()));
        (b, x, y, ix, iy, f, x_id, y_id, ix_id, iy_id, f_id)
    }

    /// Close a body expression with the standard 5-binder prefix:
    /// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] → {f : X → Y} → body
    #[allow(clippy::too_many_arguments)]
    fn close_xy_topo_f(
        &self,
        b: &mut EnvDeclBuilder,
        x: &Expr,
        y: &Expr,
        x_id: crate::expr::FVarId,
        y_id: crate::expr::FVarId,
        ix_id: crate::expr::FVarId,
        iy_id: crate::expr::FVarId,
        f_id: crate::expr::FVarId,
        f_bi: BinderInfo,
        body: Expr,
    ) -> Expr {
        let r = b.mk_pi(f_id, f_bi, Expr::arrow(x.clone(), y.clone()), body);
        let r = b.mk_pi(
            iy_id,
            BinderInfo::InstImplicit,
            Expr::app(self.topological_space(), y.clone()),
            r,
        );
        let r = b.mk_pi(
            ix_id,
            BinderInfo::InstImplicit,
            Expr::app(self.topological_space(), x.clone()),
            r,
        );
        let r = b.mk_pi(y_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r)
    }

    /// Build IsEmbedding X Y ix iy f
    fn is_embedding_app(&self, x: &Expr, y: &Expr, ix: &Expr, iy: &Expr, f: &Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(self.is_embedding_const(), x.clone()), y.clone()),
                    ix.clone(),
                ),
                iy.clone(),
            ),
            f.clone(),
        )
    }

    /// Build Continuous X Y ix iy f
    fn continuous_app(&self, x: &Expr, y: &Expr, ix: &Expr, iy: &Expr, f: &Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(self.continuous(), x.clone()), y.clone()),
                    ix.clone(),
                ),
                iy.clone(),
            ),
            f.clone(),
        )
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = EmbeddingCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    decls.push(build_is_embedding_type(&ctx));
    decls.push(build_is_embedding_continuous_type(&ctx));
    decls.push(build_function_injective(&ctx));
    decls.push(build_is_embedding_injective_type(&ctx));
    decls.push(build_inclusion_embedding_type(&ctx));
    decls.push(build_is_open_embedding_type(&ctx));
    decls.push(build_is_closed_embedding_type(&ctx));
    decls.push(build_open_embedding_to_is_embedding_type(&ctx));
    decls.push(build_closed_embedding_to_is_embedding_type(&ctx));
    decls.push(build_open_embedding_of_open_inclusion_type(&ctx));
    decls.push(build_closed_embedding_of_closed_inclusion_type(&ctx));

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

// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] → (X → Y) → Prop
fn build_is_embedding_type(ctx: &EmbeddingCtx) -> ConstantInfo {
    let (mut b, x, y, _, _, _, x_id, y_id, ix_id, iy_id, f_id) = ctx.xy_topo_f_prefix();
    let r = ctx.close_xy_topo_f(
        &mut b,
        &x,
        &y,
        x_id,
        y_id,
        ix_id,
        iy_id,
        f_id,
        BinderInfo::Default,
        ctx.prop.clone(),
    );
    ctx.to_axiom_info("Topology.IsEmbedding", b.finish(r))
}

// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] →
//   {f : X → Y} → IsEmbedding f → Continuous f
fn build_is_embedding_continuous_type(ctx: &EmbeddingCtx) -> ConstantInfo {
    let (mut b, x, y, ix, iy, f, x_id, y_id, ix_id, iy_id, f_id) = ctx.xy_topo_f_prefix();
    let is_emb = ctx.is_embedding_app(&x, &y, &ix, &iy, &f);
    let cont_f = ctx.continuous_app(&x, &y, &ix, &iy, &f);
    let (h_id, _) = b.fresh_local(is_emb.clone());
    let body = b.mk_pi(h_id, BinderInfo::Default, is_emb, cont_f);
    let r = ctx.close_xy_topo_f(
        &mut b,
        &x,
        &y,
        x_id,
        y_id,
        ix_id,
        iy_id,
        f_id,
        BinderInfo::Implicit,
        body,
    );
    ctx.to_axiom_info("Topology.IsEmbedding.continuous", b.finish(r))
}

// Function.Injective : {α : Sort u} → {β : Sort v} → (α → β) → Prop
// def Function.Injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
fn build_function_injective(_ctx: &EmbeddingCtx) -> ConstantInfo {
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let u_level = Level::param(u.clone());
    let v_level = Level::param(v.clone());
    let sort_u = Expr::sort(u_level.clone());
    let sort_v = Expr::sort(v_level.clone());
    let prop = Expr::sort(Level::zero());

    let type_ = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(sort_u.clone());
        let (beta_id, beta) = b.fresh_local(sort_v.clone());
        let (f_id, _) = b.fresh_local(Expr::arrow(a.clone(), beta.clone()));
        let r = b.mk_pi(
            f_id,
            BinderInfo::Default,
            Expr::arrow(a.clone(), beta.clone()),
            prop.clone(),
        );
        let r = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, sort_u.clone(), r);
        b.finish(r)
    };

    let value = {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a) = b.fresh_local(sort_u.clone());
        let (beta_id, beta) = b.fresh_local(sort_v.clone());
        let (f_id, f) = b.fresh_local(Expr::arrow(a.clone(), beta.clone()));
        let (a1_id, a1) = b.fresh_local(a.clone());
        let (a2_id, a2) = b.fresh_local(a.clone());
        let eq_v = Expr::const_(Name::from_string("Eq"), vec![v_level.clone()]);
        let fa1_eq_fa2 = Expr::app(
            Expr::app(
                Expr::app(eq_v, beta.clone()),
                Expr::app(f.clone(), a1.clone()),
            ),
            Expr::app(f.clone(), a2.clone()),
        );
        let (h_id, _) = b.fresh_local(fa1_eq_fa2.clone());
        let eq_u = Expr::const_(Name::from_string("Eq"), vec![u_level.clone()]);
        let a1_eq_a2 = Expr::app(
            Expr::app(Expr::app(eq_u, a.clone()), a1.clone()),
            a2.clone(),
        );
        let r = b.mk_pi(h_id, BinderInfo::Default, fa1_eq_fa2, a1_eq_a2);
        let r = b.mk_pi(a2_id, BinderInfo::StrictImplicit, a.clone(), r);
        let r = b.mk_pi(a1_id, BinderInfo::StrictImplicit, a.clone(), r);
        let r = b.mk_lam(
            f_id,
            BinderInfo::Default,
            Expr::arrow(a.clone(), beta.clone()),
            r,
        );
        let r = b.mk_lam(beta_id, BinderInfo::Implicit, sort_v.clone(), r);
        let r = b.mk_lam(a_id, BinderInfo::Implicit, sort_u.clone(), r);
        b.finish(r)
    };

    ConstantInfo {
        name: Name::from_string("Function.Injective"),
        level_params: vec![u, v],
        type_,
        value: Some(value),
        is_reducible: true,
        reducibility: Reducibility::Reducible,
        kind: ConstantKind::Axiom,
    }
}

// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] →
//   {f : X → Y} → IsEmbedding f → Function.Injective f
fn build_is_embedding_injective_type(ctx: &EmbeddingCtx) -> ConstantInfo {
    let (mut b, x, y, ix, iy, f, x_id, y_id, ix_id, iy_id, f_id) = ctx.xy_topo_f_prefix();
    let is_emb = ctx.is_embedding_app(&x, &y, &ix, &iy, &f);
    let (h_id, _) = b.fresh_local(is_emb.clone());
    let inj_f = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Function.Injective"),
                    vec![
                        Level::succ(ctx.u_level.clone()),
                        Level::succ(ctx.u_level.clone()),
                    ],
                ),
                x.clone(),
            ),
            y.clone(),
        ),
        f.clone(),
    );
    let body = b.mk_pi(h_id, BinderInfo::Default, is_emb, inj_f);
    let r = ctx.close_xy_topo_f(
        &mut b,
        &x,
        &y,
        x_id,
        y_id,
        ix_id,
        iy_id,
        f_id,
        BinderInfo::Implicit,
        body,
    );
    ctx.to_axiom_info("Topology.IsEmbedding.injective", b.finish(r))
}

// {X : Type u} → [TopologicalSpace X] → (A : X → Prop) →
//   [TopologicalSpace (Subtype A)] → IsEmbedding (Subtype.val : Subtype A → X)
fn build_inclusion_embedding_type(ctx: &EmbeddingCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (a_id, a) = b.fresh_local(Expr::arrow(x.clone(), ctx.prop.clone()));
    let subtype_a = ctx.subtype(x.clone(), a.clone());
    let (isa_id, isa) = b.fresh_local(Expr::app(ctx.topological_space(), subtype_a.clone()));
    let subtype_val = ctx.subtype_val(x.clone(), a.clone());
    let body = ctx.is_embedding_app(&subtype_a, &x, &isa, &ix, &subtype_val);
    let r = b.mk_pi(
        isa_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), subtype_a),
        body,
    );
    let r = b.mk_pi(
        a_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), ctx.prop.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.inclusion_embedding", b.finish(r))
}

// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] → (X → Y) → Prop
fn build_is_open_embedding_type(ctx: &EmbeddingCtx) -> ConstantInfo {
    let (mut b, x, y, _, _, _, x_id, y_id, ix_id, iy_id, f_id) = ctx.xy_topo_f_prefix();
    let r = ctx.close_xy_topo_f(
        &mut b,
        &x,
        &y,
        x_id,
        y_id,
        ix_id,
        iy_id,
        f_id,
        BinderInfo::Default,
        ctx.prop.clone(),
    );
    ctx.to_axiom_info("Topology.IsOpenEmbedding", b.finish(r))
}

// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] → (X → Y) → Prop
fn build_is_closed_embedding_type(ctx: &EmbeddingCtx) -> ConstantInfo {
    let (mut b, x, y, _, _, _, x_id, y_id, ix_id, iy_id, f_id) = ctx.xy_topo_f_prefix();
    let r = ctx.close_xy_topo_f(
        &mut b,
        &x,
        &y,
        x_id,
        y_id,
        ix_id,
        iy_id,
        f_id,
        BinderInfo::Default,
        ctx.prop.clone(),
    );
    ctx.to_axiom_info("Topology.IsClosedEmbedding", b.finish(r))
}

// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] →
//   {f : X → Y} → IsOpenEmbedding f → IsEmbedding f
fn build_open_embedding_to_is_embedding_type(ctx: &EmbeddingCtx) -> ConstantInfo {
    let (mut b, x, y, ix, iy, f, x_id, y_id, ix_id, iy_id, f_id) = ctx.xy_topo_f_prefix();
    let is_oe = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(ctx.is_open_embedding_const(), x.clone()),
                    y.clone(),
                ),
                ix.clone(),
            ),
            iy.clone(),
        ),
        f.clone(),
    );
    let (h_id, _) = b.fresh_local(is_oe.clone());
    let is_emb = ctx.is_embedding_app(&x, &y, &ix, &iy, &f);
    let body = b.mk_pi(h_id, BinderInfo::Default, is_oe, is_emb);
    let r = ctx.close_xy_topo_f(
        &mut b,
        &x,
        &y,
        x_id,
        y_id,
        ix_id,
        iy_id,
        f_id,
        BinderInfo::Implicit,
        body,
    );
    ctx.to_axiom_info("Topology.IsOpenEmbedding.toIsEmbedding", b.finish(r))
}

// {X Y : Type u} → [TopologicalSpace X] → [TopologicalSpace Y] →
//   {f : X → Y} → IsClosedEmbedding f → IsEmbedding f
fn build_closed_embedding_to_is_embedding_type(ctx: &EmbeddingCtx) -> ConstantInfo {
    let (mut b, x, y, ix, iy, f, x_id, y_id, ix_id, iy_id, f_id) = ctx.xy_topo_f_prefix();
    let is_ce = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(ctx.is_closed_embedding_const(), x.clone()),
                    y.clone(),
                ),
                ix.clone(),
            ),
            iy.clone(),
        ),
        f.clone(),
    );
    let (h_id, _) = b.fresh_local(is_ce.clone());
    let is_emb = ctx.is_embedding_app(&x, &y, &ix, &iy, &f);
    let body = b.mk_pi(h_id, BinderInfo::Default, is_ce, is_emb);
    let r = ctx.close_xy_topo_f(
        &mut b,
        &x,
        &y,
        x_id,
        y_id,
        ix_id,
        iy_id,
        f_id,
        BinderInfo::Implicit,
        body,
    );
    ctx.to_axiom_info("Topology.IsClosedEmbedding.toIsEmbedding", b.finish(r))
}

// {X : Type u} → [TopologicalSpace X] → (A : X → Prop) →
//   [TopologicalSpace (Subtype A)] → IsOpen A → IsOpenEmbedding (Subtype.val)
fn build_open_embedding_of_open_inclusion_type(ctx: &EmbeddingCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (a_id, a) = b.fresh_local(Expr::arrow(x.clone(), ctx.prop.clone()));
    let subtype_a = ctx.subtype(x.clone(), a.clone());
    let (isa_id, isa) = b.fresh_local(Expr::app(ctx.topological_space(), subtype_a.clone()));
    let is_open_a = Expr::app(
        Expr::app(Expr::app(ctx.is_open(), x.clone()), ix.clone()),
        a.clone(),
    );
    let (ho_id, _) = b.fresh_local(is_open_a.clone());
    let subtype_val = ctx.subtype_val(x.clone(), a.clone());
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(ctx.is_open_embedding_const(), subtype_a.clone()),
                    x.clone(),
                ),
                isa.clone(),
            ),
            ix.clone(),
        ),
        subtype_val,
    );
    let r = b.mk_pi(ho_id, BinderInfo::Default, is_open_a, body);
    let r = b.mk_pi(
        isa_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), subtype_a),
        r,
    );
    let r = b.mk_pi(
        a_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), ctx.prop.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.open_embedding_of_open_inclusion", b.finish(r))
}

// {X : Type u} → [TopologicalSpace X] → (A : X → Prop) →
//   [TopologicalSpace (Subtype A)] → IsClosed A → IsClosedEmbedding (Subtype.val)
fn build_closed_embedding_of_closed_inclusion_type(ctx: &EmbeddingCtx) -> ConstantInfo {
    let mut b = EnvDeclBuilder::new();
    let (x_id, x) = b.fresh_local(ctx.type_u.clone());
    let (ix_id, ix) = b.fresh_local(Expr::app(ctx.topological_space(), x.clone()));
    let (a_id, a) = b.fresh_local(Expr::arrow(x.clone(), ctx.prop.clone()));
    let subtype_a = ctx.subtype(x.clone(), a.clone());
    let (isa_id, isa) = b.fresh_local(Expr::app(ctx.topological_space(), subtype_a.clone()));
    let is_closed_a = Expr::app(
        Expr::app(Expr::app(ctx.is_closed(), x.clone()), ix.clone()),
        a.clone(),
    );
    let (hc_id, _) = b.fresh_local(is_closed_a.clone());
    let subtype_val = ctx.subtype_val(x.clone(), a.clone());
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(ctx.is_closed_embedding_const(), subtype_a.clone()),
                    x.clone(),
                ),
                isa.clone(),
            ),
            ix.clone(),
        ),
        subtype_val,
    );
    let r = b.mk_pi(hc_id, BinderInfo::Default, is_closed_a, body);
    let r = b.mk_pi(
        isa_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), subtype_a),
        r,
    );
    let r = b.mk_pi(
        a_id,
        BinderInfo::Default,
        Expr::arrow(x.clone(), ctx.prop.clone()),
        r,
    );
    let r = b.mk_pi(
        ix_id,
        BinderInfo::InstImplicit,
        Expr::app(ctx.topological_space(), x.clone()),
        r,
    );
    let r = b.mk_pi(x_id, BinderInfo::Implicit, ctx.type_u.clone(), r);
    ctx.to_axiom_info("Topology.closed_embedding_of_closed_inclusion", b.finish(r))
}
