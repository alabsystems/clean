// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.Homology namespace (#1444).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.Homology";
pub(crate) const DECL_COUNT: usize = 22;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.Homology.SingularChain",
    "Topology.Homology.ChainComplex",
    "Topology.Homology.boundary",
    "Topology.Homology.boundary_sq_zero",
    "Topology.Homology.H",
    "Topology.Homology.Cohomology",
    "Topology.Homology.H_is_group",
    "Topology.Homology.induced",
    "Topology.Homology.functoriality",
    "Topology.Homology.exact_sequence",
    "Topology.Homology.mayer_vietoris",
    "Topology.Homology.excision",
    "Topology.Homology.H_zero",
    "Topology.Homology.cup_product",
    "Topology.Homology.long_exact_pair",
    "Topology.Homology.homotopy_invariance",
    "Topology.Homology.dimension_axiom",
    "Topology.Homology.hurewicz",
    "Topology.Homology.hurewicz_theorem",
    "Topology.Homology.relative",
    "Topology.Homology.betti",
    "Topology.Homology.euler_poincare",
];

struct HomologyCtx {
    u: Name,
    v: Name,
    u_level: Level,
    v_level: Level,
    type_u: Expr,
    type_v: Expr,
    prop: Expr,
}

impl HomologyCtx {
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

    fn int_const(&self) -> Expr {
        Expr::const_(Name::from_string("Int"), vec![])
    }

    fn topological_space(&self, level: Level) -> Expr {
        Expr::const_(Name::from_string("TopologicalSpace"), vec![level])
    }

    fn to_axiom_u(&self, name: &str, type_: Expr) -> ConstantInfo {
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

    fn to_axiom_uv(&self, name: &str, type_: Expr) -> ConstantInfo {
        ConstantInfo {
            name: Name::from_string(name),
            level_params: vec![self.u.clone(), self.v.clone()],
            type_,
            value: None,
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            kind: ConstantKind::Axiom,
        }
    }

    fn to_axiom_no_levels(&self, name: &str, type_: Expr) -> ConstantInfo {
        ConstantInfo {
            name: Name::from_string(name),
            level_params: vec![],
            type_,
            value: None,
            is_reducible: false,
            reducibility: Reducibility::Regular(0),
            kind: ConstantKind::Axiom,
        }
    }

    /// {X : Type u} → [TopologicalSpace X] → <ret>
    fn build_ts_type_u(&self, ret: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x);
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, ret);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// (n : Nat) → {X : Type u} → [TopologicalSpace X] → <ret>
    fn build_nat_ts_type(&self, ret: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let nat_ty = self.nat_const();
        let (n_id, _) = b.fresh_local(nat_ty.clone());
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x);
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, ret);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e);
        b.mk_pi(n_id, BinderInfo::Default, nat_ty, e)
    }

    /// ChainComplex : {R : Type u} → [Ring R] → Type (u+1)
    fn build_chain_complex_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (r_id, r) = b.fresh_local(self.type_u.clone());
        let ring_ty = Expr::app(
            Expr::const_(Name::from_string("Ring"), vec![self.u_level.clone()]),
            r,
        );
        let (ri_id, _) = b.fresh_local(ring_ty.clone());
        let ret = Expr::sort(Level::succ(Level::succ(self.u_level.clone())));
        let e = b.mk_pi(ri_id, BinderInfo::InstImplicit, ring_ty, ret);
        b.mk_pi(r_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// boundary : {X} → [TS X] → {n : Nat} → SingularChain (n+1) X → SingularChain n X
    fn build_boundary_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x.clone());
        let (ts_id, ts) = b.fresh_local(ts_ty.clone());
        let nat_ty = self.nat_const();
        let (n_id, n) = b.fresh_local(nat_ty.clone());
        let singular_chain = Expr::const_(
            Name::from_string("Topology.Homology.SingularChain"),
            vec![self.u_level.clone()],
        );
        let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
        let chain_succ = Expr::app(
            Expr::app(
                Expr::app(singular_chain.clone(), Expr::app(nat_succ, n.clone())),
                x.clone(),
            ),
            ts.clone(),
        );
        let chain_n = Expr::app(Expr::app(Expr::app(singular_chain, n), x), ts);
        let (c_id, _) = b.fresh_local(chain_succ.clone());
        let e = b.mk_pi(c_id, BinderInfo::Default, chain_succ, chain_n);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// {X} → [TS X] → {n : Nat} → Prop
    fn build_boundary_sq_zero_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x);
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let nat_ty = self.nat_const();
        let (n_id, _) = b.fresh_local(nat_ty.clone());
        let e = b.mk_pi(n_id, BinderInfo::Implicit, nat_ty, self.prop.clone());
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// H_is_group : (n : Nat) → {X} → [TS X] → AddCommGroup (H n X)
    fn build_h_is_group_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let nat_ty = self.nat_const();
        let (n_id, n) = b.fresh_local(nat_ty.clone());
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x.clone());
        let (ts_id, ts) = b.fresh_local(ts_ty.clone());
        let h_n_x = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Topology.Homology.H"),
                        vec![self.u_level.clone()],
                    ),
                    n,
                ),
                x,
            ),
            ts,
        );
        let ret = Expr::app(
            Expr::const_(
                Name::from_string("AddCommGroup"),
                vec![self.u_level.clone()],
            ),
            h_n_x,
        );
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, ret);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e);
        b.mk_pi(n_id, BinderInfo::Default, nat_ty, e)
    }

    /// induced : {X : Type u} → {Y : Type v} → [TS X] → [TS Y] → (f : X → Y) → (n : Nat) → Prop
    fn build_induced_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (y_id, y) = b.fresh_local(self.type_v.clone());
        let ts_x_ty = Expr::app(self.topological_space(self.u_level.clone()), x.clone());
        let (tsx_id, _) = b.fresh_local(ts_x_ty.clone());
        let ts_y_ty = Expr::app(self.topological_space(self.v_level.clone()), y.clone());
        let (tsy_id, _) = b.fresh_local(ts_y_ty.clone());
        let f_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (a_id, _) = c.fresh_local(x.clone());
            let r = c.mk_pi(a_id, BinderInfo::Default, x.clone(), y.clone());
            c.finish_child(r)
        };
        let (f_id, _) = b.fresh_local(f_ty.clone());
        let nat_ty = self.nat_const();
        let (n_id, _) = b.fresh_local(nat_ty.clone());
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_ty, self.prop.clone());
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
        let e = b.mk_pi(tsy_id, BinderInfo::InstImplicit, ts_y_ty, e);
        let e = b.mk_pi(tsx_id, BinderInfo::InstImplicit, ts_x_ty, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, self.type_v.clone(), e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// cup_product : {X} → [TS X] → Nat → Nat → Prop
    fn build_cup_product_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x);
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let nat_ty = self.nat_const();
        let (n_id, _) = b.fresh_local(nat_ty.clone());
        let (m_id, _) = b.fresh_local(nat_ty.clone());
        let e = b.mk_pi(m_id, BinderInfo::Default, nat_ty.clone(), self.prop.clone());
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_ty, e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// long_exact_pair : {X} → [TS X] → (A : X → Prop) → Prop
    fn build_long_exact_pair_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x.clone());
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let a_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (p_id, _) = c.fresh_local(x.clone());
            let r = c.mk_pi(p_id, BinderInfo::Default, x.clone(), self.prop.clone());
            c.finish_child(r)
        };
        let (a_id, _) = b.fresh_local(a_ty.clone());
        let e = b.mk_pi(a_id, BinderInfo::Default, a_ty, self.prop.clone());
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// homotopy_invariance : {X : Type u} → {Y : Type v} → [TS X] → [TS Y] → Prop
    fn build_homotopy_invariance_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (y_id, y) = b.fresh_local(self.type_v.clone());
        let ts_x_ty = Expr::app(self.topological_space(self.u_level.clone()), x);
        let (tsx_id, _) = b.fresh_local(ts_x_ty.clone());
        let ts_y_ty = Expr::app(self.topological_space(self.v_level.clone()), y);
        let (tsy_id, _) = b.fresh_local(ts_y_ty.clone());
        let e = b.mk_pi(tsy_id, BinderInfo::InstImplicit, ts_y_ty, self.prop.clone());
        let e = b.mk_pi(tsx_id, BinderInfo::InstImplicit, ts_x_ty, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, self.type_v.clone(), e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// {X} → [TS X] → Nat → Prop
    fn build_ts_nat_prop(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x);
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let nat_ty = self.nat_const();
        let (n_id, _) = b.fresh_local(nat_ty.clone());
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_ty, self.prop.clone());
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// relative : (n : Nat) → {X} → [TS X] → (A : X → Prop) → Type u
    fn build_relative_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let nat_ty = self.nat_const();
        let (n_id, _) = b.fresh_local(nat_ty.clone());
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x.clone());
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let a_ty = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (p_id, _) = c.fresh_local(x.clone());
            let r = c.mk_pi(p_id, BinderInfo::Default, x.clone(), self.prop.clone());
            c.finish_child(r)
        };
        let (a_id, _) = b.fresh_local(a_ty.clone());
        let e = b.mk_pi(a_id, BinderInfo::Default, a_ty, self.type_u.clone());
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e);
        b.mk_pi(n_id, BinderInfo::Default, nat_ty, e)
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = HomologyCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    // SingularChain : (n : Nat) → {X : Type u} → [TS X] → Type u
    decls.push(ctx.to_axiom_u(
        "Topology.Homology.SingularChain",
        ctx.build_nat_ts_type(ctx.type_u.clone()),
    ));

    // ChainComplex : {R : Type u} → [Ring R] → Type (u+1)
    decls.push(ctx.to_axiom_u(
        "Topology.Homology.ChainComplex",
        ctx.build_chain_complex_type(),
    ));

    // boundary
    decls.push(ctx.to_axiom_u("Topology.Homology.boundary", ctx.build_boundary_type()));

    // boundary_sq_zero
    decls.push(ctx.to_axiom_u(
        "Topology.Homology.boundary_sq_zero",
        ctx.build_boundary_sq_zero_type(),
    ));

    // H, Cohomology : (n : Nat) → {X} → [TS X] → Type u
    for name in ["Topology.Homology.H", "Topology.Homology.Cohomology"] {
        decls.push(ctx.to_axiom_u(name, ctx.build_nat_ts_type(ctx.type_u.clone())));
    }

    // H_is_group
    decls.push(ctx.to_axiom_u("Topology.Homology.H_is_group", ctx.build_h_is_group_type()));

    // induced (dual-universe)
    decls.push(ctx.to_axiom_uv("Topology.Homology.induced", ctx.build_induced_type()));

    // functoriality, exact_sequence, mayer_vietoris, excision, H_zero :
    // {X} → [TS X] → Prop
    let ts_prop = ctx.build_ts_type_u(ctx.prop.clone());
    for name in [
        "Topology.Homology.functoriality",
        "Topology.Homology.exact_sequence",
        "Topology.Homology.mayer_vietoris",
        "Topology.Homology.excision",
        "Topology.Homology.H_zero",
    ] {
        decls.push(ctx.to_axiom_u(name, ts_prop.clone()));
    }

    // cup_product
    decls.push(ctx.to_axiom_u(
        "Topology.Homology.cup_product",
        ctx.build_cup_product_type(),
    ));

    // long_exact_pair
    decls.push(ctx.to_axiom_u(
        "Topology.Homology.long_exact_pair",
        ctx.build_long_exact_pair_type(),
    ));

    // homotopy_invariance (dual-universe)
    decls.push(ctx.to_axiom_uv(
        "Topology.Homology.homotopy_invariance",
        ctx.build_homotopy_invariance_type(),
    ));

    // dimension_axiom : Nat → Prop (no level params)
    decls.push(ctx.to_axiom_no_levels(
        "Topology.Homology.dimension_axiom",
        Expr::pi(BinderInfo::Default, ctx.nat_const(), ctx.prop.clone()),
    ));

    // hurewicz, hurewicz_theorem : {X} → [TS X] → Nat → Prop
    let ts_nat_prop = ctx.build_ts_nat_prop();
    for name in [
        "Topology.Homology.hurewicz",
        "Topology.Homology.hurewicz_theorem",
    ] {
        decls.push(ctx.to_axiom_u(name, ts_nat_prop.clone()));
    }

    // relative
    decls.push(ctx.to_axiom_u("Topology.Homology.relative", ctx.build_relative_type()));

    // betti : (n : Nat) → {X} → [TS X] → Nat
    decls.push(ctx.to_axiom_u(
        "Topology.Homology.betti",
        ctx.build_nat_ts_type(ctx.nat_const()),
    ));

    // euler_poincare : {X} → [TS X] → Int
    decls.push(ctx.to_axiom_u(
        "Topology.Homology.euler_poincare",
        ctx.build_ts_type_u(ctx.int_const()),
    ));

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
