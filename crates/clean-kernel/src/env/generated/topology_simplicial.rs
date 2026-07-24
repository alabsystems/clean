// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.SimplicialComplex namespace (#1444).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.SimplicialComplex";
pub(crate) const DECL_COUNT: usize = 16;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.SimplicialComplex",
    "Topology.SimplicialComplex.simplex",
    "Topology.SimplicialComplex.homology",
    "Topology.SimplicialComplex.cohomology",
    "Topology.SimplicialComplex.face",
    "Topology.SimplicialComplex.degeneracy",
    "Topology.SimplicialComplex.geometric_realization",
    "Topology.SimplicialComplex.chain_complex",
    "Topology.SimplicialComplex.link",
    "Topology.SimplicialComplex.star",
    "Topology.SimplicialComplex.euler_characteristic",
    "Topology.SimplicialComplex.realization_topology",
    "Topology.SimplicialComplex.realization_continuous",
    "Topology.SimplicialComplex.barycentric_subdivision",
    "Topology.SimplicialComplex.subcomplex",
    "Topology.SimplicialComplex.realization_to_cw",
];

struct SimplicialCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl SimplicialCtx {
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

    fn nat_const(&self) -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
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

    fn simplicial_complex(&self, v: Expr) -> Expr {
        Expr::app(
            Expr::const_(
                Name::from_string("Topology.SimplicialComplex"),
                vec![self.u_level.clone()],
            ),
            v,
        )
    }

    fn cw_complex(&self, x: Expr, ts: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Topology.CWComplex"),
                    vec![self.u_level.clone()],
                ),
                x,
            ),
            ts,
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

    /// {V : Type u} → SimplicialComplex V → <ret>
    fn build_sc_type(&self, ret: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (v_id, v) = b.fresh_local(self.type_u.clone());
        let sc_ty = self.simplicial_complex(v);
        let (sc_id, _) = b.fresh_local(sc_ty.clone());
        let e = b.mk_pi(sc_id, BinderInfo::Default, sc_ty, ret);
        b.mk_pi(v_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// {V : Type u} → SimplicialComplex V → Nat → <ret>
    fn build_sc_nat_type(&self, ret: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (v_id, v) = b.fresh_local(self.type_u.clone());
        let sc_ty = self.simplicial_complex(v);
        let (sc_id, _) = b.fresh_local(sc_ty.clone());
        let nat_ty = self.nat_const();
        let (n_id, _) = b.fresh_local(nat_ty.clone());
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_ty, ret);
        let e = b.mk_pi(sc_id, BinderInfo::Default, sc_ty, e);
        b.mk_pi(v_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// {V : Type u} → SimplicialComplex V → SimplicialComplex V
    fn build_sc_to_sc_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (v_id, v) = b.fresh_local(self.type_u.clone());
        let sc_ty = self.simplicial_complex(v.clone());
        let (sc_id, _) = b.fresh_local(sc_ty.clone());
        let ret = self.simplicial_complex(v);
        let e = b.mk_pi(sc_id, BinderInfo::Default, sc_ty, ret);
        b.mk_pi(v_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// {V : Type u} → [TopologicalSpace V] → SimplicialComplex V → <ret>
    fn build_ts_sc_type(&self, ret: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (v_id, v) = b.fresh_local(self.type_u.clone());
        let ts_ty = self.topological_space(v.clone());
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let sc_ty = self.simplicial_complex(v);
        let (sc_id, _) = b.fresh_local(sc_ty.clone());
        let e = b.mk_pi(sc_id, BinderInfo::Default, sc_ty, ret);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(v_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// {V : Type u} → [TopologicalSpace V] → SimplicialComplex V → TopologicalSpace V
    fn build_realization_topology_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (v_id, v) = b.fresh_local(self.type_u.clone());
        let ts_ty = self.topological_space(v.clone());
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let sc_ty = self.simplicial_complex(v.clone());
        let (sc_id, _) = b.fresh_local(sc_ty.clone());
        let ret = self.topological_space(v);
        let e = b.mk_pi(sc_id, BinderInfo::Default, sc_ty, ret);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(v_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// {V : Type u} → [TopologicalSpace V] → SimplicialComplex V → CWComplex V
    fn build_realization_to_cw_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (v_id, v) = b.fresh_local(self.type_u.clone());
        let ts_ty = self.topological_space(v.clone());
        let (ts_id, ts) = b.fresh_local(ts_ty.clone());
        let sc_ty = self.simplicial_complex(v.clone());
        let (sc_id, _) = b.fresh_local(sc_ty.clone());
        let ret = self.cw_complex(v, ts);
        let e = b.mk_pi(sc_id, BinderInfo::Default, sc_ty, ret);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(v_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = SimplicialCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    // SimplicialComplex : {V : Type u} → Type u
    decls.push(ctx.to_axiom(
        "Topology.SimplicialComplex",
        Expr::pi(BinderInfo::Implicit, ctx.type_u.clone(), ctx.type_u.clone()),
    ));

    // simplex, homology, cohomology : {V} → SimplicialComplex V → Nat → Type u
    for name in [
        "Topology.SimplicialComplex.simplex",
        "Topology.SimplicialComplex.homology",
        "Topology.SimplicialComplex.cohomology",
    ] {
        decls.push(ctx.to_axiom(name, ctx.build_sc_nat_type(ctx.type_u.clone())));
    }

    // face, degeneracy : {V} → SimplicialComplex V → Nat → Prop
    for name in [
        "Topology.SimplicialComplex.face",
        "Topology.SimplicialComplex.degeneracy",
    ] {
        decls.push(ctx.to_axiom(name, ctx.build_sc_nat_type(ctx.prop.clone())));
    }

    // geometric_realization, chain_complex, link, star, euler_characteristic :
    // {V} → SimplicialComplex V → Type u
    for name in [
        "Topology.SimplicialComplex.geometric_realization",
        "Topology.SimplicialComplex.chain_complex",
        "Topology.SimplicialComplex.link",
        "Topology.SimplicialComplex.star",
        "Topology.SimplicialComplex.euler_characteristic",
    ] {
        decls.push(ctx.to_axiom(name, ctx.build_sc_type(ctx.type_u.clone())));
    }

    // realization_topology : {V} → [TS V] → SimplicialComplex V → TopologicalSpace V
    decls.push(ctx.to_axiom(
        "Topology.SimplicialComplex.realization_topology",
        ctx.build_realization_topology_type(),
    ));

    // realization_continuous : {V} → [TS V] → SimplicialComplex V → Prop
    decls.push(ctx.to_axiom(
        "Topology.SimplicialComplex.realization_continuous",
        ctx.build_ts_sc_type(ctx.prop.clone()),
    ));

    // barycentric_subdivision, subcomplex : {V} → SimplicialComplex V → SimplicialComplex V
    let sc_to_sc = ctx.build_sc_to_sc_type();
    for name in [
        "Topology.SimplicialComplex.barycentric_subdivision",
        "Topology.SimplicialComplex.subcomplex",
    ] {
        decls.push(ctx.to_axiom(name, sc_to_sc.clone()));
    }

    // realization_to_cw : {V} → [TS V] → SimplicialComplex V → CWComplex V
    decls.push(ctx.to_axiom(
        "Topology.SimplicialComplex.realization_to_cw",
        ctx.build_realization_to_cw_type(),
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
