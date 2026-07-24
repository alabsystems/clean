// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.CW namespace (#1444).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.CW";
pub(crate) const DECL_COUNT: usize = 15;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.CWComplex",
    "Topology.CWComplex.skeleton",
    "Topology.CWComplex.cell",
    "Topology.CWComplex.attach_cell",
    "Topology.CWComplex.characteristic_map",
    "Topology.CWComplex.closure_finite",
    "Topology.CWComplex.weak_topology",
    "Topology.CWComplex.homotopy_extension",
    "Topology.CWComplex.whitehead",
    "Topology.CWComplex.cellular_approximation",
    "Topology.CWComplex.cw_on_subset",
    "Topology.CWComplex.connectivity",
    "Topology.CWComplex.attaching_map_continuous",
    "Topology.CWComplex.subcomplex",
    "Topology.CWComplex.cellular_homology",
];

struct CwCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl CwCtx {
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

    /// {X : Type u} → [TopologicalSpace X] → <ret>
    fn build_ts_type(&self, ret: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = self.topological_space(x);
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, ret);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// {X : Type u} → [TopologicalSpace X] → CWComplex X → Nat → <ret>
    fn build_cw_nat_type(&self, ret: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = self.topological_space(x.clone());
        let (ts_id, ts) = b.fresh_local(ts_ty.clone());
        let cw_ty = self.cw_complex(x, ts);
        let (cw_id, _) = b.fresh_local(cw_ty.clone());
        let nat_ty = self.nat_const();
        let (n_id, _) = b.fresh_local(nat_ty.clone());
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_ty, ret);
        let e = b.mk_pi(cw_id, BinderInfo::Default, cw_ty, e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// {X : Type u} → [TopologicalSpace X] → Nat → <ret>
    fn build_ts_nat_type(&self, ret: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = self.topological_space(x);
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let nat_ty = self.nat_const();
        let (n_id, _) = b.fresh_local(nat_ty.clone());
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_ty, ret);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = CwCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    // CWComplex : {X : Type u} → [TopologicalSpace X] → Type u
    decls.push(ctx.to_axiom("Topology.CWComplex", ctx.build_ts_type(ctx.type_u.clone())));

    // skeleton, cell : {X} → [TS X] → CWComplex X → Nat → Type u
    for name in ["Topology.CWComplex.skeleton", "Topology.CWComplex.cell"] {
        decls.push(ctx.to_axiom(name, ctx.build_cw_nat_type(ctx.type_u.clone())));
    }

    // attach_cell : {X} → [TS X] → CWComplex X → Nat → Prop
    decls.push(ctx.to_axiom(
        "Topology.CWComplex.attach_cell",
        ctx.build_cw_nat_type(ctx.prop.clone()),
    ));

    // 9 declarations sharing {X : Type u} → [TopologicalSpace X] → Prop
    let ts_prop = ctx.build_ts_type(ctx.prop.clone());
    for name in [
        "Topology.CWComplex.characteristic_map",
        "Topology.CWComplex.closure_finite",
        "Topology.CWComplex.weak_topology",
        "Topology.CWComplex.homotopy_extension",
        "Topology.CWComplex.whitehead",
        "Topology.CWComplex.cellular_approximation",
        "Topology.CWComplex.cw_on_subset",
        "Topology.CWComplex.connectivity",
        "Topology.CWComplex.attaching_map_continuous",
    ] {
        decls.push(ctx.to_axiom(name, ts_prop.clone()));
    }

    // subcomplex : {X : Type u} → [TopologicalSpace X] → Type u
    decls.push(ctx.to_axiom(
        "Topology.CWComplex.subcomplex",
        ctx.build_ts_type(ctx.type_u.clone()),
    ));

    // cellular_homology : {X : Type u} → [TopologicalSpace X] → Nat → Type u
    decls.push(ctx.to_axiom(
        "Topology.CWComplex.cellular_homology",
        ctx.build_ts_nat_type(ctx.type_u.clone()),
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
