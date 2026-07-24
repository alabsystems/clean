// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.Filtration namespace (#1444).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.Filtration";
pub(crate) const DECL_COUNT: usize = 18;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.Filtration.Filtration",
    "Topology.Filtration.level",
    "Topology.Filtration.associated_graded",
    "Topology.Filtration.is_increasing",
    "Topology.Filtration.bounded_below",
    "Topology.Filtration.exhaustive",
    "Topology.Filtration.separated",
    "Topology.Filtration.complete",
    "Topology.Filtration.finite_length",
    "Topology.Filtration.shift",
    "Topology.Filtration.morphism",
    "Topology.Filtration.compatible",
    "Topology.Filtration.FilteredComplex",
    "Topology.Filtration.filtered_boundary_compatible",
    "Topology.Filtration.associated_graded_complex",
    "Topology.Filtration.induced_filtration_on_homology",
    "Topology.Filtration.exhaustive_complete_equiv",
    "Topology.Filtration.topology_from_filtration",
];

struct FiltrationCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl FiltrationCtx {
    fn new() -> Self {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        Self {
            u,
            u_level: u_level.clone(),
            type_u: Expr::sort(Level::succ(u_level)),
            prop: Expr::sort(Level::zero()),
        }
    }

    fn int_const(&self) -> Expr {
        Expr::const_(Name::from_string("Int"), vec![])
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

    fn ring_class(&self, r: Expr) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Ring"), vec![self.u_level.clone()]),
            r,
        )
    }

    fn filtration_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Filtration.Filtration"),
            vec![self.u_level.clone()],
        )
    }

    fn filtered_complex_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Filtration.FilteredComplex"),
            vec![self.u_level.clone()],
        )
    }

    fn filtration_of(&self, x: Expr) -> Expr {
        Expr::app(self.filtration_const(), x)
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

    fn build_filtration_type(&self) -> Expr {
        Expr::pi(
            BinderInfo::Default,
            self.type_u.clone(),
            self.type_u.clone(),
        )
    }

    fn build_level_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let filtration_x = self.filtration_of(x);
        let (fx_id, _) = b.fresh_local(filtration_x.clone());
        let (n_id, _) = b.fresh_local(self.int_const());
        let r = b.mk_pi(
            n_id,
            BinderInfo::Default,
            self.int_const(),
            self.type_u.clone(),
        );
        let r = b.mk_pi(fx_id, BinderInfo::Default, filtration_x, r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    fn build_property_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let filtration_x = self.filtration_of(x);
        let (fx_id, _) = b.fresh_local(filtration_x.clone());
        let r = b.mk_pi(fx_id, BinderInfo::Default, filtration_x, self.prop.clone());
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    fn build_shift_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let filtration_x = self.filtration_of(x);
        let (fx_id, _) = b.fresh_local(filtration_x.clone());
        let (n_id, _) = b.fresh_local(self.int_const());
        let r = b.mk_pi(
            n_id,
            BinderInfo::Default,
            self.int_const(),
            filtration_x.clone(),
        );
        let r = b.mk_pi(fx_id, BinderInfo::Default, filtration_x, r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    fn build_morphism_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let (y_id, y) = b.fresh_local(self.type_u.clone());
        let fx_ty = self.filtration_of(x.clone());
        let fy_ty = self.filtration_of(y.clone());
        let (fx_id, _) = b.fresh_local(fx_ty.clone());
        let (fy_id, _) = b.fresh_local(fy_ty.clone());
        let map_ty = Expr::arrow(x, y);
        let (map_id, _) = b.fresh_local(map_ty.clone());

        let r = b.mk_pi(map_id, BinderInfo::Default, map_ty, self.prop.clone());
        let r = b.mk_pi(fy_id, BinderInfo::Default, fy_ty, r);
        let r = b.mk_pi(fx_id, BinderInfo::Default, fx_ty, r);
        let r = b.mk_pi(y_id, BinderInfo::Implicit, self.type_u.clone(), r);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    fn build_filtered_complex_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (r_id, r) = b.fresh_local(self.type_u.clone());
        let ring_r = self.ring_class(r);
        let (ring_id, _) = b.fresh_local(ring_r.clone());
        let sort_u_plus_2 = Expr::sort(Level::succ(Level::succ(self.u_level.clone())));
        let r = b.mk_pi(ring_id, BinderInfo::InstImplicit, ring_r, sort_u_plus_2);
        b.finish(b.mk_pi(r_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    fn build_filtered_complex_to(&self, ret: Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (r_id, r) = b.fresh_local(self.type_u.clone());
        let ring_r = self.ring_class(r.clone());
        let (ring_id, ring_inst) = b.fresh_local(ring_r.clone());
        let fc_ty = Expr::app(
            Expr::app(self.filtered_complex_const(), r),
            ring_inst.clone(),
        );
        let (fc_id, _) = b.fresh_local(fc_ty.clone());
        let r = b.mk_pi(fc_id, BinderInfo::Default, fc_ty, ret);
        let r = b.mk_pi(ring_id, BinderInfo::InstImplicit, ring_r, r);
        b.finish(b.mk_pi(r_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    fn build_topology_from_filtration_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let filtration_x = self.filtration_of(x.clone());
        let (fx_id, _) = b.fresh_local(filtration_x.clone());
        let topology_x = self.topological_space(x);
        let r = b.mk_pi(fx_id, BinderInfo::Default, filtration_x, topology_x);
        b.finish(b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = FiltrationCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    decls.push(ctx.to_axiom(
        "Topology.Filtration.Filtration",
        ctx.build_filtration_type(),
    ));
    decls.push(ctx.to_axiom("Topology.Filtration.level", ctx.build_level_type()));
    decls.push(ctx.to_axiom(
        "Topology.Filtration.associated_graded",
        ctx.build_level_type(),
    ));

    let property_type = ctx.build_property_type();
    for name in [
        "Topology.Filtration.is_increasing",
        "Topology.Filtration.bounded_below",
        "Topology.Filtration.exhaustive",
        "Topology.Filtration.separated",
        "Topology.Filtration.complete",
        "Topology.Filtration.finite_length",
    ] {
        decls.push(ctx.to_axiom(name, property_type.clone()));
    }

    decls.push(ctx.to_axiom("Topology.Filtration.shift", ctx.build_shift_type()));
    decls.push(ctx.to_axiom("Topology.Filtration.morphism", ctx.build_morphism_type()));
    decls.push(ctx.to_axiom("Topology.Filtration.compatible", property_type.clone()));
    decls.push(ctx.to_axiom(
        "Topology.Filtration.FilteredComplex",
        ctx.build_filtered_complex_type(),
    ));
    decls.push(ctx.to_axiom(
        "Topology.Filtration.filtered_boundary_compatible",
        ctx.build_filtered_complex_to(ctx.prop.clone()),
    ));
    decls.push(ctx.to_axiom(
        "Topology.Filtration.associated_graded_complex",
        ctx.build_filtered_complex_to(ctx.type_u.clone()),
    ));
    decls.push(ctx.to_axiom(
        "Topology.Filtration.induced_filtration_on_homology",
        ctx.build_filtered_complex_to(ctx.prop.clone()),
    ));
    decls.push(ctx.to_axiom(
        "Topology.Filtration.exhaustive_complete_equiv",
        property_type,
    ));
    decls.push(ctx.to_axiom(
        "Topology.Filtration.topology_from_filtration",
        ctx.build_topology_from_filtration_type(),
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
