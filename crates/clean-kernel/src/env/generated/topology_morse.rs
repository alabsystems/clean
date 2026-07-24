// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.Morse namespace (#1444).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.Morse";
pub(crate) const DECL_COUNT: usize = 26;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.Morse.MorseFunction",
    "Topology.Morse.CriticalPoint",
    "Topology.Morse.Nondegenerate",
    "Topology.Morse.MorseIndex",
    "Topology.Morse.MorseLemma",
    "Topology.Morse.GradientFlow",
    "Topology.Morse.gradient_flow_exists",
    "Topology.Morse.StableManifold",
    "Topology.Morse.UnstableManifold",
    "Topology.Morse.MorseSmale",
    "Topology.Morse.SublevelFiltration",
    "Topology.Morse.MorseComplex",
    "Topology.Morse.morse_differential",
    "Topology.Morse.morse_d_squared_zero",
    "Topology.Morse.MorseHomology",
    "Topology.Morse.morse_homology_eq_singular",
    "Topology.Morse.morse_inequalities",
    "Topology.Morse.perfect_morse_function",
    "Topology.Morse.palais_smale_condition",
    "Topology.Morse.handle_decomposition",
    "Topology.Morse.handle_slides",
    "Topology.Morse.witten_deformation",
    "Topology.Morse.sard_for_morse",
    "Topology.Morse.homology_of_sublevel",
    "Topology.Morse.morse_smash_product",
    "Topology.Morse.riemannian_metric",
];

struct MorseCtx {
    u: Name,
    u_level: Level,
    type_u: Expr,
    prop: Expr,
}

impl MorseCtx {
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

    fn nat_const(&self) -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
    }

    fn rat_const(&self) -> Expr {
        Expr::const_(Name::from_string("Rat"), vec![])
    }

    fn topological_space(&self, m: Expr) -> Expr {
        Expr::app(
            Expr::const_(
                Name::from_string("TopologicalSpace"),
                vec![self.u_level.clone()],
            ),
            m,
        )
    }

    fn smooth_manifold_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.DeRham.SmoothManifold"),
            vec![self.u_level.clone()],
        )
    }

    fn filtration_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Filtration.Filtration"),
            vec![self.u_level.clone()],
        )
    }

    fn morse_complex_const(&self) -> Expr {
        Expr::const_(
            Name::from_string("Topology.Morse.MorseComplex"),
            vec![self.u_level.clone()],
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

    fn mk_m_to_rat(&self, b: &EnvDeclBuilder, m: &Expr) -> Expr {
        let mut c = EnvDeclBuilder::child_of(b);
        let (x_id, _) = c.fresh_local(m.clone());
        let r = c.mk_pi(x_id, BinderInfo::Default, m.clone(), self.rat_const());
        c.finish_child(r)
    }

    /// `{M : Type u} → [TopologicalSpace M] → {n : Nat} → (M → Rat) → Prop`
    fn build_ts_dim_f_prop(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let ts_ty = self.topological_space(m.clone());
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let (dim_id, _) = b.fresh_local(self.nat_const());
        let f_ty = self.mk_m_to_rat(&b, &m);
        let (f_id, _) = b.fresh_local(f_ty.clone());

        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, self.prop.clone());
        let r = b.mk_pi(dim_id, BinderInfo::Implicit, self.nat_const(), r);
        let r = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, r);
        b.finish(b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    /// `{M : Type u} → [TopologicalSpace M] → {n : Nat} → (M → Rat) → M → Prop`
    fn build_ts_dim_f_point_prop(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let ts_ty = self.topological_space(m.clone());
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let (dim_id, _) = b.fresh_local(self.nat_const());
        let f_ty = self.mk_m_to_rat(&b, &m);
        let (f_id, _) = b.fresh_local(f_ty.clone());
        let (x_id, _) = b.fresh_local(m.clone());

        let r = b.mk_pi(x_id, BinderInfo::Default, m, self.prop.clone());
        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
        let r = b.mk_pi(dim_id, BinderInfo::Implicit, self.nat_const(), r);
        let r = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, r);
        b.finish(b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    /// `{M : Type u} → [TopologicalSpace M] → {n : Nat} → (M → Rat) → M → Nat`
    fn build_ts_dim_f_point_nat(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let ts_ty = self.topological_space(m.clone());
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let (dim_id, _) = b.fresh_local(self.nat_const());
        let f_ty = self.mk_m_to_rat(&b, &m);
        let (f_id, _) = b.fresh_local(f_ty.clone());
        let (x_id, _) = b.fresh_local(m.clone());

        let r = b.mk_pi(x_id, BinderInfo::Default, m, self.nat_const());
        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
        let r = b.mk_pi(dim_id, BinderInfo::Implicit, self.nat_const(), r);
        let r = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, r);
        b.finish(b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    /// `{M : Type u} → {n : Nat} → (M → Rat) → Prop`
    fn build_dim_f_prop(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let (dim_id, _) = b.fresh_local(self.nat_const());
        let f_ty = self.mk_m_to_rat(&b, &m);
        let (f_id, _) = b.fresh_local(f_ty.clone());

        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, self.prop.clone());
        let r = b.mk_pi(dim_id, BinderInfo::Implicit, self.nat_const(), r);
        b.finish(b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    /// `{M : Type u} → {n : Nat} → (M → Rat) → Type u`
    fn build_dim_f_type_u(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let (dim_id, _) = b.fresh_local(self.nat_const());
        let f_ty = self.mk_m_to_rat(&b, &m);
        let (f_id, _) = b.fresh_local(f_ty.clone());

        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, self.type_u.clone());
        let r = b.mk_pi(dim_id, BinderInfo::Implicit, self.nat_const(), r);
        b.finish(b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    /// `{M : Type u} → {n : Nat} → (M → Rat) → Filtration M`
    fn build_dim_f_filtration(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let (dim_id, _) = b.fresh_local(self.nat_const());
        let f_ty = self.mk_m_to_rat(&b, &m);
        let (f_id, _) = b.fresh_local(f_ty.clone());

        let filtration_m = Expr::app(self.filtration_const(), m);
        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, filtration_m);
        let r = b.mk_pi(dim_id, BinderInfo::Implicit, self.nat_const(), r);
        b.finish(b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    /// `{M : Type u} → [TopologicalSpace M] → {n : Nat} → (M → Rat) → M → Rat → M`
    fn build_gradient_flow_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let ts_ty = self.topological_space(m.clone());
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let (dim_id, _) = b.fresh_local(self.nat_const());
        let f_ty = self.mk_m_to_rat(&b, &m);
        let (f_id, _) = b.fresh_local(f_ty.clone());
        let (x_id, _) = b.fresh_local(m.clone());
        let (t_id, _) = b.fresh_local(self.rat_const());

        let r = b.mk_pi(t_id, BinderInfo::Default, self.rat_const(), m.clone());
        let r = b.mk_pi(x_id, BinderInfo::Default, m, r);
        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
        let r = b.mk_pi(dim_id, BinderInfo::Implicit, self.nat_const(), r);
        let r = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, r);
        b.finish(b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    /// `{M : Type u} → {n : Nat} → (M → Rat) → MorseComplex M n f → MorseComplex M n f`
    fn build_morse_differential_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let (dim_id, dim) = b.fresh_local(self.nat_const());
        let f_ty = self.mk_m_to_rat(&b, &m);
        let (f_id, f) = b.fresh_local(f_ty.clone());

        let complex = Expr::app(
            Expr::app(Expr::app(self.morse_complex_const(), m.clone()), dim),
            f,
        );
        let (d_id, _) = b.fresh_local(complex.clone());

        let r = b.mk_pi(d_id, BinderInfo::Default, complex.clone(), complex);
        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
        let r = b.mk_pi(dim_id, BinderInfo::Implicit, self.nat_const(), r);
        b.finish(b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }

    /// `{M : Type u} → {n : Nat} → (sm : SmoothManifold M n) → Type u`
    fn build_riemannian_metric_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (m_id, m) = b.fresh_local(self.type_u.clone());
        let (n_id, n) = b.fresh_local(self.nat_const());

        let manifold = Expr::app(Expr::app(self.smooth_manifold_const(), m), n);
        let (sm_id, _) = b.fresh_local(manifold.clone());

        let r = b.mk_pi(sm_id, BinderInfo::Default, manifold, self.type_u.clone());
        let r = b.mk_pi(n_id, BinderInfo::Implicit, self.nat_const(), r);
        b.finish(b.mk_pi(m_id, BinderInfo::Implicit, self.type_u.clone(), r))
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = MorseCtx::new();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    let ts_dim_f_prop = ctx.build_ts_dim_f_prop();
    let ts_dim_f_point_prop = ctx.build_ts_dim_f_point_prop();
    let dim_f_prop = ctx.build_dim_f_prop();
    let dim_f_type_u = ctx.build_dim_f_type_u();

    decls.push(ctx.to_axiom("Topology.Morse.MorseFunction", ts_dim_f_prop.clone()));
    decls.push(ctx.to_axiom("Topology.Morse.CriticalPoint", ts_dim_f_point_prop.clone()));
    decls.push(ctx.to_axiom("Topology.Morse.Nondegenerate", ts_dim_f_point_prop.clone()));
    decls.push(ctx.to_axiom("Topology.Morse.MorseIndex", ctx.build_ts_dim_f_point_nat()));
    decls.push(ctx.to_axiom("Topology.Morse.MorseLemma", ts_dim_f_prop.clone()));
    decls.push(ctx.to_axiom(
        "Topology.Morse.GradientFlow",
        ctx.build_gradient_flow_type(),
    ));
    decls.push(ctx.to_axiom("Topology.Morse.gradient_flow_exists", ts_dim_f_prop));
    decls.push(ctx.to_axiom("Topology.Morse.StableManifold", ts_dim_f_point_prop.clone()));
    decls.push(ctx.to_axiom("Topology.Morse.UnstableManifold", ts_dim_f_point_prop));
    decls.push(ctx.to_axiom("Topology.Morse.MorseSmale", ctx.build_ts_dim_f_prop()));
    decls.push(ctx.to_axiom(
        "Topology.Morse.SublevelFiltration",
        ctx.build_dim_f_filtration(),
    ));
    decls.push(ctx.to_axiom("Topology.Morse.MorseComplex", dim_f_type_u.clone()));
    decls.push(ctx.to_axiom(
        "Topology.Morse.morse_differential",
        ctx.build_morse_differential_type(),
    ));
    decls.push(ctx.to_axiom("Topology.Morse.morse_d_squared_zero", dim_f_prop.clone()));
    decls.push(ctx.to_axiom("Topology.Morse.MorseHomology", dim_f_type_u));

    for name in [
        "Topology.Morse.morse_homology_eq_singular",
        "Topology.Morse.morse_inequalities",
        "Topology.Morse.perfect_morse_function",
        "Topology.Morse.palais_smale_condition",
        "Topology.Morse.handle_decomposition",
    ] {
        decls.push(ctx.to_axiom(name, dim_f_prop.clone()));
    }

    decls.push(ctx.to_axiom("Topology.Morse.handle_slides", ctx.prop.clone()));

    for name in [
        "Topology.Morse.witten_deformation",
        "Topology.Morse.sard_for_morse",
        "Topology.Morse.homology_of_sublevel",
        "Topology.Morse.morse_smash_product",
    ] {
        decls.push(ctx.to_axiom(name, dim_f_prop.clone()));
    }
    decls.push(ctx.to_axiom(
        "Topology.Morse.riemannian_metric",
        ctx.build_riemannian_metric_type(),
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
