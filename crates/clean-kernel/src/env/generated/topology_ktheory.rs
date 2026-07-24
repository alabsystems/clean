// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for Topology.KTheory namespace (#1444).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.KTheory";
pub(crate) const DECL_COUNT: usize = 30;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.KTheory.K",
    "Topology.KTheory.K_zero",
    "Topology.KTheory.K_neg_one",
    "Topology.KTheory.K_is_add_comm_group",
    "Topology.KTheory.K_zero_is_ring",
    "Topology.KTheory.VectorBundleClass",
    "Topology.KTheory.grothendieck_completion",
    "Topology.KTheory.functoriality",
    "Topology.KTheory.reduced_splitting",
    "Topology.KTheory.chern_is_ring_hom",
    "Topology.KTheory.chern_isomorphism",
    "Topology.KTheory.exact_sequence",
    "Topology.KTheory.homotopy_invariance",
    "Topology.KTheory.thom_isomorphism",
    "Topology.KTheory.atiyah_hirzebruch",
    "Topology.KTheory.wedge_axiom",
    "Topology.KTheory.split_exact",
    "Topology.KTheory.bott_periodicity",
    "Topology.KTheory.suspension_iso",
    "Topology.KTheory.adams_operation",
    "Topology.KTheory.adams_ring_hom",
    "Topology.KTheory.adams_composition",
    "Topology.KTheory.induced",
    "Topology.KTheory.ReducedK",
    "Topology.KTheory.tensor_product",
    "Topology.KTheory.chern_character",
    "Topology.KTheory.K_sphere",
    "Topology.KTheory.K_point",
    "Topology.KTheory.dimension",
    "Topology.KTheory.clutching",
];

struct KTheoryCtx {
    u: Name,
    v: Name,
    u_level: Level,
    v_level: Level,
    type_u: Expr,
    type_v: Expr,
    prop: Expr,
}

impl KTheoryCtx {
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

    fn k_group(&self, level: Level) -> Expr {
        Expr::const_(Name::from_string("Topology.KTheory.K"), vec![level])
    }

    fn k_zero(&self, level: Level) -> Expr {
        Expr::const_(Name::from_string("Topology.KTheory.K_zero"), vec![level])
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

    /// K_is_add_comm_group : {X : Type u} → [TS X] → {n : Int} → AddCommGroup (K X n)
    fn build_k_is_group_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x.clone());
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let int_ty = self.int_const();
        let (n_id, n) = b.fresh_local(int_ty.clone());
        let k_xn = Expr::app(Expr::app(self.k_group(self.u_level.clone()), x), n);
        let ret = Expr::app(
            Expr::const_(
                Name::from_string("AddCommGroup"),
                vec![self.u_level.clone()],
            ),
            k_xn,
        );
        let e = b.mk_pi(n_id, BinderInfo::Implicit, int_ty, ret);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// K_zero_is_ring : {X : Type u} → [TS X] → Ring (K_zero X)
    fn build_k_zero_is_ring_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x.clone());
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let ret = Expr::app(
            Expr::const_(Name::from_string("Ring"), vec![self.u_level.clone()]),
            Expr::app(self.k_zero(self.u_level.clone()), x),
        );
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, ret);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// VectorBundleClass : {X} → [TS X] → {E : Type u} → [TS E] → (E → X) → K_zero(X)
    fn build_vb_class_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_x_ty = Expr::app(self.topological_space(self.u_level.clone()), x.clone());
        let (tsx_id, _) = b.fresh_local(ts_x_ty.clone());
        let (e_id, e) = b.fresh_local(self.type_u.clone());
        let ts_e_ty = Expr::app(self.topological_space(self.u_level.clone()), e.clone());
        let (tse_id, _) = b.fresh_local(ts_e_ty.clone());
        let pi_ty = Expr::pi(BinderInfo::Default, e, x.clone());
        let (pi_id, _) = b.fresh_local(pi_ty.clone());
        let ret = Expr::app(self.k_zero(self.u_level.clone()), x);
        let r = b.mk_pi(pi_id, BinderInfo::Default, pi_ty, ret);
        let r = b.mk_pi(tse_id, BinderInfo::InstImplicit, ts_e_ty, r);
        let r = b.mk_pi(e_id, BinderInfo::Implicit, self.type_u.clone(), r);
        let r = b.mk_pi(tsx_id, BinderInfo::InstImplicit, ts_x_ty, r);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), r)
    }

    /// {X} → [TS X] → {n : Int} → Prop
    fn build_ts_int_prop(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x);
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let int_ty = self.int_const();
        let (n_id, _) = b.fresh_local(int_ty.clone());
        let e = b.mk_pi(n_id, BinderInfo::Implicit, int_ty, self.prop.clone());
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// adams_operation : {X} → [TS X] → (k : Nat) → K_zero(X) → K_zero(X)
    fn build_adams_operation_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x.clone());
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let nat_ty = self.nat_const();
        let (k_id, _) = b.fresh_local(nat_ty.clone());
        let k0_x = Expr::app(self.k_zero(self.u_level.clone()), x);
        let (a_id, _) = b.fresh_local(k0_x.clone());
        let e = b.mk_pi(a_id, BinderInfo::Default, k0_x.clone(), k0_x);
        let e = b.mk_pi(k_id, BinderInfo::Default, nat_ty, e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// {X} → [TS X] → {k : Nat} → {l : Nat} → Prop
    fn build_ts_nat_nat_prop(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x);
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let nat_ty = self.nat_const();
        let (k_id, _) = b.fresh_local(nat_ty.clone());
        let (l_id, _) = b.fresh_local(nat_ty.clone());
        let e = b.mk_pi(
            l_id,
            BinderInfo::Implicit,
            nat_ty.clone(),
            self.prop.clone(),
        );
        let e = b.mk_pi(k_id, BinderInfo::Implicit, nat_ty, e);
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// induced : {X} → [TS X] → {Y : Type v} → [TS Y] → {f : X→Y} → Continuous(f) → {n : Int} → K(Y,n) → K(X,n)
    fn build_induced_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_x_ty = Expr::app(self.topological_space(self.u_level.clone()), x.clone());
        let (tsx_id, tsx) = b.fresh_local(ts_x_ty.clone());
        let (y_id, y) = b.fresh_local(self.type_v.clone());
        let ts_y_ty = Expr::app(self.topological_space(self.v_level.clone()), y.clone());
        let (tsy_id, tsy) = b.fresh_local(ts_y_ty.clone());
        let f_ty = Expr::pi(BinderInfo::Default, x.clone(), y.clone());
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let continuous = Expr::const_(
            Name::from_string("Topology.Continuous"),
            vec![self.u_level.clone(), self.v_level.clone()],
        );
        let cont_proof_ty = Expr::app(
            Expr::app(
                Expr::app(Expr::app(Expr::app(continuous, x.clone()), y.clone()), tsx),
                tsy,
            ),
            f,
        );
        let (cont_id, _) = b.fresh_local(cont_proof_ty.clone());
        let int_ty = self.int_const();
        let (n_id, n) = b.fresh_local(int_ty.clone());
        let k_y_n = Expr::app(Expr::app(self.k_group(self.v_level.clone()), y), n.clone());
        let (kyn_id, _) = b.fresh_local(k_y_n.clone());
        let ret = Expr::app(Expr::app(self.k_group(self.u_level.clone()), x), n);
        let e = b.mk_pi(kyn_id, BinderInfo::Default, k_y_n, ret);
        let e = b.mk_pi(n_id, BinderInfo::Implicit, int_ty, e);
        let e = b.mk_pi(cont_id, BinderInfo::Default, cont_proof_ty, e);
        let e = b.mk_pi(f_id, BinderInfo::Implicit, f_ty, e);
        let e = b.mk_pi(tsy_id, BinderInfo::InstImplicit, ts_y_ty, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, self.type_v.clone(), e);
        let e = b.mk_pi(tsx_id, BinderInfo::InstImplicit, ts_x_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// tensor_product : {X} → [TS X] → {Y : Type v} → [TS Y] → K_zero(X) → K_zero(Y) → Type u
    fn build_tensor_product_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_x_ty = Expr::app(self.topological_space(self.u_level.clone()), x.clone());
        let (tsx_id, _) = b.fresh_local(ts_x_ty.clone());
        let (y_id, y) = b.fresh_local(self.type_v.clone());
        let ts_y_ty = Expr::app(self.topological_space(self.v_level.clone()), y.clone());
        let (tsy_id, _) = b.fresh_local(ts_y_ty.clone());
        let k0_x = Expr::app(self.k_zero(self.u_level.clone()), x);
        let k0_y = Expr::app(self.k_zero(self.v_level.clone()), y);
        let (a_id, _) = b.fresh_local(k0_x.clone());
        let (b2_id, _) = b.fresh_local(k0_y.clone());
        let e = b.mk_pi(b2_id, BinderInfo::Default, k0_y, self.type_u.clone());
        let e = b.mk_pi(a_id, BinderInfo::Default, k0_x, e);
        let e = b.mk_pi(tsy_id, BinderInfo::InstImplicit, ts_y_ty, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, self.type_v.clone(), e);
        let e = b.mk_pi(tsx_id, BinderInfo::InstImplicit, ts_x_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// chern_character : {X} → [TS X] → K_zero(X) → Type u
    fn build_chern_character_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x.clone());
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let k0_x = Expr::app(self.k_zero(self.u_level.clone()), x);
        let (a_id, _) = b.fresh_local(k0_x.clone());
        let e = b.mk_pi(a_id, BinderInfo::Default, k0_x, self.type_u.clone());
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }

    /// dimension : {X} → [TS X] → K_zero(X) → Int
    fn build_dimension_type(&self) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(self.type_u.clone());
        let ts_ty = Expr::app(self.topological_space(self.u_level.clone()), x.clone());
        let (ts_id, _) = b.fresh_local(ts_ty.clone());
        let k0_x = Expr::app(self.k_zero(self.u_level.clone()), x);
        let (a_id, _) = b.fresh_local(k0_x.clone());
        let e = b.mk_pi(a_id, BinderInfo::Default, k0_x, self.int_const());
        let e = b.mk_pi(ts_id, BinderInfo::InstImplicit, ts_ty, e);
        b.mk_pi(x_id, BinderInfo::Implicit, self.type_u.clone(), e)
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let ctx = KTheoryCtx::new();
    let nat_ty = ctx.nat_const();
    let int_ty = ctx.int_const();
    let mut decls = Vec::with_capacity(DECL_COUNT);

    // K : Type u → Int → Type u
    decls.push(ctx.to_axiom_u(
        "Topology.KTheory.K",
        Expr::pi(
            BinderInfo::Default,
            ctx.type_u.clone(),
            Expr::pi(BinderInfo::Default, int_ty.clone(), ctx.type_u.clone()),
        ),
    ));

    // K_zero : Type u → Type u
    decls.push(ctx.to_axiom_u(
        "Topology.KTheory.K_zero",
        Expr::pi(BinderInfo::Default, ctx.type_u.clone(), ctx.type_u.clone()),
    ));

    // K_neg_one : Type u → Type u
    decls.push(ctx.to_axiom_u(
        "Topology.KTheory.K_neg_one",
        Expr::pi(BinderInfo::Default, ctx.type_u.clone(), ctx.type_u.clone()),
    ));

    // K_is_add_comm_group
    decls.push(ctx.to_axiom_u(
        "Topology.KTheory.K_is_add_comm_group",
        ctx.build_k_is_group_type(),
    ));

    // K_zero_is_ring
    decls.push(ctx.to_axiom_u(
        "Topology.KTheory.K_zero_is_ring",
        ctx.build_k_zero_is_ring_type(),
    ));

    // VectorBundleClass
    decls.push(ctx.to_axiom_u(
        "Topology.KTheory.VectorBundleClass",
        ctx.build_vb_class_type(),
    ));

    // 11 declarations sharing {X : Type u} → [TS X] → Prop
    let ts_prop = ctx.build_ts_type_u(ctx.prop.clone());
    for name in [
        "Topology.KTheory.grothendieck_completion",
        "Topology.KTheory.functoriality",
        "Topology.KTheory.reduced_splitting",
        "Topology.KTheory.chern_is_ring_hom",
        "Topology.KTheory.chern_isomorphism",
        "Topology.KTheory.exact_sequence",
        "Topology.KTheory.homotopy_invariance",
        "Topology.KTheory.thom_isomorphism",
        "Topology.KTheory.atiyah_hirzebruch",
        "Topology.KTheory.wedge_axiom",
        "Topology.KTheory.split_exact",
    ] {
        decls.push(ctx.to_axiom_u(name, ts_prop.clone()));
    }

    // bott_periodicity, suspension_iso : {X} → [TS X] → {n : Int} → Prop
    let ts_int_prop = ctx.build_ts_int_prop();
    for name in [
        "Topology.KTheory.bott_periodicity",
        "Topology.KTheory.suspension_iso",
    ] {
        decls.push(ctx.to_axiom_u(name, ts_int_prop.clone()));
    }

    // adams_operation
    decls.push(ctx.to_axiom_u(
        "Topology.KTheory.adams_operation",
        ctx.build_adams_operation_type(),
    ));

    // adams_ring_hom, adams_composition : {X} → [TS X] → {k : Nat} → {l : Nat} → Prop
    let ts_nn_prop = ctx.build_ts_nat_nat_prop();
    decls.push(ctx.to_axiom_u("Topology.KTheory.adams_ring_hom", ts_nn_prop.clone()));
    decls.push(ctx.to_axiom_u("Topology.KTheory.adams_composition", ts_nn_prop));

    // induced (dual-universe)
    decls.push(ctx.to_axiom_uv("Topology.KTheory.induced", ctx.build_induced_type()));

    // ReducedK : Type u → Int → Type u
    decls.push(ctx.to_axiom_u(
        "Topology.KTheory.ReducedK",
        Expr::pi(
            BinderInfo::Default,
            ctx.type_u.clone(),
            Expr::pi(BinderInfo::Default, int_ty, ctx.type_u.clone()),
        ),
    ));

    // tensor_product (dual-universe)
    decls.push(ctx.to_axiom_uv(
        "Topology.KTheory.tensor_product",
        ctx.build_tensor_product_type(),
    ));

    // chern_character
    decls.push(ctx.to_axiom_u(
        "Topology.KTheory.chern_character",
        ctx.build_chern_character_type(),
    ));

    // K_sphere : (n : Nat) → Prop (no level params)
    decls.push(ctx.to_axiom_no_levels(
        "Topology.KTheory.K_sphere",
        Expr::pi(BinderInfo::Default, nat_ty.clone(), ctx.prop.clone()),
    ));

    // K_point : Prop (no level params)
    decls.push(ctx.to_axiom_no_levels("Topology.KTheory.K_point", ctx.prop.clone()));

    // dimension
    decls.push(ctx.to_axiom_u("Topology.KTheory.dimension", ctx.build_dimension_type()));

    // clutching : {n : Nat} → {k : Nat} → Prop (no level params)
    decls.push(ctx.to_axiom_no_levels(
        "Topology.KTheory.clutching",
        Expr::pi(
            BinderInfo::Implicit,
            nat_ty.clone(),
            Expr::pi(BinderInfo::Implicit, nat_ty, ctx.prop.clone()),
        ),
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
