// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for `Topology.FundamentalGroup` namespace (#1444).
//!
//! Migrated from handwritten `add_decl` calls in `topology_homotopy2.rs`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.FundamentalGroup";
pub(crate) const DECL_COUNT: usize = 15;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.FundamentalGroup",
    "Topology.FundamentalGroup.class",
    "Topology.FundamentalGroup.class_eq",
    "Topology.FundamentalGroup.mul",
    "Topology.FundamentalGroup.one",
    "Topology.FundamentalGroup.inv",
    "Topology.FundamentalGroup.mul_assoc",
    "Topology.FundamentalGroup.mul_one",
    "Topology.FundamentalGroup.one_mul",
    "Topology.FundamentalGroup.mul_inv",
    "Topology.FundamentalGroup.inv_mul",
    "Topology.FundamentalGroup.IsTrivial",
    "Topology.FundamentalGroup.trivial_def",
    "Topology.simply_connected_iff_trivial_pi1",
    "Topology.FundamentalGroup.basepoint_change",
];

fn axiom(name: &str, level_params: Vec<Name>, type_: Expr) -> ConstantInfo {
    ConstantInfo {
        name: Name::from_string(name),
        level_params,
        type_,
        value: None,
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Axiom,
    }
}

pub(crate) fn payload() -> Vec<ConstantInfo> {
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());
    let type_u = Expr::sort(Level::succ(u_level.clone()));
    let prop = Expr::sort(Level::zero());

    let topological_space =
        |lvl: Level| Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl]);
    let topology_loop = |lvl: Level| Expr::const_(Name::from_string("Topology.Loop"), vec![lvl]);
    let topology_loop_homotopy =
        |lvl: Level| Expr::const_(Name::from_string("Topology.LoopHomotopy"), vec![lvl]);
    let topology_simply_connected =
        |lvl: Level| Expr::const_(Name::from_string("Topology.SimplyConnected"), vec![lvl]);
    let topology_path_connected =
        |lvl: Level| Expr::const_(Name::from_string("Topology.PathConnected"), vec![lvl]);
    let eq_const = |lvl: Level| Expr::const_(Name::from_string("Eq"), vec![lvl]);
    let iff_const = || Expr::const_(Name::from_string("Iff"), vec![]);
    let fundamental_group =
        |lvl: Level| Expr::const_(Name::from_string("Topology.FundamentalGroup"), vec![lvl]);
    let fg_class = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.FundamentalGroup.class"),
            vec![lvl],
        )
    };
    let fg_mul = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.FundamentalGroup.mul"),
            vec![lvl],
        )
    };
    let fg_one = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.FundamentalGroup.one"),
            vec![lvl],
        )
    };
    let fg_inv = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.FundamentalGroup.inv"),
            vec![lvl],
        )
    };
    let fg_is_trivial = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.FundamentalGroup.IsTrivial"),
            vec![lvl],
        )
    };

    let mut decls = Vec::with_capacity(DECL_COUNT);

    // 1. Topology.FundamentalGroup : {α : Type u} → [TopologicalSpace α] → α → Type u
    let fundamental_group_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, _inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, _x0) = b.fresh_local(alpha.clone());
        let e = type_u.clone();
        let e = b.mk_pi(x0_id, BinderInfo::Default, alpha.clone(), e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.FundamentalGroup",
        vec![u.clone()],
        fundamental_group_type,
    ));

    // 2. Topology.FundamentalGroup.class
    let class_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let loop_x0 = Expr::apps(
            topology_loop(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let (gamma_id, _gamma) = b.fresh_local(loop_x0.clone());
        let fg_x0 = Expr::apps(
            fundamental_group(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let e = fg_x0;
        let e = b.mk_pi(gamma_id, BinderInfo::Default, loop_x0, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.FundamentalGroup.class",
        vec![u.clone()],
        class_type,
    ));

    // 3. Topology.FundamentalGroup.class_eq
    let class_eq_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let loop_x0 = Expr::apps(
            topology_loop(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let (g1_id, g1) = b.fresh_local(loop_x0.clone());
        let (g2_id, g2) = b.fresh_local(loop_x0.clone());
        let lh_g1_g2 = Expr::apps(
            topology_loop_homotopy(u_level.clone()),
            [
                alpha.clone(),
                inst.clone(),
                x0.clone(),
                g1.clone(),
                g2.clone(),
            ],
        );
        let (h_id, _h) = b.fresh_local(lh_g1_g2.clone());
        let fg_x0 = Expr::apps(
            fundamental_group(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let class_g1 = Expr::apps(
            fg_class(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone(), g1],
        );
        let class_g2 = Expr::apps(
            fg_class(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone(), g2],
        );
        let eq_body = Expr::apps(
            eq_const(Level::succ(u_level.clone())),
            [fg_x0, class_g1, class_g2],
        );
        let e = eq_body;
        let e = b.mk_pi(h_id, BinderInfo::Default, lh_g1_g2, e);
        let e = b.mk_pi(g2_id, BinderInfo::Implicit, loop_x0.clone(), e);
        let e = b.mk_pi(g1_id, BinderInfo::Implicit, loop_x0, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.FundamentalGroup.class_eq",
        vec![u.clone()],
        class_eq_type,
    ));

    // 4. Topology.FundamentalGroup.mul
    let mul_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let fg_x0 = Expr::apps(
            fundamental_group(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let (a_id, _a) = b.fresh_local(fg_x0.clone());
        let (b_id2, _b) = b.fresh_local(fg_x0.clone());
        let e = fg_x0.clone();
        let e = b.mk_pi(b_id2, BinderInfo::Default, fg_x0.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Default, fg_x0, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.FundamentalGroup.mul",
        vec![u.clone()],
        mul_type,
    ));

    // 5. Topology.FundamentalGroup.one
    let one_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let fg_x0 = Expr::apps(
            fundamental_group(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let e = fg_x0;
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.FundamentalGroup.one",
        vec![u.clone()],
        one_type,
    ));

    // 6. Topology.FundamentalGroup.inv
    let inv_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let fg_x0 = Expr::apps(
            fundamental_group(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let (a_id, _a) = b.fresh_local(fg_x0.clone());
        let e = fg_x0.clone();
        let e = b.mk_pi(a_id, BinderInfo::Default, fg_x0, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.FundamentalGroup.inv",
        vec![u.clone()],
        inv_type,
    ));

    // 7. Topology.FundamentalGroup.mul_assoc
    let mul_assoc_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let fg_x0 = Expr::apps(
            fundamental_group(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let (a_id, a) = b.fresh_local(fg_x0.clone());
        let (b_id2, bv) = b.fresh_local(fg_x0.clone());
        let (c_id, c) = b.fresh_local(fg_x0.clone());
        let mul_a_b = Expr::apps(
            fg_mul(u_level.clone()),
            [
                alpha.clone(),
                inst.clone(),
                x0.clone(),
                a.clone(),
                bv.clone(),
            ],
        );
        let mul_mul_a_b_c = Expr::apps(
            fg_mul(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone(), mul_a_b, c.clone()],
        );
        let mul_b_c = Expr::apps(
            fg_mul(u_level.clone()),
            [
                alpha.clone(),
                inst.clone(),
                x0.clone(),
                bv.clone(),
                c.clone(),
            ],
        );
        let mul_a_mul_b_c = Expr::apps(
            fg_mul(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone(), a.clone(), mul_b_c],
        );
        let eq_body = Expr::apps(
            eq_const(Level::succ(u_level.clone())),
            [fg_x0.clone(), mul_mul_a_b_c, mul_a_mul_b_c],
        );
        let e = eq_body;
        let e = b.mk_pi(c_id, BinderInfo::Default, fg_x0.clone(), e);
        let e = b.mk_pi(b_id2, BinderInfo::Default, fg_x0.clone(), e);
        let e = b.mk_pi(a_id, BinderInfo::Default, fg_x0, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.FundamentalGroup.mul_assoc",
        vec![u.clone()],
        mul_assoc_type,
    ));

    // 8. Topology.FundamentalGroup.mul_one
    let mul_one_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let fg_x0 = Expr::apps(
            fundamental_group(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let (a_id, a) = b.fresh_local(fg_x0.clone());
        let one = Expr::apps(
            fg_one(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let mul_a_one = Expr::apps(
            fg_mul(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone(), a.clone(), one],
        );
        let eq_body = Expr::apps(
            eq_const(Level::succ(u_level.clone())),
            [fg_x0.clone(), mul_a_one, a.clone()],
        );
        let e = eq_body;
        let e = b.mk_pi(a_id, BinderInfo::Default, fg_x0, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.FundamentalGroup.mul_one",
        vec![u.clone()],
        mul_one_type,
    ));

    // 9. Topology.FundamentalGroup.one_mul
    let one_mul_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let fg_x0 = Expr::apps(
            fundamental_group(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let (a_id, a) = b.fresh_local(fg_x0.clone());
        let one = Expr::apps(
            fg_one(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let mul_one_a = Expr::apps(
            fg_mul(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone(), one, a.clone()],
        );
        let eq_body = Expr::apps(
            eq_const(Level::succ(u_level.clone())),
            [fg_x0.clone(), mul_one_a, a.clone()],
        );
        let e = eq_body;
        let e = b.mk_pi(a_id, BinderInfo::Default, fg_x0, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.FundamentalGroup.one_mul",
        vec![u.clone()],
        one_mul_type,
    ));

    // 10. Topology.FundamentalGroup.mul_inv
    let mul_inv_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let fg_x0 = Expr::apps(
            fundamental_group(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let (a_id, a) = b.fresh_local(fg_x0.clone());
        let inv_a = Expr::apps(
            fg_inv(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone(), a.clone()],
        );
        let mul_a_inv = Expr::apps(
            fg_mul(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone(), a.clone(), inv_a],
        );
        let one = Expr::apps(
            fg_one(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let eq_body = Expr::apps(
            eq_const(Level::succ(u_level.clone())),
            [fg_x0.clone(), mul_a_inv, one],
        );
        let e = eq_body;
        let e = b.mk_pi(a_id, BinderInfo::Default, fg_x0, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.FundamentalGroup.mul_inv",
        vec![u.clone()],
        mul_inv_type,
    ));

    // 11. Topology.FundamentalGroup.inv_mul
    let inv_mul_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let fg_x0 = Expr::apps(
            fundamental_group(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let (a_id, a) = b.fresh_local(fg_x0.clone());
        let inv_a = Expr::apps(
            fg_inv(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone(), a.clone()],
        );
        let mul_inv_a = Expr::apps(
            fg_mul(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone(), inv_a, a.clone()],
        );
        let one = Expr::apps(
            fg_one(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let eq_body = Expr::apps(
            eq_const(Level::succ(u_level.clone())),
            [fg_x0.clone(), mul_inv_a, one],
        );
        let e = eq_body;
        let e = b.mk_pi(a_id, BinderInfo::Default, fg_x0, e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.FundamentalGroup.inv_mul",
        vec![u.clone()],
        inv_mul_type,
    ));

    // 12. Topology.FundamentalGroup.IsTrivial
    let is_trivial_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let _fg_x0 = Expr::apps(
            fundamental_group(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let e = prop.clone();
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.FundamentalGroup.IsTrivial",
        vec![u.clone()],
        is_trivial_type,
    ));

    // 13. Topology.FundamentalGroup.trivial_def
    let trivial_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let fg_x0 = Expr::apps(
            fundamental_group(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let is_trivial = Expr::apps(
            fg_is_trivial(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let one = Expr::apps(
            fg_one(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let forall_g_eq_one = {
            let mut bi = EnvDeclBuilder::child_of(&b);
            let (g_id, g) = bi.fresh_local(fg_x0.clone());
            let eq_g_one = Expr::apps(
                eq_const(Level::succ(u_level.clone())),
                [fg_x0.clone(), g, one],
            );
            bi.mk_pi(g_id, BinderInfo::Default, fg_x0, eq_g_one)
        };
        let result = Expr::app(Expr::app(iff_const(), is_trivial), forall_g_eq_one);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), result);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.FundamentalGroup.trivial_def",
        vec![u.clone()],
        trivial_def_type,
    ));

    // 14. Topology.simply_connected_iff_trivial_pi1
    let sc_iff_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let pc = Expr::app(
            Expr::app(topology_path_connected(u_level.clone()), alpha.clone()),
            inst.clone(),
        );
        let (pc_id, _pc) = b.fresh_local(pc.clone());
        let sc = Expr::app(
            Expr::app(topology_simply_connected(u_level.clone()), alpha.clone()),
            inst.clone(),
        );
        let forall_x0_trivial = {
            let mut bi = EnvDeclBuilder::child_of(&b);
            let (x0_id, x0) = bi.fresh_local(alpha.clone());
            let is_trivial = Expr::apps(
                fg_is_trivial(u_level.clone()),
                [alpha.clone(), inst.clone(), x0],
            );
            bi.mk_pi(x0_id, BinderInfo::Default, alpha.clone(), is_trivial)
        };
        let result = Expr::app(Expr::app(iff_const(), sc), forall_x0_trivial);
        let e = b.mk_pi(pc_id, BinderInfo::Default, pc, result);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.simply_connected_iff_trivial_pi1",
        vec![u.clone()],
        sc_iff_type,
    ));

    // 15. Topology.FundamentalGroup.basepoint_change
    let bp_change_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let pc = Expr::app(
            Expr::app(topology_path_connected(u_level.clone()), alpha.clone()),
            inst.clone(),
        );
        let (pc_id, _pc) = b.fresh_local(pc.clone());
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let (y0_id, y0) = b.fresh_local(alpha.clone());
        let fg_x0 = Expr::apps(
            fundamental_group(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        );
        let (a_id, _a) = b.fresh_local(fg_x0.clone());
        let fg_y0 = Expr::apps(
            fundamental_group(u_level.clone()),
            [alpha.clone(), inst.clone(), y0.clone()],
        );
        let e = fg_y0;
        let e = b.mk_pi(a_id, BinderInfo::Default, fg_x0, e);
        let e = b.mk_pi(y0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(x0_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(pc_id, BinderInfo::Default, pc, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.FundamentalGroup.basepoint_change",
        vec![u.clone()],
        bp_change_type,
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
