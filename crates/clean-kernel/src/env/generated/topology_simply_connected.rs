// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for `Topology.SimplyConnected` namespace (#1444).
//!
//! Migrated from handwritten `add_decl` calls in `topology_homotopy.rs`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.SimplyConnected";
pub(crate) const DECL_COUNT: usize = 17;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.Loop",
    "Topology.Loop.toPath",
    "Topology.Loop.refl",
    "Topology.Loop.symm",
    "Topology.Loop.trans",
    "Topology.Homotopy",
    "Topology.Homotopy.refl",
    "Topology.Homotopy.symm",
    "Topology.Homotopy.trans",
    "Topology.LoopHomotopy",
    "Topology.NullHomotopic",
    "Topology.null_homotopic_def",
    "Topology.SimplyConnected",
    "Topology.simply_connected_def",
    "Topology.simply_connected_implies_path_connected",
    "Topology.simply_connected_implies_connected",
    "Topology.null_homotopic_refl",
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
    let topology_path = |lvl: Level| Expr::const_(Name::from_string("Topology.Path"), vec![lvl]);
    let topology_path_connected =
        |lvl: Level| Expr::const_(Name::from_string("Topology.PathConnected"), vec![lvl]);
    let topology_connected =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Connected"), vec![lvl]);
    let topology_loop = |lvl: Level| Expr::const_(Name::from_string("Topology.Loop"), vec![lvl]);
    let loop_refl_const =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Loop.refl"), vec![lvl]);
    let topology_homotopy =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Homotopy"), vec![lvl]);
    let loop_homotopy =
        |lvl: Level| Expr::const_(Name::from_string("Topology.LoopHomotopy"), vec![lvl]);
    let null_homotopic =
        |lvl: Level| Expr::const_(Name::from_string("Topology.NullHomotopic"), vec![lvl]);
    let simply_connected =
        |lvl: Level| Expr::const_(Name::from_string("Topology.SimplyConnected"), vec![lvl]);
    let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    let true_const = Expr::const_(Name::from_string("True"), vec![]);

    let mk_loop_app = |alpha: &Expr, inst: &Expr, x: &Expr| {
        Expr::apps(
            topology_loop(u_level.clone()),
            [alpha.clone(), inst.clone(), x.clone()],
        )
    };

    let mk_path_app = |alpha: &Expr, inst: &Expr, x: &Expr, y: &Expr| {
        Expr::apps(
            topology_path(u_level.clone()),
            [alpha.clone(), inst.clone(), x.clone(), y.clone()],
        )
    };

    let mk_hom_app = |alpha: &Expr, inst: &Expr, x: &Expr, y: &Expr, p: &Expr, q: &Expr| {
        Expr::apps(
            topology_homotopy(u_level.clone()),
            [
                alpha.clone(),
                inst.clone(),
                x.clone(),
                y.clone(),
                p.clone(),
                q.clone(),
            ],
        )
    };

    let mk_loop_hom_app = |alpha: &Expr, inst: &Expr, x: &Expr, gamma: &Expr, delta: &Expr| {
        Expr::apps(
            loop_homotopy(u_level.clone()),
            [
                alpha.clone(),
                inst.clone(),
                x.clone(),
                gamma.clone(),
                delta.clone(),
            ],
        )
    };

    let mk_null_hom_app = |alpha: &Expr, inst: &Expr, x: &Expr, gamma: &Expr| {
        Expr::apps(
            null_homotopic(u_level.clone()),
            [alpha.clone(), inst.clone(), x.clone(), gamma.clone()],
        )
    };

    let mk_loop_refl_app = |alpha: &Expr, inst: &Expr, x: &Expr| {
        Expr::apps(
            loop_refl_const(u_level.clone()),
            [alpha.clone(), inst.clone(), x.clone()],
        )
    };

    let mut decls = Vec::with_capacity(DECL_COUNT);

    // 1. Topology.Loop : {α : Type u} → [TopologicalSpace α] → α → Type u
    let loop_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, _inst) = b.fresh_local(ts_alpha.clone());
        let (x_id, _x) = b.fresh_local(alpha.clone());
        let e = type_u.clone();
        let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom("Topology.Loop", vec![u.clone()], loop_type));

    // 2. Topology.Loop.toPath : {α : Type u} → [TopologicalSpace α] →
    //    {x : α} → Loop x → Path x x
    let loop_to_path_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (gamma_id, _gamma) = b.fresh_local(mk_loop_app(&alpha, &inst, &x));
        let e = mk_path_app(&alpha, &inst, &x, &x);
        let e = b.mk_pi(
            gamma_id,
            BinderInfo::Default,
            mk_loop_app(&alpha, &inst, &x),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.Loop.toPath",
        vec![u.clone()],
        loop_to_path_type,
    ));

    // 3. Topology.Loop.refl : {α : Type u} → [TopologicalSpace α] → (x : α) → Loop x
    let loop_refl_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let e = mk_loop_app(&alpha, &inst, &x);
        let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom("Topology.Loop.refl", vec![u.clone()], loop_refl_type));

    // 4. Topology.Loop.symm : {α : Type u} → [TopologicalSpace α] →
    //    {x : α} → Loop x → Loop x
    let loop_symm_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (gamma_id, _gamma) = b.fresh_local(mk_loop_app(&alpha, &inst, &x));
        let e = mk_loop_app(&alpha, &inst, &x);
        let e = b.mk_pi(
            gamma_id,
            BinderInfo::Default,
            mk_loop_app(&alpha, &inst, &x),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom("Topology.Loop.symm", vec![u.clone()], loop_symm_type));

    // 5. Topology.Loop.trans : {α : Type u} → [TopologicalSpace α] →
    //    {x : α} → Loop x → Loop x → Loop x
    let loop_trans_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let loop_x = mk_loop_app(&alpha, &inst, &x);
        let (gamma_id, _gamma) = b.fresh_local(loop_x.clone());
        let (delta_id, _delta) = b.fresh_local(loop_x.clone());
        let e = loop_x.clone();
        let e = b.mk_pi(delta_id, BinderInfo::Default, loop_x.clone(), e);
        let e = b.mk_pi(gamma_id, BinderInfo::Default, loop_x, e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.Loop.trans",
        vec![u.clone()],
        loop_trans_type,
    ));

    // 6. Topology.Homotopy : {α : Type u} → [TopologicalSpace α] →
    //    {x y : α} → Path x y → Path x y → Type u
    let homotopy_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());
        let path_xy = mk_path_app(&alpha, &inst, &x, &y);
        let (p_id, _p) = b.fresh_local(path_xy.clone());
        let (q_id, _q) = b.fresh_local(path_xy.clone());
        let e = type_u.clone();
        let e = b.mk_pi(q_id, BinderInfo::Default, path_xy.clone(), e);
        let e = b.mk_pi(p_id, BinderInfo::Default, path_xy, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom("Topology.Homotopy", vec![u.clone()], homotopy_type));

    // 7. Topology.Homotopy.refl : {α : Type u} → [TopologicalSpace α] →
    //    {x y : α} → (p : Path x y) → Homotopy p p
    let homotopy_refl_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());
        let path_xy = mk_path_app(&alpha, &inst, &x, &y);
        let (p_id, p) = b.fresh_local(path_xy.clone());
        let e = mk_hom_app(&alpha, &inst, &x, &y, &p, &p);
        let e = b.mk_pi(p_id, BinderInfo::Default, path_xy, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.Homotopy.refl",
        vec![u.clone()],
        homotopy_refl_type,
    ));

    // 8. Topology.Homotopy.symm : {α : Type u} → [TopologicalSpace α] →
    //    {x y : α} → {p q : Path x y} → Homotopy p q → Homotopy q p
    let homotopy_symm_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());
        let path_xy = mk_path_app(&alpha, &inst, &x, &y);
        let (p_id, p) = b.fresh_local(path_xy.clone());
        let (q_id, q) = b.fresh_local(path_xy.clone());
        let (h_id, _h) = b.fresh_local(mk_hom_app(&alpha, &inst, &x, &y, &p, &q));
        let e = mk_hom_app(&alpha, &inst, &x, &y, &q, &p);
        let e = b.mk_pi(
            h_id,
            BinderInfo::Default,
            mk_hom_app(&alpha, &inst, &x, &y, &p, &q),
            e,
        );
        let e = b.mk_pi(q_id, BinderInfo::Implicit, path_xy.clone(), e);
        let e = b.mk_pi(p_id, BinderInfo::Implicit, path_xy, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.Homotopy.symm",
        vec![u.clone()],
        homotopy_symm_type,
    ));

    // 9. Topology.Homotopy.trans : {α : Type u} → [TopologicalSpace α] →
    //    {x y : α} → {p q r : Path x y} → Homotopy p q → Homotopy q r → Homotopy p r
    let homotopy_trans_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());
        let path_xy = mk_path_app(&alpha, &inst, &x, &y);
        let (p_id, p) = b.fresh_local(path_xy.clone());
        let (q_id, q) = b.fresh_local(path_xy.clone());
        let (r_id, r) = b.fresh_local(path_xy.clone());
        let (h1_id, _h1) = b.fresh_local(mk_hom_app(&alpha, &inst, &x, &y, &p, &q));
        let (h2_id, _h2) = b.fresh_local(mk_hom_app(&alpha, &inst, &x, &y, &q, &r));
        let e = mk_hom_app(&alpha, &inst, &x, &y, &p, &r);
        let e = b.mk_pi(
            h2_id,
            BinderInfo::Default,
            mk_hom_app(&alpha, &inst, &x, &y, &q, &r),
            e,
        );
        let e = b.mk_pi(
            h1_id,
            BinderInfo::Default,
            mk_hom_app(&alpha, &inst, &x, &y, &p, &q),
            e,
        );
        let e = b.mk_pi(r_id, BinderInfo::Implicit, path_xy.clone(), e);
        let e = b.mk_pi(q_id, BinderInfo::Implicit, path_xy.clone(), e);
        let e = b.mk_pi(p_id, BinderInfo::Implicit, path_xy, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.Homotopy.trans",
        vec![u.clone()],
        homotopy_trans_type,
    ));

    // 10. Topology.LoopHomotopy : {α : Type u} → [TopologicalSpace α] →
    //     {x : α} → Loop x → Loop x → Type u
    let loop_homotopy_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let loop_x = mk_loop_app(&alpha, &inst, &x);
        let (gamma_id, _gamma) = b.fresh_local(loop_x.clone());
        let (delta_id, _delta) = b.fresh_local(loop_x.clone());
        let e = type_u.clone();
        let e = b.mk_pi(delta_id, BinderInfo::Default, loop_x.clone(), e);
        let e = b.mk_pi(gamma_id, BinderInfo::Default, loop_x, e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.LoopHomotopy",
        vec![u.clone()],
        loop_homotopy_type,
    ));

    // 11. Topology.NullHomotopic : {α : Type u} → [TopologicalSpace α] →
    //     {x : α} → Loop x → Prop
    let null_homotopic_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (gamma_id, _gamma) = b.fresh_local(mk_loop_app(&alpha, &inst, &x));
        let e = prop.clone();
        let e = b.mk_pi(
            gamma_id,
            BinderInfo::Default,
            mk_loop_app(&alpha, &inst, &x),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.NullHomotopic",
        vec![u.clone()],
        null_homotopic_type,
    ));

    // 12. Topology.null_homotopic_def : {α : Type u} → [TopologicalSpace α] →
    //     {x : α} → (γ : Loop x) → Iff (NullHomotopic γ) (∃ h : LoopHomotopy γ (Loop.refl x), True)
    let null_homotopic_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let loop_x = mk_loop_app(&alpha, &inst, &x);
        let (gamma_id, gamma) = b.fresh_local(loop_x.clone());

        let null_hom_gamma = mk_null_hom_app(&alpha, &inst, &x, &gamma);
        let loop_refl_x = mk_loop_refl_app(&alpha, &inst, &x);
        let loop_hom_gamma_refl = mk_loop_hom_app(&alpha, &inst, &x, &gamma, &loop_refl_x);

        // ∃ h : LoopHomotopy γ (Loop.refl x), True
        let exists_hom = Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Exists"),
                    vec![Level::succ(u_level.clone())],
                ),
                loop_hom_gamma_refl.clone(),
            ),
            Expr::lam(BinderInfo::Default, loop_hom_gamma_refl, true_const.clone()),
        );

        let e = Expr::app(Expr::app(iff_const.clone(), null_hom_gamma), exists_hom);
        let e = b.mk_pi(gamma_id, BinderInfo::Default, loop_x, e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.null_homotopic_def",
        vec![u.clone()],
        null_homotopic_def_type,
    ));

    // 13. Topology.SimplyConnected : {α : Type u} → [TopologicalSpace α] → Prop
    let simply_connected_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, _inst) = b.fresh_local(ts_alpha.clone());
        let e = prop.clone();
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.SimplyConnected",
        vec![u.clone()],
        simply_connected_type,
    ));

    // 14. Topology.simply_connected_def : {α : Type u} → [TopologicalSpace α] →
    //     Iff SimplyConnected (PathConnected ∧ ∀ x (γ : Loop x), NullHomotopic γ)
    let simply_connected_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());

        let sc_inst = Expr::apps(
            simply_connected(u_level.clone()),
            [alpha.clone(), inst.clone()],
        );
        let pc_inst = Expr::apps(
            topology_path_connected(u_level.clone()),
            [alpha.clone(), inst.clone()],
        );

        // ∀ x : α, ∀ (γ : Loop x), NullHomotopic γ
        let forall_x_gamma = {
            let mut inner = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = inner.fresh_local(alpha.clone());
            let loop_x = mk_loop_app(&alpha, &inst, &x);
            let (gamma_id, gamma) = inner.fresh_local(loop_x.clone());
            let null_hom = mk_null_hom_app(&alpha, &inst, &x, &gamma);
            let e = inner.mk_pi(gamma_id, BinderInfo::Default, loop_x, null_hom);
            let e = inner.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
            inner.finish_child(e)
        };

        let pc_and_all_null = Expr::app(Expr::app(and_const.clone(), pc_inst), forall_x_gamma);
        let e = Expr::app(Expr::app(iff_const.clone(), sc_inst), pc_and_all_null);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.simply_connected_def",
        vec![u.clone()],
        simply_connected_def_type,
    ));

    // 15. Topology.simply_connected_implies_path_connected :
    //     {α : Type u} → [TopologicalSpace α] → SimplyConnected → PathConnected
    let sc_implies_pc_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
        let sc = Expr::apps(
            simply_connected(u_level.clone()),
            [alpha.clone(), inst.clone()],
        );
        let pc = Expr::apps(
            topology_path_connected(u_level.clone()),
            [alpha.clone(), inst.clone()],
        );
        let (sc_id, _sc_proof) = b.fresh_local(sc.clone());
        let e = pc;
        let e = b.mk_pi(sc_id, BinderInfo::Default, sc, e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.simply_connected_implies_path_connected",
        vec![u.clone()],
        sc_implies_pc_type,
    ));

    // 16. Topology.simply_connected_implies_connected :
    //     {α : Type u} → [TopologicalSpace α] → SimplyConnected → Connected
    let sc_implies_c_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
        let sc = Expr::apps(
            simply_connected(u_level.clone()),
            [alpha.clone(), inst.clone()],
        );
        let conn = Expr::apps(
            topology_connected(u_level.clone()),
            [alpha.clone(), inst.clone()],
        );
        let (sc_id, _sc_proof) = b.fresh_local(sc.clone());
        let e = conn;
        let e = b.mk_pi(sc_id, BinderInfo::Default, sc, e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.simply_connected_implies_connected",
        vec![u.clone()],
        sc_implies_c_type,
    ));

    // 17. Topology.null_homotopic_refl : {α : Type u} → [TopologicalSpace α] →
    //     (x : α) → NullHomotopic (Loop.refl x)
    let null_hom_refl_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let loop_refl_x = mk_loop_refl_app(&alpha, &inst, &x);
        let e = mk_null_hom_app(&alpha, &inst, &x, &loop_refl_x);
        let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.null_homotopic_refl",
        vec![u.clone()],
        null_hom_refl_type,
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
