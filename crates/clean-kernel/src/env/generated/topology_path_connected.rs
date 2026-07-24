// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for `Topology.PathConnected` namespace (#1444).
//!
//! Migrated from handwritten `add_decl` calls in `topology_homotopy.rs`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.PathConnected";
pub(crate) const DECL_COUNT: usize = 17;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.UnitInterval",
    "Topology.UnitInterval.topologicalSpace",
    "Topology.UnitInterval.zero",
    "Topology.UnitInterval.one",
    "Topology.Path",
    "Topology.Path.toFun",
    "Topology.Path.continuous",
    "Topology.Path.source",
    "Topology.Path.target",
    "Topology.Path.refl",
    "Topology.Path.symm",
    "Topology.Path.trans",
    "Topology.PathConnected",
    "Topology.path_connected_def",
    "Topology.path_connected_implies_connected",
    "Topology.continuous_image_path_connected",
    "Topology.path_connected_of_path_components_eq",
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
    let v = Name::from_string("v");
    let u_level = Level::param(u.clone());
    let v_level = Level::param(v.clone());
    let type_u = Expr::sort(Level::succ(u_level.clone()));
    let type_v = Expr::sort(Level::succ(v_level.clone()));
    let prop = Expr::sort(Level::zero());
    let type_0 = Expr::sort(Level::succ(Level::zero())); // Type

    let topological_space =
        |lvl: Level| Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl]);
    let topology_continuous = |lvl1: Level, lvl2: Level| {
        Expr::const_(Name::from_string("Topology.Continuous"), vec![lvl1, lvl2])
    };
    let topology_connected =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Connected"), vec![lvl]);
    let eq_const = |lvl: Level| Expr::const_(Name::from_string("Eq"), vec![lvl]);
    let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
    let true_const = Expr::const_(Name::from_string("True"), vec![]);

    let unit_interval = Expr::const_(Name::from_string("Topology.UnitInterval"), vec![]);
    let unit_interval_topo = Expr::const_(
        Name::from_string("Topology.UnitInterval.topologicalSpace"),
        vec![],
    );
    let unit_zero = Expr::const_(Name::from_string("Topology.UnitInterval.zero"), vec![]);
    let unit_one = Expr::const_(Name::from_string("Topology.UnitInterval.one"), vec![]);
    let topology_path = |lvl: Level| Expr::const_(Name::from_string("Topology.Path"), vec![lvl]);
    let path_to_fun =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Path.toFun"), vec![lvl]);
    let path_connected =
        |lvl: Level| Expr::const_(Name::from_string("Topology.PathConnected"), vec![lvl]);

    let mk_path_app = |alpha: &Expr, inst: &Expr, x: &Expr, y: &Expr| {
        Expr::apps(
            topology_path(u_level.clone()),
            [alpha.clone(), inst.clone(), x.clone(), y.clone()],
        )
    };

    let mk_path_to_fun = |alpha: &Expr, inst: &Expr, x: &Expr, y: &Expr, p: &Expr| {
        Expr::apps(
            path_to_fun(u_level.clone()),
            [alpha.clone(), inst.clone(), x.clone(), y.clone(), p.clone()],
        )
    };

    let mut decls = Vec::with_capacity(DECL_COUNT);

    // ================================================================
    // 1. Topology.UnitInterval : Type
    // ================================================================
    decls.push(axiom("Topology.UnitInterval", vec![], type_0.clone()));

    // ================================================================
    // 2. Topology.UnitInterval.topologicalSpace : TopologicalSpace UnitInterval
    // ================================================================
    decls.push(axiom(
        "Topology.UnitInterval.topologicalSpace",
        vec![],
        Expr::app(topological_space(Level::zero()), unit_interval.clone()),
    ));

    // ================================================================
    // 3. Topology.UnitInterval.zero : UnitInterval
    // ================================================================
    decls.push(axiom(
        "Topology.UnitInterval.zero",
        vec![],
        unit_interval.clone(),
    ));

    // ================================================================
    // 4. Topology.UnitInterval.one : UnitInterval
    // ================================================================
    decls.push(axiom(
        "Topology.UnitInterval.one",
        vec![],
        unit_interval.clone(),
    ));

    // ================================================================
    // 5. Topology.Path : {α : Type u} → [TopologicalSpace α] → α → α → Type u
    // ================================================================
    let path_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, _inst) = b.fresh_local(ts_alpha_ty.clone());
        let (x_id, _x) = b.fresh_local(alpha.clone());
        let (y_id, _y) = b.fresh_local(alpha.clone());
        let e = type_u.clone();
        let e = b.mk_pi(y_id, BinderInfo::Default, alpha.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha_ty, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom("Topology.Path", vec![u.clone()], path_type));

    // ================================================================
    // 6. Topology.Path.toFun : {α : Type u} → [TopologicalSpace α] →
    //    {x y : α} → Path x y → (UnitInterval → α)
    // ================================================================
    let to_fun_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha_ty.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());
        let (p_id, _p) = b.fresh_local(mk_path_app(&alpha, &inst, &x, &y));
        let (t_id, _t) = b.fresh_local(unit_interval.clone());
        let e = alpha.clone();
        let e = b.mk_pi(t_id, BinderInfo::Default, unit_interval.clone(), e);
        let e = b.mk_pi(
            p_id,
            BinderInfo::Default,
            mk_path_app(&alpha, &inst, &x, &y),
            e,
        );
        let e = b.mk_pi(y_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha_ty, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom("Topology.Path.toFun", vec![u.clone()], to_fun_type));

    // ================================================================
    // 7. Topology.Path.continuous : {α : Type u} → [TopologicalSpace α] →
    //    {x y : α} → (p : Path x y) → Continuous (Path.toFun p)
    // ================================================================
    let path_continuous_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha_ty.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());
        let (p_id, p) = b.fresh_local(mk_path_app(&alpha, &inst, &x, &y));
        let to_fun_p = mk_path_to_fun(&alpha, &inst, &x, &y, &p);
        let result = Expr::apps(
            topology_continuous(Level::zero(), u_level.clone()),
            [
                unit_interval.clone(),
                alpha.clone(),
                unit_interval_topo.clone(),
                inst.clone(),
                to_fun_p,
            ],
        );
        let e = b.mk_pi(
            p_id,
            BinderInfo::Default,
            mk_path_app(&alpha, &inst, &x, &y),
            result,
        );
        let e = b.mk_pi(y_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha_ty, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.Path.continuous",
        vec![u.clone()],
        path_continuous_type,
    ));

    // ================================================================
    // 8. Topology.Path.source : {α : Type u} → [TopologicalSpace α] →
    //    {x y : α} → (p : Path x y) → Eq (Path.toFun p 0) x
    // ================================================================
    let path_source_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha_ty.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());
        let (p_id, p) = b.fresh_local(mk_path_app(&alpha, &inst, &x, &y));
        let to_fun_p_zero = Expr::app(mk_path_to_fun(&alpha, &inst, &x, &y, &p), unit_zero.clone());
        let result = Expr::apps(
            eq_const(Level::succ(u_level.clone())),
            [alpha.clone(), to_fun_p_zero, x.clone()],
        );
        let e = b.mk_pi(
            p_id,
            BinderInfo::Default,
            mk_path_app(&alpha, &inst, &x, &y),
            result,
        );
        let e = b.mk_pi(y_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha_ty, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.Path.source",
        vec![u.clone()],
        path_source_type,
    ));

    // ================================================================
    // 9. Topology.Path.target : {α : Type u} → [TopologicalSpace α] →
    //    {x y : α} → (p : Path x y) → Eq (Path.toFun p 1) y
    // ================================================================
    let path_target_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha_ty.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());
        let (p_id, p) = b.fresh_local(mk_path_app(&alpha, &inst, &x, &y));
        let to_fun_p_one = Expr::app(mk_path_to_fun(&alpha, &inst, &x, &y, &p), unit_one.clone());
        let result = Expr::apps(
            eq_const(Level::succ(u_level.clone())),
            [alpha.clone(), to_fun_p_one, y.clone()],
        );
        let e = b.mk_pi(
            p_id,
            BinderInfo::Default,
            mk_path_app(&alpha, &inst, &x, &y),
            result,
        );
        let e = b.mk_pi(y_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha_ty, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.Path.target",
        vec![u.clone()],
        path_target_type,
    ));

    // ================================================================
    // 10. Topology.Path.refl : {α : Type u} → [TopologicalSpace α] →
    //     (x : α) → Path x x
    // ================================================================
    let path_refl_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha_ty.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let result = mk_path_app(&alpha, &inst, &x, &x);
        let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), result);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha_ty, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom("Topology.Path.refl", vec![u.clone()], path_refl_type));

    // ================================================================
    // 11. Topology.Path.symm : {α : Type u} → [TopologicalSpace α] →
    //     {x y : α} → Path x y → Path y x
    // ================================================================
    let path_symm_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha_ty.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());
        let (p_id, _p) = b.fresh_local(mk_path_app(&alpha, &inst, &x, &y));
        let result = mk_path_app(&alpha, &inst, &y, &x);
        let e = b.mk_pi(
            p_id,
            BinderInfo::Default,
            mk_path_app(&alpha, &inst, &x, &y),
            result,
        );
        let e = b.mk_pi(y_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha_ty, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom("Topology.Path.symm", vec![u.clone()], path_symm_type));

    // ================================================================
    // 12. Topology.Path.trans : {α : Type u} → [TopologicalSpace α] →
    //     {x y z : α} → Path x y → Path y z → Path x z
    // ================================================================
    let path_trans_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha_ty.clone());
        let (x_id, x) = b.fresh_local(alpha.clone());
        let (y_id, y) = b.fresh_local(alpha.clone());
        let (z_id, z) = b.fresh_local(alpha.clone());
        let (p_id, _p) = b.fresh_local(mk_path_app(&alpha, &inst, &x, &y));
        let (q_id, _q) = b.fresh_local(mk_path_app(&alpha, &inst, &y, &z));
        let result = mk_path_app(&alpha, &inst, &x, &z);
        let e = b.mk_pi(
            q_id,
            BinderInfo::Default,
            mk_path_app(&alpha, &inst, &y, &z),
            result,
        );
        let e = b.mk_pi(
            p_id,
            BinderInfo::Default,
            mk_path_app(&alpha, &inst, &x, &y),
            e,
        );
        let e = b.mk_pi(z_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha_ty, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.Path.trans",
        vec![u.clone()],
        path_trans_type,
    ));

    // ================================================================
    // 13. Topology.PathConnected : {α : Type u} → [TopologicalSpace α] → Prop
    // ================================================================
    let path_connected_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, _inst) = b.fresh_local(ts_alpha_ty.clone());
        let e = prop.clone();
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha_ty, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.PathConnected",
        vec![u.clone()],
        path_connected_type,
    ));

    // ================================================================
    // 14. Topology.path_connected_def : {α : Type u} → [TopologicalSpace α] →
    //     Iff PathConnected (∀ x y : α, ∃ (p : Path x y), True)
    // ================================================================
    let path_connected_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha_ty.clone());

        let pc_applied = Expr::app(
            Expr::app(path_connected(u_level.clone()), alpha.clone()),
            inst.clone(),
        );

        // Inner: ∀ x : α, ∀ y : α, ∃ (p : Path x y), True
        let forall_inner = {
            let mut bi = EnvDeclBuilder::child_of(&b);
            let (x_id, x_inner) = bi.fresh_local(alpha.clone());
            let (y_id, y_inner) = bi.fresh_local(alpha.clone());
            let path_xy_inner = mk_path_app(&alpha, &inst, &x_inner, &y_inner);
            let exists_path = Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Exists"),
                        vec![Level::succ(u_level.clone())],
                    ),
                    path_xy_inner.clone(),
                ),
                {
                    let mut bl = EnvDeclBuilder::child_of(&bi);
                    let (p_id, _p) = bl.fresh_local(path_xy_inner.clone());
                    bl.mk_lam(
                        p_id,
                        BinderInfo::Default,
                        path_xy_inner.clone(),
                        true_const.clone(),
                    )
                },
            );
            let e = bi.mk_pi(y_id, BinderInfo::Default, alpha.clone(), exists_path);
            bi.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e)
        };

        let result = Expr::app(Expr::app(iff_const.clone(), pc_applied), forall_inner);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha_ty, result);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.path_connected_def",
        vec![u.clone()],
        path_connected_def_type,
    ));

    // ================================================================
    // 15. Topology.path_connected_implies_connected : {α : Type u} →
    //     [TopologicalSpace α] → PathConnected → Connected
    // ================================================================
    let path_implies_connected_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha_ty.clone());
        let pc_ty = Expr::app(
            Expr::app(path_connected(u_level.clone()), alpha.clone()),
            inst.clone(),
        );
        let (pc_id, _pc) = b.fresh_local(pc_ty.clone());
        let result = Expr::app(
            Expr::app(topology_connected(u_level.clone()), alpha.clone()),
            inst.clone(),
        );
        let e = b.mk_pi(pc_id, BinderInfo::Default, pc_ty, result);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha_ty, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.path_connected_implies_connected",
        vec![u.clone()],
        path_implies_connected_type,
    ));

    // ================================================================
    // 16. Topology.continuous_image_path_connected : {α : Type u} → {β : Type v} →
    //     [TopologicalSpace α] → [TopologicalSpace β] →
    //     (f : α → β) → Continuous f → PathConnected α → PathConnected β
    // ================================================================
    let continuous_image_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let ts_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_a_id, inst_a) = b.fresh_local(ts_alpha_ty.clone());
        let ts_beta_ty = Expr::app(topological_space(v_level.clone()), beta.clone());
        let (inst_b_id, inst_b) = b.fresh_local(ts_beta_ty.clone());
        let f_type = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, f) = b.fresh_local(f_type.clone());
        let continuous_f = Expr::apps(
            topology_continuous(u_level.clone(), v_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                f.clone(),
            ],
        );
        let (hf_id, _hf) = b.fresh_local(continuous_f.clone());
        let pc_alpha = Expr::app(
            Expr::app(path_connected(u_level.clone()), alpha.clone()),
            inst_a.clone(),
        );
        let (hpc_id, _hpc) = b.fresh_local(pc_alpha.clone());
        let result = Expr::app(
            Expr::app(path_connected(v_level.clone()), beta.clone()),
            inst_b.clone(),
        );
        let e = b.mk_pi(hpc_id, BinderInfo::Default, pc_alpha, result);
        let e = b.mk_pi(hf_id, BinderInfo::Default, continuous_f, e);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_type, e);
        let e = b.mk_pi(inst_b_id, BinderInfo::InstImplicit, ts_beta_ty, e);
        let e = b.mk_pi(inst_a_id, BinderInfo::InstImplicit, ts_alpha_ty, e);
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.continuous_image_path_connected",
        vec![u.clone(), v.clone()],
        continuous_image_type,
    ));

    // ================================================================
    // 17. Topology.path_connected_of_path_components_eq : {α : Type u} →
    //     [TopologicalSpace α] → (∀ x y : α, ∃ (p : Path x y), True) → PathConnected
    // ================================================================
    let path_of_components_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let ts_alpha_ty = Expr::app(topological_space(u_level.clone()), alpha.clone());
        let (inst_id, inst) = b.fresh_local(ts_alpha_ty.clone());

        let forall_x_y_hyp = {
            let mut bi = EnvDeclBuilder::child_of(&b);
            let (x_id, x_inner) = bi.fresh_local(alpha.clone());
            let (y_id, y_inner) = bi.fresh_local(alpha.clone());
            let path_xy_inner = mk_path_app(&alpha, &inst, &x_inner, &y_inner);
            let exists_path = Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Exists"),
                        vec![Level::succ(u_level.clone())],
                    ),
                    path_xy_inner.clone(),
                ),
                {
                    let mut bl = EnvDeclBuilder::child_of(&bi);
                    let (p_id, _p) = bl.fresh_local(path_xy_inner.clone());
                    bl.mk_lam(
                        p_id,
                        BinderInfo::Default,
                        path_xy_inner.clone(),
                        true_const.clone(),
                    )
                },
            );
            let e = bi.mk_pi(y_id, BinderInfo::Default, alpha.clone(), exists_path);
            bi.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e)
        };

        let (h_id, _h) = b.fresh_local(forall_x_y_hyp.clone());
        let result = Expr::app(
            Expr::app(path_connected(u_level.clone()), alpha.clone()),
            inst.clone(),
        );
        let e = b.mk_pi(h_id, BinderInfo::Default, forall_x_y_hyp, result);
        let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha_ty, e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.path_connected_of_path_components_eq",
        vec![u.clone()],
        path_of_components_type,
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
