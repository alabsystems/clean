// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for `Topology.Contractible` namespace (#1444).
//!
//! Migrated from handwritten `add_decl` calls in `topology_homotopy.rs`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.Contractible";
pub(crate) const DECL_COUNT: usize = 12;

#[cfg(test)]
#[allow(dead_code)] // 2026-07-31: no caller in any build (lib or lib-test); kept, not deleted.
pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.Contraction",
    "Topology.Contraction.homotopy",
    "Topology.Contraction.at_zero",
    "Topology.Contraction.at_one",
    "Topology.Contraction.continuous_slice",
    "Topology.Contractible",
    "Topology.contractible_def",
    "Topology.contractible_implies_simply_connected",
    "Topology.contractible_implies_path_connected",
    "Topology.contractible_implies_connected",
    "Topology.contractible_point",
    "Topology.Contraction.mk",
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
    let topology_unit_interval =
        || Expr::const_(Name::from_string("Topology.UnitInterval"), vec![]);
    let topology_unit_interval_zero =
        || Expr::const_(Name::from_string("Topology.UnitInterval.zero"), vec![]);
    let topology_unit_interval_one =
        || Expr::const_(Name::from_string("Topology.UnitInterval.one"), vec![]);
    let topology_continuous = |lvl1: Level, lvl2: Level| {
        Expr::const_(Name::from_string("Topology.Continuous"), vec![lvl1, lvl2])
    };
    let topology_simply_connected =
        |lvl: Level| Expr::const_(Name::from_string("Topology.SimplyConnected"), vec![lvl]);
    let topology_path_connected =
        |lvl: Level| Expr::const_(Name::from_string("Topology.PathConnected"), vec![lvl]);
    let topology_connected =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Connected"), vec![lvl]);
    let iff_const = || Expr::const_(Name::from_string("Iff"), vec![]);
    let exists_const = |lvl: Level| Expr::const_(Name::from_string("Exists"), vec![lvl]);
    let nonempty_const = |lvl: Level| Expr::const_(Name::from_string("Nonempty"), vec![lvl]);

    let contraction =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Contraction"), vec![lvl]);
    let contraction_homotopy = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.Contraction.homotopy"),
            vec![lvl],
        )
    };
    let contractible =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Contractible"), vec![lvl]);

    let mk_contraction_app = |alpha: &Expr, inst: &Expr, x0: &Expr| {
        Expr::apps(
            contraction(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone()],
        )
    };
    let mk_homotopy_app = |alpha: &Expr, inst: &Expr, x0: &Expr, c: &Expr| {
        Expr::apps(
            contraction_homotopy(u_level.clone()),
            [alpha.clone(), inst.clone(), x0.clone(), c.clone()],
        )
    };
    let mk_contractible_app = |alpha: &Expr, inst: &Expr| {
        Expr::app(
            Expr::app(contractible(u_level.clone()), alpha.clone()),
            inst.clone(),
        )
    };

    let mut decls = Vec::with_capacity(DECL_COUNT);

    // ================================================================
    // Topology.Contraction : {α : Type u} → [TopologicalSpace α] → α → Type u
    // ================================================================
    let contraction_type = {
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
        "Topology.Contraction",
        vec![u.clone()],
        contraction_type,
    ));

    // ================================================================
    // Topology.Contraction.homotopy : {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
    //   Contraction x₀ → (UnitInterval → α → α)
    // ================================================================
    let homotopy_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, _inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let (c_id, _c) = b.fresh_local(mk_contraction_app(&alpha, &_inst, &x0));
        let (t_id, _t) = b.fresh_local(topology_unit_interval());
        let (x_id, _x) = b.fresh_local(alpha.clone());
        let e = alpha.clone();
        let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
        let e = b.mk_pi(t_id, BinderInfo::Default, topology_unit_interval(), e);
        let e = b.mk_pi(
            c_id,
            BinderInfo::Default,
            mk_contraction_app(&alpha, &_inst, &x0),
            e,
        );
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
        "Topology.Contraction.homotopy",
        vec![u.clone()],
        homotopy_type,
    ));

    // ================================================================
    // Topology.Contraction.at_zero : {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
    //   (c : Contraction x₀) → ∀ x, Eq (Contraction.homotopy c 0 x) x
    // ================================================================
    let at_zero_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let (c_id, c) = b.fresh_local(mk_contraction_app(&alpha, &inst, &x0));
        let (x_id, x) = b.fresh_local(alpha.clone());
        let hom_c_0_x = Expr::app(
            Expr::app(
                mk_homotopy_app(&alpha, &inst, &x0, &c),
                topology_unit_interval_zero(),
            ),
            x.clone(),
        );
        let eq_body = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]),
            [alpha.clone(), hom_c_0_x, x.clone()],
        );
        let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), eq_body);
        let e = b.mk_pi(
            c_id,
            BinderInfo::Default,
            mk_contraction_app(&alpha, &inst, &x0),
            e,
        );
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
        "Topology.Contraction.at_zero",
        vec![u.clone()],
        at_zero_type,
    ));

    // ================================================================
    // Topology.Contraction.at_one : {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
    //   (c : Contraction x₀) → ∀ x, Eq (Contraction.homotopy c 1 x) x₀
    // ================================================================
    let at_one_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let (c_id, c) = b.fresh_local(mk_contraction_app(&alpha, &inst, &x0));
        let (x_id, x) = b.fresh_local(alpha.clone());
        let hom_c_1_x = Expr::app(
            Expr::app(
                mk_homotopy_app(&alpha, &inst, &x0, &c),
                topology_unit_interval_one(),
            ),
            x.clone(),
        );
        let eq_body = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]),
            [alpha.clone(), hom_c_1_x, x0.clone()],
        );
        let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), eq_body);
        let e = b.mk_pi(
            c_id,
            BinderInfo::Default,
            mk_contraction_app(&alpha, &inst, &x0),
            e,
        );
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
        "Topology.Contraction.at_one",
        vec![u.clone()],
        at_one_type,
    ));

    // ================================================================
    // Topology.Contraction.continuous_slice : {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
    //   (c : Contraction x₀) → ∀ t : UnitInterval, Continuous (fun x => Contraction.homotopy c t x)
    // ================================================================
    let continuous_slice_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());
        let (c_id, c) = b.fresh_local(mk_contraction_app(&alpha, &inst, &x0));
        let (t_id, t) = b.fresh_local(topology_unit_interval());
        let slice_fun = {
            let mut lb = EnvDeclBuilder::child_of(&b);
            let (lx_id, lx) = lb.fresh_local(alpha.clone());
            let hom_c_t_x = Expr::app(
                Expr::app(mk_homotopy_app(&alpha, &inst, &x0, &c), t.clone()),
                lx.clone(),
            );
            lb.mk_lam(lx_id, BinderInfo::Default, alpha.clone(), hom_c_t_x)
        };
        let continuous_app = Expr::apps(
            topology_continuous(u_level.clone(), u_level.clone()),
            [
                alpha.clone(),
                alpha.clone(),
                inst.clone(),
                inst.clone(),
                slice_fun,
            ],
        );
        let e = b.mk_pi(
            t_id,
            BinderInfo::Default,
            topology_unit_interval(),
            continuous_app,
        );
        let e = b.mk_pi(
            c_id,
            BinderInfo::Default,
            mk_contraction_app(&alpha, &inst, &x0),
            e,
        );
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
        "Topology.Contraction.continuous_slice",
        vec![u.clone()],
        continuous_slice_type,
    ));

    // ================================================================
    // Topology.Contractible : {α : Type u} → [TopologicalSpace α] → Prop
    // ================================================================
    let contractible_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, _inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let e = prop.clone();
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
        "Topology.Contractible",
        vec![u.clone()],
        contractible_type,
    ));

    // ================================================================
    // Topology.contractible_def : {α : Type u} → [TopologicalSpace α] →
    //   Iff Contractible (∃ x₀ : α, Nonempty (Contraction x₀))
    // ================================================================
    let contractible_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let lhs = mk_contractible_app(&alpha, &inst);
        let pred_lambda = {
            let mut lb = EnvDeclBuilder::child_of(&b);
            let (lx0_id, lx0) = lb.fresh_local(alpha.clone());
            let body = Expr::app(
                nonempty_const(Level::succ(u_level.clone())),
                mk_contraction_app(&alpha, &inst, &lx0),
            );
            lb.mk_lam(lx0_id, BinderInfo::Default, alpha.clone(), body)
        };
        let rhs = Expr::app(
            Expr::app(exists_const(Level::succ(u_level.clone())), alpha.clone()),
            pred_lambda,
        );
        let iff_body = Expr::app(Expr::app(iff_const(), lhs), rhs);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            iff_body,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.contractible_def",
        vec![u.clone()],
        contractible_def_type,
    ));

    // ================================================================
    // Topology.contractible_implies_simply_connected :
    //   {α : Type u} → [TopologicalSpace α] → Contractible → SimplyConnected
    // ================================================================
    let contr_implies_sc_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (h_id, _h) = b.fresh_local(mk_contractible_app(&alpha, &inst));
        let e = Expr::app(
            Expr::app(topology_simply_connected(u_level.clone()), alpha.clone()),
            inst.clone(),
        );
        let e = b.mk_pi(
            h_id,
            BinderInfo::Default,
            mk_contractible_app(&alpha, &inst),
            e,
        );
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
        "Topology.contractible_implies_simply_connected",
        vec![u.clone()],
        contr_implies_sc_type,
    ));

    // ================================================================
    // Topology.contractible_implies_path_connected :
    //   {α : Type u} → [TopologicalSpace α] → Contractible → PathConnected
    // ================================================================
    let contr_implies_pc_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (h_id, _h) = b.fresh_local(mk_contractible_app(&alpha, &inst));
        let e = Expr::app(
            Expr::app(topology_path_connected(u_level.clone()), alpha.clone()),
            inst.clone(),
        );
        let e = b.mk_pi(
            h_id,
            BinderInfo::Default,
            mk_contractible_app(&alpha, &inst),
            e,
        );
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
        "Topology.contractible_implies_path_connected",
        vec![u.clone()],
        contr_implies_pc_type,
    ));

    // ================================================================
    // Topology.contractible_implies_connected :
    //   {α : Type u} → [TopologicalSpace α] → Contractible → Connected
    // ================================================================
    let contr_implies_conn_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (h_id, _h) = b.fresh_local(mk_contractible_app(&alpha, &inst));
        let e = Expr::app(
            Expr::app(topology_connected(u_level.clone()), alpha.clone()),
            inst.clone(),
        );
        let e = b.mk_pi(
            h_id,
            BinderInfo::Default,
            mk_contractible_app(&alpha, &inst),
            e,
        );
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
        "Topology.contractible_implies_connected",
        vec![u.clone()],
        contr_implies_conn_type,
    ));

    // ================================================================
    // Topology.contractible_point : {α : Type u} → [TopologicalSpace α] →
    //   Contractible → (x : α) → Contraction x
    // ================================================================
    let contr_point_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (h_id, _h) = b.fresh_local(mk_contractible_app(&alpha, &inst));
        let (x_id, x) = b.fresh_local(alpha.clone());
        let e = mk_contraction_app(&alpha, &inst, &x);
        let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
        let e = b.mk_pi(
            h_id,
            BinderInfo::Default,
            mk_contractible_app(&alpha, &inst),
            e,
        );
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
        "Topology.contractible_point",
        vec![u.clone()],
        contr_point_type,
    ));

    // ================================================================
    // Topology.Contraction.mk : {α : Type u} → [TopologicalSpace α] → (x₀ : α) →
    //   (H : UnitInterval → α → α) →
    //   (at_zero : ∀ x, Eq (H 0 x) x) →
    //   (at_one : ∀ x, Eq (H 1 x) x₀) →
    //   (cont : ∀ t, Continuous (fun x => H t x)) →
    //   Contraction x₀
    // ================================================================
    let mk_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (x0_id, x0) = b.fresh_local(alpha.clone());

        // H : UnitInterval → α → α
        let h_type = {
            let mut hb = EnvDeclBuilder::child_of(&b);
            let (ht_id, _ht) = hb.fresh_local(topology_unit_interval());
            let (hx_id, _hx) = hb.fresh_local(alpha.clone());
            let e = alpha.clone();
            let e = hb.mk_pi(hx_id, BinderInfo::Default, alpha.clone(), e);
            let e = hb.mk_pi(ht_id, BinderInfo::Default, topology_unit_interval(), e);
            hb.finish_child(e)
        };
        let (h_id, h) = b.fresh_local(h_type.clone());

        // at_zero : ∀ x : α, Eq α (H 0 x) x
        let at_zero_param_type = {
            let mut azb = EnvDeclBuilder::child_of(&b);
            let (ax_id, ax) = azb.fresh_local(alpha.clone());
            let h_0_x = Expr::app(
                Expr::app(h.clone(), topology_unit_interval_zero()),
                ax.clone(),
            );
            let eq_body = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]),
                [alpha.clone(), h_0_x, ax.clone()],
            );
            azb.mk_pi(ax_id, BinderInfo::Default, alpha.clone(), eq_body)
        };
        let (az_id, _az) = b.fresh_local(at_zero_param_type.clone());

        // at_one : ∀ x : α, Eq α (H 1 x) x₀
        let at_one_param_type = {
            let mut aob = EnvDeclBuilder::child_of(&b);
            let (ox_id, ox) = aob.fresh_local(alpha.clone());
            let h_1_x = Expr::app(
                Expr::app(h.clone(), topology_unit_interval_one()),
                ox.clone(),
            );
            let eq_body = Expr::apps(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]),
                [alpha.clone(), h_1_x, x0.clone()],
            );
            aob.mk_pi(ox_id, BinderInfo::Default, alpha.clone(), eq_body)
        };
        let (ao_id, _ao) = b.fresh_local(at_one_param_type.clone());

        // cont : ∀ t : UnitInterval, Continuous (fun x => H t x)
        let cont_type = {
            let mut ctb = EnvDeclBuilder::child_of(&b);
            let (ct_id, ct) = ctb.fresh_local(topology_unit_interval());
            let slice_fun = {
                let mut slb = EnvDeclBuilder::child_of(&ctb);
                let (sx_id, sx) = slb.fresh_local(alpha.clone());
                let h_t_x = Expr::app(Expr::app(h.clone(), ct.clone()), sx.clone());
                slb.mk_lam(sx_id, BinderInfo::Default, alpha.clone(), h_t_x)
            };
            let continuous_app = Expr::apps(
                topology_continuous(u_level.clone(), u_level.clone()),
                [
                    alpha.clone(),
                    alpha.clone(),
                    inst.clone(),
                    inst.clone(),
                    slice_fun,
                ],
            );
            ctb.mk_pi(
                ct_id,
                BinderInfo::Default,
                topology_unit_interval(),
                continuous_app,
            )
        };
        let (cont_id, _cont) = b.fresh_local(cont_type.clone());

        // Result: Contraction x₀
        let e = mk_contraction_app(&alpha, &inst, &x0);
        let e = b.mk_pi(cont_id, BinderInfo::Default, cont_type, e);
        let e = b.mk_pi(ao_id, BinderInfo::Default, at_one_param_type, e);
        let e = b.mk_pi(az_id, BinderInfo::Default, at_zero_param_type, e);
        let e = b.mk_pi(h_id, BinderInfo::Default, h_type, e);
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
    decls.push(axiom("Topology.Contraction.mk", vec![u.clone()], mk_type));

    assert_eq!(decls.len(), DECL_COUNT);
    decls
}
