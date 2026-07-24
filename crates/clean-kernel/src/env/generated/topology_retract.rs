// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for `Topology.Retract` namespace (#1444).
//!
//! Migrated from handwritten `add_decl` calls in `topology_homotopy2.rs`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.Retract";
pub(crate) const DECL_COUNT: usize = 22;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.IsRetract",
    "Topology.Retraction",
    "Topology.Retraction.map",
    "Topology.Retraction.continuous",
    "Topology.Retraction.maps_into",
    "Topology.Retraction.fixes_subset",
    "Topology.is_retract_def",
    "Topology.IsDeformationRetract",
    "Topology.DeformationRetraction",
    "Topology.DeformationRetraction.toRetraction",
    "Topology.DeformationRetraction.homotopy",
    "Topology.is_deformation_retract_def",
    "Topology.IsStrongDeformationRetract",
    "Topology.StrongDeformationRetraction",
    "Topology.StrongDeformationRetraction.toDeformationRetraction",
    "Topology.StrongDeformationRetraction.fixes_points_rel",
    "Topology.is_strong_deformation_retract_def",
    "Topology.strong_deformation_retract_is_deformation_retract",
    "Topology.deformation_retract_is_retract",
    "Topology.deformation_retract_homotopy_equiv",
    "Topology.contractible_iff_point_deformation_retract",
    "Topology.retract_of_contractible_is_contractible",
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
    let continuous = |lvl1: Level, lvl2: Level| {
        Expr::const_(Name::from_string("Topology.Continuous"), vec![lvl1, lvl2])
    };
    let continuous_homotopy =
        |lvl: Level| Expr::const_(Name::from_string("Topology.ContinuousHomotopy"), vec![lvl]);
    let nonempty_const = |lvl: Level| Expr::const_(Name::from_string("Nonempty"), vec![lvl]);
    let iff_const = || Expr::const_(Name::from_string("Iff"), vec![]);
    let eq_const = |lvl: Level| Expr::const_(Name::from_string("Eq"), vec![lvl]);
    let is_retract = |lvl: Level| Expr::const_(Name::from_string("Topology.IsRetract"), vec![lvl]);
    let retraction = |lvl: Level| Expr::const_(Name::from_string("Topology.Retraction"), vec![lvl]);
    let retraction_map =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Retraction.map"), vec![lvl]);
    let is_deformation_retract = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.IsDeformationRetract"),
            vec![lvl],
        )
    };
    let deformation_retraction = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.DeformationRetraction"),
            vec![lvl],
        )
    };
    let dr_to_retraction = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.DeformationRetraction.toRetraction"),
            vec![lvl],
        )
    };
    let is_strong_deformation_retract = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.IsStrongDeformationRetract"),
            vec![lvl],
        )
    };
    let strong_deformation_retraction = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.StrongDeformationRetraction"),
            vec![lvl],
        )
    };
    let contractible =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Contractible"), vec![lvl]);

    let mut decls = Vec::with_capacity(DECL_COUNT);

    // ================================================================
    // 1. Topology.IsRetract : {X : Type u} -> [TopologicalSpace X] -> (X -> Prop) -> Prop
    // ================================================================
    let is_retract_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, _inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, _a) = b.fresh_local(a_ty.clone());

        let e = prop.clone();
        let e = b.mk_pi(a_id, BinderInfo::Default, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.IsRetract",
        vec![u.clone()],
        is_retract_type,
    ));

    // ================================================================
    // 2. Topology.Retraction : {X : Type u} -> [TopologicalSpace X] -> (X -> Prop) -> Type u
    // ================================================================
    let retraction_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, _inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, _a) = b.fresh_local(a_ty.clone());

        let e = type_u.clone();
        let e = b.mk_pi(a_id, BinderInfo::Default, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.Retraction",
        vec![u.clone()],
        retraction_type,
    ));

    // ================================================================
    // 3. Topology.Retraction.map : {X : Type u} -> [TopologicalSpace X] ->
    //    {A : X -> Prop} -> Retraction A -> (X -> X)
    // ================================================================
    let retraction_map_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());
        let ret_a = Expr::apps(
            retraction(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let (r_id, _r) = b.fresh_local(ret_a.clone());
        let xx = Expr::arrow(x.clone(), x.clone());

        let e = xx;
        let e = b.mk_pi(r_id, BinderInfo::Default, ret_a, e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.Retraction.map",
        vec![u.clone()],
        retraction_map_type,
    ));

    // ================================================================
    // 4. Topology.Retraction.continuous : {X : Type u} -> [TopologicalSpace X] ->
    //    {A : X -> Prop} -> (r : Retraction A) -> Continuous (map r)
    // ================================================================
    let retraction_continuous_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());
        let ret_a = Expr::apps(
            retraction(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let (r_id, r) = b.fresh_local(ret_a.clone());

        // map r : X -> X
        let map_r = Expr::apps(
            retraction_map(u_level.clone()),
            [x.clone(), inst.clone(), a.clone(), r.clone()],
        );

        // Continuous X X inst inst (map r)
        let cont_map_r = Expr::apps(
            continuous(u_level.clone(), u_level.clone()),
            [x.clone(), x.clone(), inst.clone(), inst.clone(), map_r],
        );

        let e = cont_map_r;
        let e = b.mk_pi(r_id, BinderInfo::Default, ret_a, e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.Retraction.continuous",
        vec![u.clone()],
        retraction_continuous_type,
    ));

    // ================================================================
    // 5. Topology.Retraction.maps_into : {X : Type u} -> [TopologicalSpace X] ->
    //    {A : X -> Prop} -> (r : Retraction A) -> forall x, A (map r x)
    // ================================================================
    let retraction_maps_into_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());
        let ret_a = Expr::apps(
            retraction(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let (r_id, r) = b.fresh_local(ret_a.clone());
        let (xv_id, xv) = b.fresh_local(x.clone());

        // map r xv
        let map_r_xv = Expr::app(
            Expr::apps(
                retraction_map(u_level.clone()),
                [x.clone(), inst.clone(), a.clone(), r.clone()],
            ),
            xv.clone(),
        );

        // A (map r xv)
        let a_map_r_xv = Expr::app(a.clone(), map_r_xv);

        let e = a_map_r_xv;
        let e = b.mk_pi(xv_id, BinderInfo::Default, x.clone(), e);
        let e = b.mk_pi(r_id, BinderInfo::Default, ret_a, e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.Retraction.maps_into",
        vec![u.clone()],
        retraction_maps_into_type,
    ));

    // ================================================================
    // 6. Topology.Retraction.fixes_subset : {X : Type u} -> [TopologicalSpace X] ->
    //    {A : X -> Prop} -> (r : Retraction A) -> forall x, A x -> Eq (map r x) x
    // ================================================================
    let retraction_fixes_subset_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());
        let ret_a = Expr::apps(
            retraction(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let (r_id, r) = b.fresh_local(ret_a.clone());
        let (xv_id, xv) = b.fresh_local(x.clone());
        // (hx : A xv)
        let a_xv = Expr::app(a.clone(), xv.clone());
        let (hx_id, _hx) = b.fresh_local(a_xv.clone());

        // map r xv
        let map_r_xv = Expr::app(
            Expr::apps(
                retraction_map(u_level.clone()),
                [x.clone(), inst.clone(), a.clone(), r.clone()],
            ),
            xv.clone(),
        );

        // Eq X (map r xv) xv
        let eq_body = Expr::apps(
            eq_const(Level::succ(u_level.clone())),
            [x.clone(), map_r_xv, xv.clone()],
        );

        let e = eq_body;
        let e = b.mk_pi(hx_id, BinderInfo::Default, a_xv, e);
        let e = b.mk_pi(xv_id, BinderInfo::Default, x.clone(), e);
        let e = b.mk_pi(r_id, BinderInfo::Default, ret_a, e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.Retraction.fixes_subset",
        vec![u.clone()],
        retraction_fixes_subset_type,
    ));

    // ================================================================
    // 7. Topology.is_retract_def : {X : Type u} -> [TopologicalSpace X] ->
    //    {A : X -> Prop} -> Iff (IsRetract A) (Nonempty (Retraction A))
    // ================================================================
    let is_retract_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());

        let is_ret_a = Expr::apps(
            is_retract(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let ret_a = Expr::apps(
            retraction(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let nonempty_ret_a = Expr::app(nonempty_const(Level::succ(u_level.clone())), ret_a);
        let iff_body = Expr::app(Expr::app(iff_const(), is_ret_a), nonempty_ret_a);

        let e = iff_body;
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.is_retract_def",
        vec![u.clone()],
        is_retract_def_type,
    ));

    // ================================================================
    // 8. Topology.IsDeformationRetract : {X : Type u} -> [TopologicalSpace X] -> (X -> Prop) -> Prop
    // ================================================================
    let is_deformation_retract_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, _inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, _a) = b.fresh_local(a_ty.clone());
        let e = prop.clone();
        let e = b.mk_pi(a_id, BinderInfo::Default, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.IsDeformationRetract",
        vec![u.clone()],
        is_deformation_retract_type,
    ));

    // ================================================================
    // 9. Topology.DeformationRetraction : {X : Type u} -> [TopologicalSpace X] -> (X -> Prop) -> Type u
    // ================================================================
    let deformation_retraction_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, _inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, _a) = b.fresh_local(a_ty.clone());
        let e = type_u.clone();
        let e = b.mk_pi(a_id, BinderInfo::Default, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.DeformationRetraction",
        vec![u.clone()],
        deformation_retraction_type,
    ));

    // ================================================================
    // 10. Topology.DeformationRetraction.toRetraction : {X : Type u} ->
    //     [TopologicalSpace X] -> {A : X -> Prop} -> DeformationRetraction A -> Retraction A
    // ================================================================
    let dr_to_retraction_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());
        let dr_a = Expr::apps(
            deformation_retraction(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let (dr_id, _dr) = b.fresh_local(dr_a.clone());
        let ret_a = Expr::apps(
            retraction(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );

        let e = ret_a;
        let e = b.mk_pi(dr_id, BinderInfo::Default, dr_a, e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.DeformationRetraction.toRetraction",
        vec![u.clone()],
        dr_to_retraction_type,
    ));

    // ================================================================
    // 11. Topology.DeformationRetraction.homotopy : {X : Type u} -> [TopologicalSpace X] ->
    //     {A : X -> Prop} -> (dr : DeformationRetraction A) ->
    //     ContinuousHomotopy id (map (toRetraction dr))
    // ================================================================
    let dr_homotopy_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());
        let dr_a = Expr::apps(
            deformation_retraction(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let (dr_id, dr) = b.fresh_local(dr_a.clone());

        // id : X -> X  (lambda (y : X), y)
        let (y_id, y) = b.fresh_local(x.clone());
        let id_x = b.mk_lam(y_id, BinderInfo::Default, x.clone(), y);

        // toRetraction dr
        let to_retraction_dr = Expr::app(
            Expr::apps(
                dr_to_retraction(u_level.clone()),
                [x.clone(), inst.clone(), a.clone()],
            ),
            dr.clone(),
        );

        // map (toRetraction dr)
        let map_to_retraction_dr = Expr::app(
            Expr::apps(
                retraction_map(u_level.clone()),
                [x.clone(), inst.clone(), a.clone()],
            ),
            to_retraction_dr,
        );

        // ContinuousHomotopy X X inst inst id (map (toRetraction dr))
        let ch_id_map = Expr::apps(
            continuous_homotopy(u_level.clone()),
            [
                x.clone(),
                x.clone(),
                inst.clone(),
                inst.clone(),
                id_x,
                map_to_retraction_dr,
            ],
        );

        let e = ch_id_map;
        let e = b.mk_pi(dr_id, BinderInfo::Default, dr_a, e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.DeformationRetraction.homotopy",
        vec![u.clone()],
        dr_homotopy_type,
    ));

    // ================================================================
    // 12. Topology.is_deformation_retract_def : {X : Type u} -> [TopologicalSpace X] ->
    //     {A : X -> Prop} -> Iff (IsDeformationRetract A) (Nonempty (DeformationRetraction A))
    // ================================================================
    let is_deformation_retract_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());

        let is_dr_a = Expr::apps(
            is_deformation_retract(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let dr_a = Expr::apps(
            deformation_retraction(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        // DeformationRetraction X A : Type u, Nonempty needs u+1
        let nonempty_dr_a = Expr::app(nonempty_const(Level::succ(u_level.clone())), dr_a);
        let iff_body = Expr::app(Expr::app(iff_const(), is_dr_a), nonempty_dr_a);

        let e = iff_body;
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.is_deformation_retract_def",
        vec![u.clone()],
        is_deformation_retract_def_type,
    ));

    // ================================================================
    // 13. Topology.IsStrongDeformationRetract : {X : Type u} -> [TopologicalSpace X] ->
    //     (X -> Prop) -> Prop
    // ================================================================
    let is_strong_deformation_retract_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, _inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, _a) = b.fresh_local(a_ty.clone());
        let e = prop.clone();
        let e = b.mk_pi(a_id, BinderInfo::Default, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.IsStrongDeformationRetract",
        vec![u.clone()],
        is_strong_deformation_retract_type,
    ));

    // ================================================================
    // 14. Topology.StrongDeformationRetraction : {X : Type u} -> [TopologicalSpace X] ->
    //     (X -> Prop) -> Type u
    // ================================================================
    let strong_deformation_retraction_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, _inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, _a) = b.fresh_local(a_ty.clone());
        let e = type_u.clone();
        let e = b.mk_pi(a_id, BinderInfo::Default, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.StrongDeformationRetraction",
        vec![u.clone()],
        strong_deformation_retraction_type,
    ));

    // ================================================================
    // 15. Topology.StrongDeformationRetraction.toDeformationRetraction : {X : Type u} ->
    //     [TopologicalSpace X] -> {A : X -> Prop} ->
    //     StrongDeformationRetraction A -> DeformationRetraction A
    // ================================================================
    let sdr_to_dr_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());
        let sdr_a = Expr::apps(
            strong_deformation_retraction(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let (sdr_id, _sdr) = b.fresh_local(sdr_a.clone());
        let dr_a = Expr::apps(
            deformation_retraction(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let e = dr_a;
        let e = b.mk_pi(sdr_id, BinderInfo::Default, sdr_a, e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.StrongDeformationRetraction.toDeformationRetraction",
        vec![u.clone()],
        sdr_to_dr_type,
    ));

    // ================================================================
    // 16. Topology.StrongDeformationRetraction.fixes_points_rel : {X : Type u} ->
    //     [TopologicalSpace X] -> {A : X -> Prop} ->
    //     StrongDeformationRetraction A -> Prop
    // ================================================================
    let sdr_fixes_rel_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());
        let sdr_a = Expr::apps(
            strong_deformation_retraction(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let (sdr_id, _sdr) = b.fresh_local(sdr_a.clone());
        let e = prop.clone();
        let e = b.mk_pi(sdr_id, BinderInfo::Default, sdr_a, e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.StrongDeformationRetraction.fixes_points_rel",
        vec![u.clone()],
        sdr_fixes_rel_type,
    ));

    // ================================================================
    // 17. Topology.is_strong_deformation_retract_def : {X : Type u} -> [TopologicalSpace X] ->
    //     {A : X -> Prop} -> Iff (IsStrongDeformationRetract A)
    //                            (Nonempty (StrongDeformationRetraction A))
    // ================================================================
    let is_strong_deformation_retract_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());

        let is_sdr_a = Expr::apps(
            is_strong_deformation_retract(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let sdr_a = Expr::apps(
            strong_deformation_retraction(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        // StrongDeformationRetraction X A : Type u, Nonempty needs u+1
        let nonempty_sdr_a = Expr::app(nonempty_const(Level::succ(u_level.clone())), sdr_a);
        let iff_body = Expr::app(Expr::app(iff_const(), is_sdr_a), nonempty_sdr_a);

        let e = iff_body;
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.is_strong_deformation_retract_def",
        vec![u.clone()],
        is_strong_deformation_retract_def_type,
    ));

    // ================================================================
    // 18. Topology.strong_deformation_retract_is_deformation_retract : {X : Type u} ->
    //     [TopologicalSpace X] -> {A : X -> Prop} ->
    //     IsStrongDeformationRetract A -> IsDeformationRetract A
    // ================================================================
    let sdr_is_dr_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());
        let is_sdr_a = Expr::apps(
            is_strong_deformation_retract(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let (h_id, _h) = b.fresh_local(is_sdr_a.clone());
        let is_dr_a = Expr::apps(
            is_deformation_retract(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let e = is_dr_a;
        let e = b.mk_pi(h_id, BinderInfo::Default, is_sdr_a, e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.strong_deformation_retract_is_deformation_retract",
        vec![u.clone()],
        sdr_is_dr_type,
    ));

    // ================================================================
    // 19. Topology.deformation_retract_is_retract : {X : Type u} ->
    //     [TopologicalSpace X] -> {A : X -> Prop} ->
    //     IsDeformationRetract A -> IsRetract A
    // ================================================================
    let dr_is_retract_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());
        let is_dr_a = Expr::apps(
            is_deformation_retract(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let (h_id, _h) = b.fresh_local(is_dr_a.clone());
        let is_retract_a = Expr::apps(
            is_retract(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let e = is_retract_a;
        let e = b.mk_pi(h_id, BinderInfo::Default, is_dr_a, e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.deformation_retract_is_retract",
        vec![u.clone()],
        dr_is_retract_type,
    ));

    // ================================================================
    // 20. Topology.deformation_retract_homotopy_equiv : {X : Type u} ->
    //     [TopologicalSpace X] -> {A : X -> Prop} ->
    //     IsDeformationRetract A -> Prop
    // ================================================================
    let dr_homotopy_equiv_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());
        let is_dr_a = Expr::apps(
            is_deformation_retract(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let (h_id, _h) = b.fresh_local(is_dr_a.clone());
        let e = prop.clone();
        let e = b.mk_pi(h_id, BinderInfo::Default, is_dr_a, e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.deformation_retract_homotopy_equiv",
        vec![u.clone()],
        dr_homotopy_equiv_type,
    ));

    // ================================================================
    // 21. Topology.contractible_iff_point_deformation_retract : {X : Type u} ->
    //     [TopologicalSpace X] -> Prop
    // ================================================================
    let contractible_iff_point_dr_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, _inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let e = prop.clone();
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.contractible_iff_point_deformation_retract",
        vec![u.clone()],
        contractible_iff_point_dr_type,
    ));

    // ================================================================
    // 22. Topology.retract_of_contractible_is_contractible : {X : Type u} ->
    //     [TopologicalSpace X] -> {A : X -> Prop} ->
    //     Contractible X -> IsRetract A -> Prop
    // ================================================================
    let retract_of_contractible_type = {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), x.clone()));
        let a_ty = Expr::arrow(x.clone(), prop.clone());
        let (a_id, a) = b.fresh_local(a_ty.clone());
        let contractible_x = Expr::app(
            Expr::app(contractible(u_level.clone()), x.clone()),
            inst.clone(),
        );
        let (hc_id, _hc) = b.fresh_local(contractible_x.clone());
        let is_retract_a = Expr::apps(
            is_retract(u_level.clone()),
            [x.clone(), inst.clone(), a.clone()],
        );
        let (hr_id, _hr) = b.fresh_local(is_retract_a.clone());
        let e = prop.clone();
        let e = b.mk_pi(hr_id, BinderInfo::Default, is_retract_a, e);
        let e = b.mk_pi(hc_id, BinderInfo::Default, contractible_x, e);
        let e = b.mk_pi(a_id, BinderInfo::Implicit, a_ty, e);
        let e = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), x.clone()),
            e,
        );
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.retract_of_contractible_is_contractible",
        vec![u.clone()],
        retract_of_contractible_type,
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
