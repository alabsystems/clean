// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for `Topology.CoveringSpace` namespace (#1444).
//!
//! Migrated from handwritten `add_decl` calls in `topology_homotopy.rs`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.CoveringSpace";
pub(crate) const DECL_COUNT: usize = 18;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.Fiber",
    "Topology.fiber_def",
    "Topology.Discrete",
    "Topology.CoveringMap",
    "Topology.CoveringMap.surjective",
    "Topology.EvenlyCovers",
    "Topology.CoveringMap.evenly_covered",
    "Topology.CoveringMap.discrete_fiber",
    "Topology.Lift",
    "Topology.lift_def",
    "Topology.CoveringMap.continuous",
    "Topology.IsCoveringSpace",
    "Topology.is_covering_space_def",
    "Topology.UniversalCover",
    "Topology.UniversalCover.proj",
    "Topology.UniversalCover.is_covering",
    "Topology.UniversalCover.simply_connected",
    "Topology.UniversalCover.universal_property",
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

    let v = Name::from_string("v");
    let v_level = Level::param(v.clone());
    let type_v = Expr::sort(Level::succ(v_level.clone()));

    let topological_space =
        |lvl: Level| Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl]);
    let is_open = |lvl: Level| Expr::const_(Name::from_string("IsOpen"), vec![lvl]);
    let topology_continuous = |lvl1: Level, lvl2: Level| {
        Expr::const_(Name::from_string("Topology.Continuous"), vec![lvl1, lvl2])
    };
    let iff_const = || Expr::const_(Name::from_string("Iff"), vec![]);
    let and_const = || Expr::const_(Name::from_string("And"), vec![]);
    let exists_const = |lvl: Level| Expr::const_(Name::from_string("Exists"), vec![lvl]);
    let eq_const = |lvl: Level| Expr::const_(Name::from_string("Eq"), vec![lvl]);
    let topology_path_connected =
        |lvl: Level| Expr::const_(Name::from_string("Topology.PathConnected"), vec![lvl]);

    let fiber = |lvl: Level| Expr::const_(Name::from_string("Topology.Fiber"), vec![lvl]);
    let discrete = |lvl: Level| Expr::const_(Name::from_string("Topology.Discrete"), vec![lvl]);
    let covering_map =
        |lvl: Level| Expr::const_(Name::from_string("Topology.CoveringMap"), vec![lvl]);
    let evenly_covers =
        |lvl: Level| Expr::const_(Name::from_string("Topology.EvenlyCovers"), vec![lvl]);
    let lift = |u_lvl: Level, v_lvl: Level| {
        Expr::const_(Name::from_string("Topology.Lift"), vec![u_lvl, v_lvl])
    };
    let is_covering_space =
        |lvl: Level| Expr::const_(Name::from_string("Topology.IsCoveringSpace"), vec![lvl]);
    let universal_cover =
        |lvl: Level| Expr::const_(Name::from_string("Topology.UniversalCover"), vec![lvl]);

    let mut decls = Vec::with_capacity(DECL_COUNT);

    // ================================================================
    // Topology.Fiber : {E B : Type u} → (E → B) → B → (E → Prop)
    // ================================================================
    let fiber_type = {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e_var) = b.fresh_local(type_u.clone());
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (tmp_id, _) = b.fresh_local(e_var.clone());
        let p_ty = b.mk_pi(tmp_id, BinderInfo::Default, e_var.clone(), b_var.clone());
        let (p_id, _p) = b.fresh_local(p_ty.clone());
        let (bb_id, _bb) = b.fresh_local(b_var.clone());
        let (ee_id, _ee) = b.fresh_local(e_var.clone());
        let r = prop.clone();
        let r = b.mk_pi(ee_id, BinderInfo::Default, e_var.clone(), r);
        let r = b.mk_pi(bb_id, BinderInfo::Default, b_var.clone(), r);
        let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        let r = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom("Topology.Fiber", vec![u.clone()], fiber_type));

    // ================================================================
    // Topology.fiber_def : {E B : Type u} → (p : E → B) → (b : B) → (e : E) →
    //   Iff (Fiber p b e) (Eq B (p e) b)
    // ================================================================
    let fiber_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e_var) = b.fresh_local(type_u.clone());
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (tmp_id, _) = b.fresh_local(e_var.clone());
        let p_ty = b.mk_pi(tmp_id, BinderInfo::Default, e_var.clone(), b_var.clone());
        let (p_id, p) = b.fresh_local(p_ty.clone());
        let (bb_id, bb) = b.fresh_local(b_var.clone());
        let (ee_id, ee) = b.fresh_local(e_var.clone());
        let fiber_p_b_e = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(fiber(u_level.clone()), e_var.clone()),
                        b_var.clone(),
                    ),
                    p.clone(),
                ),
                bb.clone(),
            ),
            ee.clone(),
        );
        let p_e = Expr::app(p.clone(), ee.clone());
        let eq_p_e_b = Expr::app(
            Expr::app(
                Expr::app(eq_const(Level::succ(u_level.clone())), b_var.clone()),
                p_e,
            ),
            bb.clone(),
        );
        let body = Expr::app(Expr::app(iff_const(), fiber_p_b_e), eq_p_e_b);
        let r = b.mk_pi(ee_id, BinderInfo::Default, e_var.clone(), body);
        let r = b.mk_pi(bb_id, BinderInfo::Default, b_var.clone(), r);
        let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        let r = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom("Topology.fiber_def", vec![u.clone()], fiber_def_type));

    // ================================================================
    // Topology.Discrete : {α : Type u} → (α → Prop) → Prop
    // ================================================================
    let discrete_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (tmp_id, _) = b.fresh_local(alpha.clone());
        let s_ty = b.mk_pi(tmp_id, BinderInfo::Default, alpha.clone(), prop.clone());
        let (s_id, _s) = b.fresh_local(s_ty.clone());
        let r = prop.clone();
        let r = b.mk_pi(s_id, BinderInfo::Default, s_ty, r);
        let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom("Topology.Discrete", vec![u.clone()], discrete_type));

    // ================================================================
    // Topology.CoveringMap : {E B : Type u} → [TopologicalSpace E] → [TopologicalSpace B] →
    //   (E → B) → Prop
    // ================================================================
    let covering_map_type = {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e_var) = b.fresh_local(type_u.clone());
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (inst_e_id, _) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), e_var.clone()));
        let (inst_b_id, _) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), b_var.clone()));
        let (tmp_id, _) = b.fresh_local(e_var.clone());
        let p_ty = b.mk_pi(tmp_id, BinderInfo::Default, e_var.clone(), b_var.clone());
        let (p_id, _p) = b.fresh_local(p_ty.clone());
        let r = prop.clone();
        let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
        let r = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), b_var.clone()),
            r,
        );
        let r = b.mk_pi(
            inst_e_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), e_var.clone()),
            r,
        );
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        let r = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom(
        "Topology.CoveringMap",
        vec![u.clone()],
        covering_map_type,
    ));

    // ================================================================
    // Topology.CoveringMap.surjective : {E B : Type u} → [TopologicalSpace E] →
    //   [TopologicalSpace B] → (p : E → B) → CoveringMap p → ∀ b, ∃ e, Eq (p e) b
    // ================================================================
    let surjective_type = {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e_var) = b.fresh_local(type_u.clone());
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (inst_e_id, inst_e) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), e_var.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), b_var.clone()));
        let (tmp_id, _) = b.fresh_local(e_var.clone());
        let p_ty = b.mk_pi(tmp_id, BinderInfo::Default, e_var.clone(), b_var.clone());
        let (p_id, p) = b.fresh_local(p_ty.clone());
        let cov_map_p = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(covering_map(u_level.clone()), e_var.clone()),
                        b_var.clone(),
                    ),
                    inst_e.clone(),
                ),
                inst_b.clone(),
            ),
            p.clone(),
        );
        let (h_id, _h) = b.fresh_local(cov_map_p.clone());
        let (bb_id, bb) = b.fresh_local(b_var.clone());
        let exists_body = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (e2_id, e2) = c.fresh_local(e_var.clone());
            let eq_inner = Expr::app(
                Expr::app(
                    Expr::app(eq_const(Level::succ(u_level.clone())), b_var.clone()),
                    Expr::app(p.clone(), e2),
                ),
                bb.clone(),
            );
            let lam = c.mk_lam(e2_id, BinderInfo::Default, e_var.clone(), eq_inner);
            c.finish_child(lam)
        };
        let r = Expr::app(
            Expr::app(exists_const(Level::succ(u_level.clone())), e_var.clone()),
            exists_body,
        );
        let r = b.mk_pi(bb_id, BinderInfo::Default, b_var.clone(), r);
        let r = b.mk_pi(h_id, BinderInfo::Default, cov_map_p, r);
        let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
        let r = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), b_var.clone()),
            r,
        );
        let r = b.mk_pi(
            inst_e_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), e_var.clone()),
            r,
        );
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        let r = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom(
        "Topology.CoveringMap.surjective",
        vec![u.clone()],
        surjective_type,
    ));

    // ================================================================
    // Topology.EvenlyCovers : {E B : Type u} → [TopologicalSpace E] → [TopologicalSpace B] →
    //   (E → B) → (B → Prop) → Prop
    // ================================================================
    let evenly_covers_type = {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e_var) = b.fresh_local(type_u.clone());
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (inst_e_id, _) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), e_var.clone()));
        let (inst_b_id, _) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), b_var.clone()));
        let (tmp_id, _) = b.fresh_local(e_var.clone());
        let p_ty = b.mk_pi(tmp_id, BinderInfo::Default, e_var.clone(), b_var.clone());
        let (p_id, _p) = b.fresh_local(p_ty.clone());
        let (tmp2_id, _) = b.fresh_local(b_var.clone());
        let u_ty = b.mk_pi(tmp2_id, BinderInfo::Default, b_var.clone(), prop.clone());
        let (u_id, _u_var) = b.fresh_local(u_ty.clone());
        let r = prop.clone();
        let r = b.mk_pi(u_id, BinderInfo::Default, u_ty, r);
        let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
        let r = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), b_var.clone()),
            r,
        );
        let r = b.mk_pi(
            inst_e_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), e_var.clone()),
            r,
        );
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        let r = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom(
        "Topology.EvenlyCovers",
        vec![u.clone()],
        evenly_covers_type,
    ));

    // ================================================================
    // Topology.CoveringMap.evenly_covered
    // ================================================================
    let evenly_covered_type = {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e_var) = b.fresh_local(type_u.clone());
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (inst_e_id, inst_e) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), e_var.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), b_var.clone()));
        let (tmp_id, _) = b.fresh_local(e_var.clone());
        let p_ty = b.mk_pi(tmp_id, BinderInfo::Default, e_var.clone(), b_var.clone());
        let (p_id, p) = b.fresh_local(p_ty.clone());
        let cov_map_p = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(covering_map(u_level.clone()), e_var.clone()),
                        b_var.clone(),
                    ),
                    inst_e.clone(),
                ),
                inst_b.clone(),
            ),
            p.clone(),
        );
        let (h_id, _h) = b.fresh_local(cov_map_p.clone());
        let (bb_id, bb) = b.fresh_local(b_var.clone());
        // ∃ U : B → Prop, And (IsOpen U) (And (U b) (EvenlyCovers p U))
        let exists_body = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (tmp3_id, _) = c.fresh_local(b_var.clone());
            let u_ty = c.mk_pi(tmp3_id, BinderInfo::Default, b_var.clone(), prop.clone());
            let (u2_id, u_var) = c.fresh_local(u_ty.clone());
            let is_open_u_expr = Expr::app(
                Expr::app(
                    Expr::app(is_open(u_level.clone()), b_var.clone()),
                    inst_b.clone(),
                ),
                u_var.clone(),
            );
            let u_b_expr = Expr::app(u_var.clone(), bb.clone());
            let ec_p_u = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(evenly_covers(u_level.clone()), e_var.clone()),
                                b_var.clone(),
                            ),
                            inst_e.clone(),
                        ),
                        inst_b.clone(),
                    ),
                    p.clone(),
                ),
                u_var.clone(),
            );
            let and_body = Expr::app(
                Expr::app(and_const(), is_open_u_expr),
                Expr::app(Expr::app(and_const(), u_b_expr), ec_p_u),
            );
            let lam = c.mk_lam(u2_id, BinderInfo::Default, u_ty.clone(), and_body);
            c.finish_child(lam)
        };
        let b_to_prop = {
            let mut c2 = EnvDeclBuilder::child_of(&b);
            let (tmp4_id, _) = c2.fresh_local(b_var.clone());
            let ty = c2.mk_pi(tmp4_id, BinderInfo::Default, b_var.clone(), prop.clone());
            c2.finish_child(ty)
        };
        let r = Expr::app(
            Expr::app(exists_const(Level::succ(u_level.clone())), b_to_prop),
            exists_body,
        );
        let r = b.mk_pi(bb_id, BinderInfo::Default, b_var.clone(), r);
        let r = b.mk_pi(h_id, BinderInfo::Default, cov_map_p, r);
        let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
        let r = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), b_var.clone()),
            r,
        );
        let r = b.mk_pi(
            inst_e_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), e_var.clone()),
            r,
        );
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        let r = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom(
        "Topology.CoveringMap.evenly_covered",
        vec![u.clone()],
        evenly_covered_type,
    ));

    // ================================================================
    // Topology.CoveringMap.discrete_fiber
    // ================================================================
    let discrete_fiber_type = {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e_var) = b.fresh_local(type_u.clone());
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (inst_e_id, inst_e) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), e_var.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), b_var.clone()));
        let (tmp_id, _) = b.fresh_local(e_var.clone());
        let p_ty = b.mk_pi(tmp_id, BinderInfo::Default, e_var.clone(), b_var.clone());
        let (p_id, p) = b.fresh_local(p_ty.clone());
        let cov_map_p = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(covering_map(u_level.clone()), e_var.clone()),
                        b_var.clone(),
                    ),
                    inst_e.clone(),
                ),
                inst_b.clone(),
            ),
            p.clone(),
        );
        let (h_id, _h) = b.fresh_local(cov_map_p.clone());
        let (bb_id, bb) = b.fresh_local(b_var.clone());
        let fiber_p_b = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(fiber(u_level.clone()), e_var.clone()),
                    b_var.clone(),
                ),
                p.clone(),
            ),
            bb.clone(),
        );
        let r = Expr::app(
            Expr::app(discrete(u_level.clone()), e_var.clone()),
            fiber_p_b,
        );
        let r = b.mk_pi(bb_id, BinderInfo::Default, b_var.clone(), r);
        let r = b.mk_pi(h_id, BinderInfo::Default, cov_map_p, r);
        let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
        let r = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), b_var.clone()),
            r,
        );
        let r = b.mk_pi(
            inst_e_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), e_var.clone()),
            r,
        );
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        let r = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom(
        "Topology.CoveringMap.discrete_fiber",
        vec![u.clone()],
        discrete_fiber_type,
    ));

    // ================================================================
    // Topology.Lift : {E B : Type u} → {X : Type v} → [TopologicalSpace E] →
    //   [TopologicalSpace B] → [TopologicalSpace X] →
    //   (E → B) → (X → B) → (X → E) → Prop
    // ================================================================
    let lift_type = {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e_var) = b.fresh_local(type_u.clone());
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (x_id, x_var) = b.fresh_local(type_v.clone());
        let (inst_e_id, _) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), e_var.clone()));
        let (inst_b_id, _) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), b_var.clone()));
        let (inst_x_id, _) =
            b.fresh_local(Expr::app(topological_space(v_level.clone()), x_var.clone()));
        let (tmp_id, _) = b.fresh_local(e_var.clone());
        let p_ty = b.mk_pi(tmp_id, BinderInfo::Default, e_var.clone(), b_var.clone());
        let (p_id, _p) = b.fresh_local(p_ty.clone());
        let (tmp2_id, _) = b.fresh_local(x_var.clone());
        let f_ty = b.mk_pi(tmp2_id, BinderInfo::Default, x_var.clone(), b_var.clone());
        let (f_id, _f) = b.fresh_local(f_ty.clone());
        let (tmp3_id, _) = b.fresh_local(x_var.clone());
        let ft_ty = b.mk_pi(tmp3_id, BinderInfo::Default, x_var.clone(), e_var.clone());
        let (ft_id, _ft) = b.fresh_local(ft_ty.clone());
        let r = prop.clone();
        let r = b.mk_pi(ft_id, BinderInfo::Default, ft_ty, r);
        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
        let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
        let r = b.mk_pi(
            inst_x_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(v_level.clone()), x_var.clone()),
            r,
        );
        let r = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), b_var.clone()),
            r,
        );
        let r = b.mk_pi(
            inst_e_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), e_var.clone()),
            r,
        );
        let r = b.mk_pi(x_id, BinderInfo::Implicit, type_v.clone(), r);
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        let r = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom(
        "Topology.Lift",
        vec![u.clone(), v.clone()],
        lift_type,
    ));

    // ================================================================
    // Topology.lift_def
    // ================================================================
    let lift_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e_var) = b.fresh_local(type_u.clone());
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (x_id, x_var) = b.fresh_local(type_v.clone());
        let (inst_e_id, inst_e) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), e_var.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), b_var.clone()));
        let (inst_x_id, inst_x) =
            b.fresh_local(Expr::app(topological_space(v_level.clone()), x_var.clone()));
        let (tmp_id, _) = b.fresh_local(e_var.clone());
        let p_ty = b.mk_pi(tmp_id, BinderInfo::Default, e_var.clone(), b_var.clone());
        let (p_id, p) = b.fresh_local(p_ty.clone());
        let (tmp2_id, _) = b.fresh_local(x_var.clone());
        let f_ty = b.mk_pi(tmp2_id, BinderInfo::Default, x_var.clone(), b_var.clone());
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let (tmp3_id, _) = b.fresh_local(x_var.clone());
        let ft_ty = b.mk_pi(tmp3_id, BinderInfo::Default, x_var.clone(), e_var.clone());
        let (ft_id, ft) = b.fresh_local(ft_ty.clone());
        let lift_app = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::app(
                                        Expr::app(
                                            lift(u_level.clone(), v_level.clone()),
                                            e_var.clone(),
                                        ),
                                        b_var.clone(),
                                    ),
                                    x_var.clone(),
                                ),
                                inst_e.clone(),
                            ),
                            inst_b.clone(),
                        ),
                        inst_x.clone(),
                    ),
                    p.clone(),
                ),
                f.clone(),
            ),
            ft.clone(),
        );
        let forall_body = {
            let mut c = EnvDeclBuilder::child_of(&b);
            let (xx_id, xx) = c.fresh_local(x_var.clone());
            let eq_inner = Expr::app(
                Expr::app(
                    Expr::app(eq_const(Level::succ(u_level.clone())), b_var.clone()),
                    Expr::app(p.clone(), Expr::app(ft.clone(), xx.clone())),
                ),
                Expr::app(f.clone(), xx),
            );
            let r = c.mk_pi(xx_id, BinderInfo::Default, x_var.clone(), eq_inner);
            c.finish_child(r)
        };
        let body = Expr::app(Expr::app(iff_const(), lift_app), forall_body);
        let r = b.mk_pi(ft_id, BinderInfo::Default, ft_ty, body);
        let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
        let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
        let r = b.mk_pi(
            inst_x_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(v_level.clone()), x_var.clone()),
            r,
        );
        let r = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), b_var.clone()),
            r,
        );
        let r = b.mk_pi(
            inst_e_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), e_var.clone()),
            r,
        );
        let r = b.mk_pi(x_id, BinderInfo::Implicit, type_v.clone(), r);
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        let r = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom(
        "Topology.lift_def",
        vec![u.clone(), v.clone()],
        lift_def_type,
    ));

    // ================================================================
    // Topology.CoveringMap.continuous
    // ================================================================
    let covering_map_continuous_type = {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e_var) = b.fresh_local(type_u.clone());
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (inst_e_id, inst_e) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), e_var.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), b_var.clone()));
        let (tmp_id, _) = b.fresh_local(e_var.clone());
        let p_ty = b.mk_pi(tmp_id, BinderInfo::Default, e_var.clone(), b_var.clone());
        let (p_id, p) = b.fresh_local(p_ty.clone());
        let cov_map_p = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(covering_map(u_level.clone()), e_var.clone()),
                        b_var.clone(),
                    ),
                    inst_e.clone(),
                ),
                inst_b.clone(),
            ),
            p.clone(),
        );
        let (h_id, _h) = b.fresh_local(cov_map_p.clone());
        let continuous_p = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            topology_continuous(u_level.clone(), u_level.clone()),
                            e_var.clone(),
                        ),
                        b_var.clone(),
                    ),
                    inst_e.clone(),
                ),
                inst_b.clone(),
            ),
            p.clone(),
        );
        let r = b.mk_pi(h_id, BinderInfo::Default, cov_map_p, continuous_p);
        let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
        let r = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), b_var.clone()),
            r,
        );
        let r = b.mk_pi(
            inst_e_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), e_var.clone()),
            r,
        );
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        let r = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom(
        "Topology.CoveringMap.continuous",
        vec![u.clone()],
        covering_map_continuous_type,
    ));

    // ================================================================
    // Topology.IsCoveringSpace : {E B : Type u} → [TopologicalSpace E] → [TopologicalSpace B] →
    //   (E → B) → Prop
    // ================================================================
    let is_covering_space_type = {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e_var) = b.fresh_local(type_u.clone());
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (inst_e_id, _) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), e_var.clone()));
        let (inst_b_id, _) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), b_var.clone()));
        let (tmp_id, _) = b.fresh_local(e_var.clone());
        let p_ty = b.mk_pi(tmp_id, BinderInfo::Default, e_var.clone(), b_var.clone());
        let (p_id, _p) = b.fresh_local(p_ty.clone());
        let r = prop.clone();
        let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
        let r = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), b_var.clone()),
            r,
        );
        let r = b.mk_pi(
            inst_e_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), e_var.clone()),
            r,
        );
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        let r = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom(
        "Topology.IsCoveringSpace",
        vec![u.clone()],
        is_covering_space_type,
    ));

    // ================================================================
    // Topology.is_covering_space_def
    // ================================================================
    let is_covering_space_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e_var) = b.fresh_local(type_u.clone());
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (inst_e_id, inst_e) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), e_var.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), b_var.clone()));
        let (tmp_id, _) = b.fresh_local(e_var.clone());
        let p_ty = b.mk_pi(tmp_id, BinderInfo::Default, e_var.clone(), b_var.clone());
        let (p_id, p) = b.fresh_local(p_ty.clone());
        let is_cov = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(is_covering_space(u_level.clone()), e_var.clone()),
                        b_var.clone(),
                    ),
                    inst_e.clone(),
                ),
                inst_b.clone(),
            ),
            p.clone(),
        );
        let cov_map = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(covering_map(u_level.clone()), e_var.clone()),
                        b_var.clone(),
                    ),
                    inst_e.clone(),
                ),
                inst_b.clone(),
            ),
            p.clone(),
        );
        let body = Expr::app(Expr::app(iff_const(), is_cov), cov_map);
        let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, body);
        let r = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), b_var.clone()),
            r,
        );
        let r = b.mk_pi(
            inst_e_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), e_var.clone()),
            r,
        );
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        let r = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom(
        "Topology.is_covering_space_def",
        vec![u.clone()],
        is_covering_space_def_type,
    ));

    // ================================================================
    // Topology.UniversalCover : {B : Type u} → [TopologicalSpace B] →
    //   [PathConnected B] → Type u
    // ================================================================
    let universal_cover_type = {
        let mut b = EnvDeclBuilder::new();
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), b_var.clone()));
        let pc_ty = Expr::app(
            Expr::app(topology_path_connected(u_level.clone()), b_var.clone()),
            inst.clone(),
        );
        let (pc_id, _pc) = b.fresh_local(pc_ty.clone());
        let r = type_u.clone();
        let r = b.mk_pi(pc_id, BinderInfo::InstImplicit, pc_ty, r);
        let r = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), b_var.clone()),
            r,
        );
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom(
        "Topology.UniversalCover",
        vec![u.clone()],
        universal_cover_type,
    ));

    // ================================================================
    // Topology.UniversalCover.proj : {B : Type u} → [TopologicalSpace B] →
    //   [PathConnected B] → UniversalCover B → B
    // ================================================================
    let universal_cover_proj_type = {
        let mut b = EnvDeclBuilder::new();
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), b_var.clone()));
        let pc_ty = Expr::app(
            Expr::app(topology_path_connected(u_level.clone()), b_var.clone()),
            inst.clone(),
        );
        let (pc_id, pc) = b.fresh_local(pc_ty.clone());
        let uc_b = Expr::app(
            Expr::app(
                Expr::app(universal_cover(u_level.clone()), b_var.clone()),
                inst.clone(),
            ),
            pc.clone(),
        );
        let (_x_id, _x) = b.fresh_local(uc_b.clone());
        let r = b_var.clone();
        let r = b.mk_pi(_x_id, BinderInfo::Default, uc_b, r);
        let r = b.mk_pi(pc_id, BinderInfo::InstImplicit, pc_ty, r);
        let r = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), b_var.clone()),
            r,
        );
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };
    decls.push(axiom(
        "Topology.UniversalCover.proj",
        vec![u.clone()],
        universal_cover_proj_type,
    ));

    // Helper: {B : Type u} → [TopologicalSpace B] → [PathConnected B] → Prop
    // Used by is_covering, simply_connected, and universal_property
    let mk_b_topo_pc_prop = || {
        let mut b = EnvDeclBuilder::new();
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (inst_id, inst) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), b_var.clone()));
        let pc_ty = Expr::app(
            Expr::app(topology_path_connected(u_level.clone()), b_var.clone()),
            inst.clone(),
        );
        let (pc_id, _pc) = b.fresh_local(pc_ty.clone());
        let r = prop.clone();
        let r = b.mk_pi(pc_id, BinderInfo::InstImplicit, pc_ty, r);
        let r = b.mk_pi(
            inst_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), b_var.clone()),
            r,
        );
        let r = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), r);
        b.finish(r)
    };

    // ================================================================
    // Topology.UniversalCover.is_covering
    // ================================================================
    decls.push(axiom(
        "Topology.UniversalCover.is_covering",
        vec![u.clone()],
        mk_b_topo_pc_prop(),
    ));

    // ================================================================
    // Topology.UniversalCover.simply_connected
    // ================================================================
    decls.push(axiom(
        "Topology.UniversalCover.simply_connected",
        vec![u.clone()],
        mk_b_topo_pc_prop(),
    ));

    // ================================================================
    // Topology.UniversalCover.universal_property
    // ================================================================
    decls.push(axiom(
        "Topology.UniversalCover.universal_property",
        vec![u.clone()],
        mk_b_topo_pc_prop(),
    ));

    assert_eq!(decls.len(), DECL_COUNT);
    decls
}
