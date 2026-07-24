// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for `Topology.HomotopyEquivalence` namespace (#1444).
//!
//! Migrated from handwritten `add_decl` calls in `topology_homotopy2.rs`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.HomotopyEquivalence";
pub(crate) const DECL_COUNT: usize = 22;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.ContinuousHomotopy",
    "Topology.ContinuousHomotopy.refl",
    "Topology.ContinuousHomotopy.symm",
    "Topology.ContinuousHomotopy.trans",
    "Topology.HomotopyEquiv",
    "Topology.HomotopyEquiv.toFun",
    "Topology.HomotopyEquiv.invFun",
    "Topology.HomotopyEquiv.continuous_toFun",
    "Topology.HomotopyEquiv.continuous_invFun",
    "Topology.HomotopyEquiv.left_inv",
    "Topology.HomotopyEquiv.right_inv",
    "Topology.HomotopyEquiv.refl",
    "Topology.HomotopyEquiv.symm",
    "Topology.HomotopyEquiv.trans",
    "Topology.AreHomotopyEquiv",
    "Topology.are_homotopy_equiv_def",
    "Topology.are_homotopy_equiv_refl",
    "Topology.are_homotopy_equiv_symm",
    "Topology.are_homotopy_equiv_trans",
    "Topology.homeomorphism_to_homotopy_equiv",
    "Topology.contractible_are_homotopy_equiv",
    "Topology.homotopy_equiv_preserves_path_connected",
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
    let homeomorphism = |lvl1: Level, lvl2: Level| {
        Expr::const_(
            Name::from_string("Topology.Homeomorphism"),
            vec![lvl1, lvl2],
        )
    };
    let contractible =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Contractible"), vec![lvl]);
    let path_connected =
        |lvl: Level| Expr::const_(Name::from_string("Topology.PathConnected"), vec![lvl]);
    let nonempty_const = |lvl: Level| Expr::const_(Name::from_string("Nonempty"), vec![lvl]);
    let iff_const = || Expr::const_(Name::from_string("Iff"), vec![]);
    let continuous_homotopy =
        |lvl: Level| Expr::const_(Name::from_string("Topology.ContinuousHomotopy"), vec![lvl]);
    let homotopy_equiv =
        |lvl: Level| Expr::const_(Name::from_string("Topology.HomotopyEquiv"), vec![lvl]);
    let he_to_fun =
        |lvl: Level| Expr::const_(Name::from_string("Topology.HomotopyEquiv.toFun"), vec![lvl]);
    let he_inv_fun = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.HomotopyEquiv.invFun"),
            vec![lvl],
        )
    };
    let are_homotopy_equiv =
        |lvl: Level| Expr::const_(Name::from_string("Topology.AreHomotopyEquiv"), vec![lvl]);

    let mut decls = Vec::with_capacity(DECL_COUNT);

    // ================================================================
    // 1. Topology.ContinuousHomotopy : {α β : Type u} → [TopologicalSpace α] →
    //    [TopologicalSpace β] → (α → β) → (α → β) → Type u
    // ================================================================
    let continuous_homotopy_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, _inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, _inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));
        let ab = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, _f) = b.fresh_local(ab.clone());
        let (g_id, _g) = b.fresh_local(ab.clone());

        let e = type_u.clone();
        let e = b.mk_pi(g_id, BinderInfo::Default, ab.clone(), e);
        let e = b.mk_pi(f_id, BinderInfo::Default, ab, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.ContinuousHomotopy",
        vec![u.clone()],
        continuous_homotopy_type,
    ));

    // ================================================================
    // 2. Topology.ContinuousHomotopy.refl : {α β : Type u} → [TopologicalSpace α] →
    //    [TopologicalSpace β] → (f : α → β) → Continuous f → ContinuousHomotopy f f
    // ================================================================
    let ch_refl_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));
        let ab = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, f) = b.fresh_local(ab.clone());
        let cont_f = Expr::apps(
            continuous(u_level.clone(), u_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                f.clone(),
            ],
        );
        let (hc_id, _hc) = b.fresh_local(cont_f.clone());
        let ch_f_f = Expr::apps(
            continuous_homotopy(u_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                f.clone(),
                f.clone(),
            ],
        );

        let e = ch_f_f;
        let e = b.mk_pi(hc_id, BinderInfo::Default, cont_f, e);
        let e = b.mk_pi(f_id, BinderInfo::Default, ab, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.ContinuousHomotopy.refl",
        vec![u.clone()],
        ch_refl_type,
    ));

    // ================================================================
    // 3. Topology.ContinuousHomotopy.symm : {α β : Type u} → [TopologicalSpace α] →
    //    [TopologicalSpace β] → {f g : α → β} → ContinuousHomotopy f g → ContinuousHomotopy g f
    // ================================================================
    let ch_symm_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));
        let ab = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, f) = b.fresh_local(ab.clone());
        let (g_id, g) = b.fresh_local(ab.clone());
        let ch_fg = Expr::apps(
            continuous_homotopy(u_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                f.clone(),
                g.clone(),
            ],
        );
        let (h_id, _h) = b.fresh_local(ch_fg.clone());
        let ch_gf = Expr::apps(
            continuous_homotopy(u_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                g.clone(),
                f.clone(),
            ],
        );

        let e = ch_gf;
        let e = b.mk_pi(h_id, BinderInfo::Default, ch_fg, e);
        let e = b.mk_pi(g_id, BinderInfo::Implicit, ab.clone(), e);
        let e = b.mk_pi(f_id, BinderInfo::Implicit, ab, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.ContinuousHomotopy.symm",
        vec![u.clone()],
        ch_symm_type,
    ));

    // ================================================================
    // 4. Topology.ContinuousHomotopy.trans : {α β : Type u} → [TopologicalSpace α] →
    //    [TopologicalSpace β] → {f g h : α → β} → ContinuousHomotopy f g →
    //    ContinuousHomotopy g h → ContinuousHomotopy f h
    // ================================================================
    let ch_trans_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));
        let ab = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, f) = b.fresh_local(ab.clone());
        let (g_id, g) = b.fresh_local(ab.clone());
        let (hv_id, hv) = b.fresh_local(ab.clone());
        let ch_fg = Expr::apps(
            continuous_homotopy(u_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                f.clone(),
                g.clone(),
            ],
        );
        let (h1_id, _h1) = b.fresh_local(ch_fg.clone());
        let ch_gh = Expr::apps(
            continuous_homotopy(u_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                g.clone(),
                hv.clone(),
            ],
        );
        let (h2_id, _h2) = b.fresh_local(ch_gh.clone());
        let ch_fh = Expr::apps(
            continuous_homotopy(u_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                f.clone(),
                hv.clone(),
            ],
        );

        let e = ch_fh;
        let e = b.mk_pi(h2_id, BinderInfo::Default, ch_gh, e);
        let e = b.mk_pi(h1_id, BinderInfo::Default, ch_fg, e);
        let e = b.mk_pi(hv_id, BinderInfo::Implicit, ab.clone(), e);
        let e = b.mk_pi(g_id, BinderInfo::Implicit, ab.clone(), e);
        let e = b.mk_pi(f_id, BinderInfo::Implicit, ab, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.ContinuousHomotopy.trans",
        vec![u.clone()],
        ch_trans_type,
    ));

    // ================================================================
    // 5. Topology.HomotopyEquiv : {α β : Type u} → [TopologicalSpace α] →
    //    [TopologicalSpace β] → Type u
    // ================================================================
    let homotopy_equiv_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, _inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, _inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));

        let e = type_u.clone();
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.HomotopyEquiv",
        vec![u.clone()],
        homotopy_equiv_type,
    ));

    // ================================================================
    // 6. Topology.HomotopyEquiv.toFun : {α β : Type u} → [TopologicalSpace α] →
    //    [TopologicalSpace β] → HomotopyEquiv α β → (α → β)
    // ================================================================
    let to_fun_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));
        let he_ab = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );
        let (ev_id, _ev) = b.fresh_local(he_ab.clone());
        let ab = Expr::arrow(alpha.clone(), beta.clone());

        let e = ab;
        let e = b.mk_pi(ev_id, BinderInfo::Default, he_ab, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.HomotopyEquiv.toFun",
        vec![u.clone()],
        to_fun_type,
    ));

    // ================================================================
    // 7. Topology.HomotopyEquiv.invFun : {α β : Type u} → [TopologicalSpace α] →
    //    [TopologicalSpace β] → HomotopyEquiv α β → (β → α)
    // ================================================================
    let inv_fun_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));
        let he_ab = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );
        let (ev_id, _ev) = b.fresh_local(he_ab.clone());
        let ba = Expr::arrow(beta.clone(), alpha.clone());

        let e = ba;
        let e = b.mk_pi(ev_id, BinderInfo::Default, he_ab, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.HomotopyEquiv.invFun",
        vec![u.clone()],
        inv_fun_type,
    ));

    // ================================================================
    // 8. Topology.HomotopyEquiv.continuous_toFun : {α β : Type u} → [TopologicalSpace α] →
    //    [TopologicalSpace β] → (e : HomotopyEquiv α β) → Continuous (toFun e)
    // ================================================================
    let continuous_to_fun_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));
        let he_ab = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );
        let (ev_id, ev) = b.fresh_local(he_ab.clone());

        // toFun e : α → β
        let to_fun_e = Expr::apps(
            he_to_fun(u_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                ev.clone(),
            ],
        );

        // Continuous (toFun e)
        let cont_to_fun = Expr::apps(
            continuous(u_level.clone(), u_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                to_fun_e,
            ],
        );

        let e = cont_to_fun;
        let e = b.mk_pi(ev_id, BinderInfo::Default, he_ab, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.HomotopyEquiv.continuous_toFun",
        vec![u.clone()],
        continuous_to_fun_type,
    ));

    // ================================================================
    // 9. Topology.HomotopyEquiv.continuous_invFun : {α β : Type u} → [TopologicalSpace α] →
    //    [TopologicalSpace β] → (e : HomotopyEquiv α β) → Continuous (invFun e)
    // ================================================================
    let continuous_inv_fun_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));
        let he_ab = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );
        let (ev_id, ev) = b.fresh_local(he_ab.clone());

        // invFun e : β → α
        let inv_fun_e = Expr::apps(
            he_inv_fun(u_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                ev.clone(),
            ],
        );

        // Continuous (invFun e) - note: β → α, so Continuous β α inst_β inst_α
        let cont_inv_fun = Expr::apps(
            continuous(u_level.clone(), u_level.clone()),
            [
                beta.clone(),
                alpha.clone(),
                inst_b.clone(),
                inst_a.clone(),
                inv_fun_e,
            ],
        );

        let e = cont_inv_fun;
        let e = b.mk_pi(ev_id, BinderInfo::Default, he_ab, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.HomotopyEquiv.continuous_invFun",
        vec![u.clone()],
        continuous_inv_fun_type,
    ));

    // ================================================================
    // 10. Topology.HomotopyEquiv.left_inv : {α β : Type u} → [TopologicalSpace α] →
    //     [TopologicalSpace β] → (e : HomotopyEquiv α β) → Prop
    //
    //     Simplified: the composition invFun . toFun is homotopic to identity
    // ================================================================
    let left_inv_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));
        let he_ab = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );
        let (ev_id, _ev) = b.fresh_local(he_ab.clone());

        // Simplified to Prop
        let e = prop.clone();
        let e = b.mk_pi(ev_id, BinderInfo::Default, he_ab, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.HomotopyEquiv.left_inv",
        vec![u.clone()],
        left_inv_type,
    ));

    // ================================================================
    // 11. Topology.HomotopyEquiv.right_inv : {α β : Type u} → [TopologicalSpace α] →
    //     [TopologicalSpace β] → (e : HomotopyEquiv α β) → Prop
    //
    //     Simplified: the composition toFun . invFun is homotopic to identity
    // ================================================================
    let right_inv_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));
        let he_ab = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );
        let (ev_id, _ev) = b.fresh_local(he_ab.clone());

        // Simplified to Prop
        let e = prop.clone();
        let e = b.mk_pi(ev_id, BinderInfo::Default, he_ab, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.HomotopyEquiv.right_inv",
        vec![u.clone()],
        right_inv_type,
    ));

    // ================================================================
    // 12. Topology.HomotopyEquiv.refl : {α : Type u} → [TopologicalSpace α] →
    //     HomotopyEquiv α α
    // ================================================================
    let he_refl_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));

        // HomotopyEquiv α α
        let he_aa = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [alpha.clone(), alpha.clone(), inst_a.clone(), inst_a.clone()],
        );

        let e = he_aa;
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.HomotopyEquiv.refl",
        vec![u.clone()],
        he_refl_type,
    ));

    // ================================================================
    // 13. Topology.HomotopyEquiv.symm : {α β : Type u} → [TopologicalSpace α] →
    //     [TopologicalSpace β] → HomotopyEquiv α β → HomotopyEquiv β α
    // ================================================================
    let he_symm_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));
        let he_ab = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );
        let (ev_id, _ev) = b.fresh_local(he_ab.clone());

        // HomotopyEquiv β α
        let he_ba = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [beta.clone(), alpha.clone(), inst_b.clone(), inst_a.clone()],
        );

        let e = he_ba;
        let e = b.mk_pi(ev_id, BinderInfo::Default, he_ab, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.HomotopyEquiv.symm",
        vec![u.clone()],
        he_symm_type,
    ));

    // ================================================================
    // 14. Topology.HomotopyEquiv.trans : {α β γ : Type u} → [TopologicalSpace α] →
    //     [TopologicalSpace β] → [TopologicalSpace γ] →
    //     HomotopyEquiv α β → HomotopyEquiv β γ → HomotopyEquiv α γ
    // ================================================================
    let he_trans_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (gamma_id, gamma) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));
        let (inst_g_id, inst_g) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), gamma.clone()));

        // HomotopyEquiv α β
        let he_ab = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );
        let (e1_id, _e1) = b.fresh_local(he_ab.clone());

        // HomotopyEquiv β γ
        let he_bg = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [beta.clone(), gamma.clone(), inst_b.clone(), inst_g.clone()],
        );
        let (e2_id, _e2) = b.fresh_local(he_bg.clone());

        // HomotopyEquiv α γ (result)
        let he_ag = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [alpha.clone(), gamma.clone(), inst_a.clone(), inst_g.clone()],
        );

        let e = he_ag;
        let e = b.mk_pi(e2_id, BinderInfo::Default, he_bg, e);
        let e = b.mk_pi(e1_id, BinderInfo::Default, he_ab, e);
        let e = b.mk_pi(
            inst_g_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), gamma.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(gamma_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.HomotopyEquiv.trans",
        vec![u.clone()],
        he_trans_type,
    ));

    // ================================================================
    // 15. Topology.AreHomotopyEquiv : {α β : Type u} → [TopologicalSpace α] →
    //     [TopologicalSpace β] → Prop
    // ================================================================
    let are_he_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, _inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, _inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));

        let e = prop.clone();
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.AreHomotopyEquiv",
        vec![u.clone()],
        are_he_type,
    ));

    // ================================================================
    // 16. Topology.are_homotopy_equiv_def : {α β : Type u} → [TopologicalSpace α] →
    //     [TopologicalSpace β] → Iff (AreHomotopyEquiv α β) (Nonempty (HomotopyEquiv α β))
    // ================================================================
    let are_he_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));

        // AreHomotopyEquiv α β
        let are_he_ab_local = Expr::apps(
            are_homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );

        // HomotopyEquiv α β
        let he_ab = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );

        // Nonempty (HomotopyEquiv α β) -- HomotopyEquiv : Type u, Nonempty needs u+1
        let nonempty_he_ab = Expr::app(nonempty_const(Level::succ(u_level.clone())), he_ab);

        // Iff (AreHomotopyEquiv α β) (Nonempty (HomotopyEquiv α β))
        let iff_body = Expr::app(Expr::app(iff_const(), are_he_ab_local), nonempty_he_ab);

        let e = iff_body;
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.are_homotopy_equiv_def",
        vec![u.clone()],
        are_he_def_type,
    ));

    // ================================================================
    // 17. Topology.are_homotopy_equiv_refl : {α : Type u} → [TopologicalSpace α] →
    //     AreHomotopyEquiv α α
    // ================================================================
    let are_he_refl_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));

        // AreHomotopyEquiv α α
        let are_he_aa = Expr::apps(
            are_homotopy_equiv(u_level.clone()),
            [alpha.clone(), alpha.clone(), inst_a.clone(), inst_a.clone()],
        );

        let e = are_he_aa;
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.are_homotopy_equiv_refl",
        vec![u.clone()],
        are_he_refl_type,
    ));

    // ================================================================
    // 18. Topology.are_homotopy_equiv_symm : {α β : Type u} → [TopologicalSpace α] →
    //     [TopologicalSpace β] → AreHomotopyEquiv α β → AreHomotopyEquiv β α
    // ================================================================
    let are_he_symm_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));

        // AreHomotopyEquiv α β
        let are_he_ab_local = Expr::apps(
            are_homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );
        let (h_id, _h) = b.fresh_local(are_he_ab_local.clone());

        // AreHomotopyEquiv β α
        let are_he_ba = Expr::apps(
            are_homotopy_equiv(u_level.clone()),
            [beta.clone(), alpha.clone(), inst_b.clone(), inst_a.clone()],
        );

        let e = are_he_ba;
        let e = b.mk_pi(h_id, BinderInfo::Default, are_he_ab_local, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.are_homotopy_equiv_symm",
        vec![u.clone()],
        are_he_symm_type,
    ));

    // ================================================================
    // 19. Topology.are_homotopy_equiv_trans : {α β γ : Type u} → [TopologicalSpace α] →
    //     [TopologicalSpace β] → [TopologicalSpace γ] →
    //     AreHomotopyEquiv α β → AreHomotopyEquiv β γ → AreHomotopyEquiv α γ
    // ================================================================
    let are_he_trans_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (gamma_id, gamma) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));
        let (inst_g_id, inst_g) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), gamma.clone()));

        // AreHomotopyEquiv α β
        let are_he_ab_local = Expr::apps(
            are_homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );
        let (h1_id, _h1) = b.fresh_local(are_he_ab_local.clone());

        // AreHomotopyEquiv β γ
        let are_he_bg = Expr::apps(
            are_homotopy_equiv(u_level.clone()),
            [beta.clone(), gamma.clone(), inst_b.clone(), inst_g.clone()],
        );
        let (h2_id, _h2) = b.fresh_local(are_he_bg.clone());

        // AreHomotopyEquiv α γ
        let are_he_ag = Expr::apps(
            are_homotopy_equiv(u_level.clone()),
            [alpha.clone(), gamma.clone(), inst_a.clone(), inst_g.clone()],
        );

        let e = are_he_ag;
        let e = b.mk_pi(h2_id, BinderInfo::Default, are_he_bg, e);
        let e = b.mk_pi(h1_id, BinderInfo::Default, are_he_ab_local, e);
        let e = b.mk_pi(
            inst_g_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), gamma.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(gamma_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.are_homotopy_equiv_trans",
        vec![u.clone()],
        are_he_trans_type,
    ));

    // ================================================================
    // 20. Topology.homeomorphism_to_homotopy_equiv : {α β : Type u} →
    //     [TopologicalSpace α] → [TopologicalSpace β] →
    //     (f : α → β) → (g : β → α) → Homeomorphism α β f g → HomotopyEquiv α β
    // ================================================================
    let homeo_to_he_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));
        let f_ty = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let g_ty = Expr::arrow(beta.clone(), alpha.clone());
        let (g_id, g) = b.fresh_local(g_ty.clone());

        // Homeomorphism.{u,u} α β inst_a inst_b f g : Prop
        let homeo_fg = Expr::apps(
            homeomorphism(u_level.clone(), u_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_a.clone(),
                inst_b.clone(),
                f.clone(),
                g.clone(),
            ],
        );
        let (h_id, _h) = b.fresh_local(homeo_fg.clone());

        // HomotopyEquiv.{u} α β inst_a inst_b
        let he_ab = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );

        // Close binders innermost first
        let e = b.mk_pi(h_id, BinderInfo::Default, homeo_fg, he_ab);
        let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, e);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.homeomorphism_to_homotopy_equiv",
        vec![u.clone()],
        homeo_to_he_type,
    ));

    // ================================================================
    // 21. Topology.contractible_are_homotopy_equiv : {α β : Type u} →
    //     [TopologicalSpace α] → [TopologicalSpace β] →
    //     Contractible α → Contractible β → AreHomotopyEquiv α β
    // ================================================================
    let contr_are_he_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));

        // Contractible α
        let contr_a = Expr::apps(
            contractible(u_level.clone()),
            [alpha.clone(), inst_a.clone()],
        );
        let (ha_id, _ha) = b.fresh_local(contr_a.clone());

        // Contractible β
        let contr_b = Expr::apps(
            contractible(u_level.clone()),
            [beta.clone(), inst_b.clone()],
        );
        let (hb_id, _hb) = b.fresh_local(contr_b.clone());

        // AreHomotopyEquiv α β
        let are_he_ab_result = Expr::apps(
            are_homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );

        let e = are_he_ab_result;
        let e = b.mk_pi(hb_id, BinderInfo::Default, contr_b, e);
        let e = b.mk_pi(ha_id, BinderInfo::Default, contr_a, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.contractible_are_homotopy_equiv",
        vec![u.clone()],
        contr_are_he_type,
    ));

    // ================================================================
    // 22. Topology.homotopy_equiv_preserves_path_connected : {α β : Type u} →
    //     [TopologicalSpace α] → [TopologicalSpace β] →
    //     HomotopyEquiv α β → PathConnected α → PathConnected β
    // ================================================================
    let he_preserves_pc_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_u.clone());
        let (inst_a_id, inst_a) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_b_id, inst_b) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), beta.clone()));

        // HomotopyEquiv α β
        let he_ab = Expr::apps(
            homotopy_equiv(u_level.clone()),
            [alpha.clone(), beta.clone(), inst_a.clone(), inst_b.clone()],
        );
        let (ev_id, _ev) = b.fresh_local(he_ab.clone());

        // PathConnected α
        let pc_a = Expr::apps(
            path_connected(u_level.clone()),
            [alpha.clone(), inst_a.clone()],
        );
        let (h_id, _h) = b.fresh_local(pc_a.clone());

        // PathConnected β
        let pc_b = Expr::apps(
            path_connected(u_level.clone()),
            [beta.clone(), inst_b.clone()],
        );

        let e = pc_b;
        let e = b.mk_pi(h_id, BinderInfo::Default, pc_a, e);
        let e = b.mk_pi(ev_id, BinderInfo::Default, he_ab, e);
        let e = b.mk_pi(
            inst_b_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_a_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };
    decls.push(axiom(
        "Topology.homotopy_equiv_preserves_path_connected",
        vec![u.clone()],
        he_preserves_pc_type,
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
