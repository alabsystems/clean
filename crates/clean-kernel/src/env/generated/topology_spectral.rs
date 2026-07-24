// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Generated overlay payload for `Topology.Spectral` namespace (#1444).
//!
//! Replaces 40 handwritten `add_decl` calls in `topology_algebraic2.rs`
//! `init_topology_spectral`, eliminating manual de Bruijn index arithmetic.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::types::{ConstantInfo, ConstantKind, Reducibility};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

pub(crate) const NAMESPACE: &str = "Topology.Spectral";
pub(crate) const DECL_COUNT: usize = 40;

pub(crate) const DECL_NAMES: [&str; DECL_COUNT] = [
    "Topology.Spectral.SpectralSequence",
    "Topology.Spectral.E_page",
    "Topology.Spectral.differential",
    "Topology.Spectral.d_squared_zero",
    "Topology.Spectral.page_homology",
    "Topology.Spectral.E_infty",
    "Topology.Spectral.converges_to",
    "Topology.Spectral.filtration",
    "Topology.Spectral.associated_graded",
    "Topology.Spectral.convergence_theorem",
    "Topology.Spectral.serre",
    "Topology.Spectral.serre_e2",
    "Topology.Spectral.serre_converges",
    "Topology.Spectral.atiyah_hirzebruch",
    "Topology.Spectral.ah_e2",
    "Topology.Spectral.adams",
    "Topology.Spectral.adams_e2",
    "Topology.Spectral.adams_converges",
    "Topology.Spectral.leray",
    "Topology.Spectral.leray_e2",
    "Topology.Spectral.grothendieck",
    "Topology.Spectral.grothendieck_e2",
    "Topology.Spectral.edge_horizontal",
    "Topology.Spectral.edge_vertical",
    "Topology.Spectral.transgression",
    "Topology.Spectral.is_first_quadrant",
    "Topology.Spectral.is_bounded",
    "Topology.Spectral.bounded_collapses",
    "Topology.Spectral.collapses_at",
    "Topology.Spectral.degenerates",
    "Topology.Spectral.is_multiplicative",
    "Topology.Spectral.product",
    "Topology.Spectral.leibniz",
    "Topology.Spectral.ExactCouple",
    "Topology.Spectral.derived_couple",
    "Topology.Spectral.couple_to_spectral",
    "Topology.Spectral.from_filtered_complex",
    "Topology.Spectral.filtered_converges",
    "Topology.Spectral.morphism",
    "Topology.Spectral.comparison_theorem",
];

fn axiom(name: &str, levels: Vec<Name>, type_: Expr) -> ConstantInfo {
    ConstantInfo {
        name: Name::from_string(name),
        level_params: levels,
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

    let nat_const = || Expr::const_(Name::from_string("Nat"), vec![]);
    let int_const = || Expr::const_(Name::from_string("Int"), vec![]);
    let topological_space =
        |lvl: Level| Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl]);
    let spectral_seq = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.Spectral.SpectralSequence"),
            vec![lvl],
        )
    };
    let e_page =
        |lvl: Level| Expr::const_(Name::from_string("Topology.Spectral.E_page"), vec![lvl]);
    let exact_couple = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.Spectral.ExactCouple"),
            vec![lvl],
        )
    };
    let fiber_bundle =
        |lvl: Level| Expr::const_(Name::from_string("Topology.FiberBundle"), vec![lvl]);
    let continuous = |lvl_a: Level, lvl_b: Level| {
        Expr::const_(Name::from_string("Topology.Continuous"), vec![lvl_a, lvl_b])
    };
    let ring_class = |lvl: Level| Expr::const_(Name::from_string("Ring"), vec![lvl]);
    let filtered_complex = |lvl: Level| {
        Expr::const_(
            Name::from_string("Topology.Filtration.FilteredComplex"),
            vec![lvl],
        )
    };

    let levels_u = || vec![u.clone()];

    let mut p = Vec::with_capacity(DECL_COUNT);

    // 1. SpectralSequence : Type u
    p.push(axiom(
        "Topology.Spectral.SpectralSequence",
        levels_u(),
        type_u.clone(),
    ));

    // 2. E_page : SpectralSequence → Nat → Int → Int → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (e_id, _) = b.fresh_local(spectral_seq(u_level.clone()));
        let (r_id, _) = b.fresh_local(nat_const());
        let (p_id, _) = b.fresh_local(int_const());
        let (q_id, _) = b.fresh_local(int_const());

        let e = type_u.clone();
        let e = b.mk_pi(q_id, BinderInfo::Default, int_const(), e);
        let e = b.mk_pi(p_id, BinderInfo::Default, int_const(), e);
        let e = b.mk_pi(r_id, BinderInfo::Default, nat_const(), e);
        let e = b.mk_pi(e_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        p.push(axiom("Topology.Spectral.E_page", levels_u(), b.finish(e)));
    }

    // 3. differential : (E : SS) → (r : Nat) → {p : Int} → {q : Int} →
    //    E_page E r p q → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (ss_id, ss) = b.fresh_local(spectral_seq(u_level.clone()));
        let (r_id, r) = b.fresh_local(nat_const());
        let (p_id, p_var) = b.fresh_local(int_const());
        let (q_id, q_var) = b.fresh_local(int_const());
        let e_page_app = Expr::app(
            Expr::app(Expr::app(Expr::app(e_page(u_level.clone()), ss), r), p_var),
            q_var,
        );
        let (arg_id, _) = b.fresh_local(e_page_app.clone());

        let e = type_u.clone();
        let e = b.mk_pi(arg_id, BinderInfo::Default, e_page_app, e);
        let e = b.mk_pi(q_id, BinderInfo::Implicit, int_const(), e);
        let e = b.mk_pi(p_id, BinderInfo::Implicit, int_const(), e);
        let e = b.mk_pi(r_id, BinderInfo::Default, nat_const(), e);
        let e = b.mk_pi(ss_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        p.push(axiom(
            "Topology.Spectral.differential",
            levels_u(),
            b.finish(e),
        ));
    }

    // 4. d_squared_zero : SS → Nat → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (ss_id, _) = b.fresh_local(spectral_seq(u_level.clone()));
        let (r_id, _) = b.fresh_local(nat_const());
        let e = prop.clone();
        let e = b.mk_pi(r_id, BinderInfo::Default, nat_const(), e);
        let e = b.mk_pi(ss_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        p.push(axiom(
            "Topology.Spectral.d_squared_zero",
            levels_u(),
            b.finish(e),
        ));
    }

    // 5. page_homology : SS → Nat → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (ss_id, _) = b.fresh_local(spectral_seq(u_level.clone()));
        let (r_id, _) = b.fresh_local(nat_const());
        let e = prop.clone();
        let e = b.mk_pi(r_id, BinderInfo::Default, nat_const(), e);
        let e = b.mk_pi(ss_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        p.push(axiom(
            "Topology.Spectral.page_homology",
            levels_u(),
            b.finish(e),
        ));
    }

    // 6. E_infty : SS → Int → Int → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (ss_id, _) = b.fresh_local(spectral_seq(u_level.clone()));
        let (p_id, _) = b.fresh_local(int_const());
        let (q_id, _) = b.fresh_local(int_const());
        let e = type_u.clone();
        let e = b.mk_pi(q_id, BinderInfo::Default, int_const(), e);
        let e = b.mk_pi(p_id, BinderInfo::Default, int_const(), e);
        let e = b.mk_pi(ss_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        p.push(axiom("Topology.Spectral.E_infty", levels_u(), b.finish(e)));
    }

    // 7. converges_to : SS → (Int → Type u) → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (ss_id, _) = b.fresh_local(spectral_seq(u_level.clone()));
        let target_ty = Expr::pi(BinderInfo::Default, int_const(), type_u.clone());
        let (tgt_id, _) = b.fresh_local(target_ty.clone());
        let e = prop.clone();
        let e = b.mk_pi(tgt_id, BinderInfo::Default, target_ty, e);
        let e = b.mk_pi(ss_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        p.push(axiom(
            "Topology.Spectral.converges_to",
            levels_u(),
            b.finish(e),
        ));
    }

    // 8. filtration : Type u → Type u
    p.push(axiom(
        "Topology.Spectral.filtration",
        levels_u(),
        Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone()),
    ));

    // 9. associated_graded : Type u → Int → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, _) = b.fresh_local(type_u.clone());
        let (i_id, _) = b.fresh_local(int_const());
        let e = type_u.clone();
        let e = b.mk_pi(i_id, BinderInfo::Default, int_const(), e);
        let e = b.mk_pi(x_id, BinderInfo::Default, type_u.clone(), e);
        p.push(axiom(
            "Topology.Spectral.associated_graded",
            levels_u(),
            b.finish(e),
        ));
    }

    // 10. convergence_theorem : SS → Prop
    p.push(axiom(
        "Topology.Spectral.convergence_theorem",
        levels_u(),
        Expr::pi(
            BinderInfo::Default,
            spectral_seq(u_level.clone()),
            prop.clone(),
        ),
    ));

    // 11. serre : {E B F : Type u} → [TS E] → [TS B] → [TS F] →
    //     {π : E → B} → FiberBundle E B F [TS E] [TS B] [TS F] π → SS
    {
        let mut b = EnvDeclBuilder::new();
        let (e_id, e_var) = b.fresh_local(type_u.clone());
        let (b_id, b_var) = b.fresh_local(type_u.clone());
        let (f_id, f_var) = b.fresh_local(type_u.clone());
        let ts_e_ty = Expr::app(topological_space(u_level.clone()), e_var.clone());
        let (ts_e_id, ts_e) = b.fresh_local(ts_e_ty.clone());
        let ts_b_ty = Expr::app(topological_space(u_level.clone()), b_var.clone());
        let (ts_b_id, ts_b) = b.fresh_local(ts_b_ty.clone());
        let ts_f_ty = Expr::app(topological_space(u_level.clone()), f_var.clone());
        let (ts_f_id, ts_f) = b.fresh_local(ts_f_ty.clone());
        // π : E → B
        let pi_ty = Expr::pi(BinderInfo::Default, e_var.clone(), b_var.clone());
        let (pi_id, pi_var) = b.fresh_local(pi_ty.clone());
        // FiberBundle E B F inst_E inst_B inst_F π
        let fb_app = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(Expr::app(fiber_bundle(u_level.clone()), e_var), b_var),
                            f_var,
                        ),
                        ts_e,
                    ),
                    ts_b,
                ),
                ts_f,
            ),
            pi_var,
        );
        let (fb_id, _) = b.fresh_local(fb_app.clone());

        let e = spectral_seq(u_level.clone());
        let e = b.mk_pi(fb_id, BinderInfo::Default, fb_app, e);
        let e = b.mk_pi(pi_id, BinderInfo::Implicit, pi_ty, e);
        let e = b.mk_pi(ts_f_id, BinderInfo::InstImplicit, ts_f_ty, e);
        let e = b.mk_pi(ts_b_id, BinderInfo::InstImplicit, ts_b_ty, e);
        let e = b.mk_pi(ts_e_id, BinderInfo::InstImplicit, ts_e_ty, e);
        let e = b.mk_pi(f_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), e);
        p.push(axiom("Topology.Spectral.serre", levels_u(), b.finish(e)));
    }

    // 12. serre_e2 : {E B F : Type u} → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (e_id, _) = b.fresh_local(type_u.clone());
        let (b_id, _) = b.fresh_local(type_u.clone());
        let (f_id, _) = b.fresh_local(type_u.clone());
        let e = prop.clone();
        let e = b.mk_pi(f_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), e);
        p.push(axiom("Topology.Spectral.serre_e2", levels_u(), b.finish(e)));
    }

    // 13. serre_converges : {E B F : Type u} → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (e_id, _) = b.fresh_local(type_u.clone());
        let (b_id, _) = b.fresh_local(type_u.clone());
        let (f_id, _) = b.fresh_local(type_u.clone());
        let e = prop.clone();
        let e = b.mk_pi(f_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(b_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(e_id, BinderInfo::Implicit, type_u.clone(), e);
        p.push(axiom(
            "Topology.Spectral.serre_converges",
            levels_u(),
            b.finish(e),
        ));
    }

    // 14. atiyah_hirzebruch : {X : Type u} → [TS X] → SS
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let ts_x_ty = Expr::app(topological_space(u_level.clone()), x);
        let (ts_x_id, _) = b.fresh_local(ts_x_ty.clone());
        let e = spectral_seq(u_level.clone());
        let e = b.mk_pi(ts_x_id, BinderInfo::InstImplicit, ts_x_ty, e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        p.push(axiom(
            "Topology.Spectral.atiyah_hirzebruch",
            levels_u(),
            b.finish(e),
        ));
    }

    // 15. ah_e2 : {X : Type u} → [TS X] → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let ts_x_ty = Expr::app(topological_space(u_level.clone()), x);
        let (ts_x_id, _) = b.fresh_local(ts_x_ty.clone());
        let e = prop.clone();
        let e = b.mk_pi(ts_x_id, BinderInfo::InstImplicit, ts_x_ty, e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        p.push(axiom("Topology.Spectral.ah_e2", levels_u(), b.finish(e)));
    }

    // 16. adams : {X : Type u} → [TS X] → {Y : Type u} → [TS Y] → SS
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let ts_x_ty = Expr::app(topological_space(u_level.clone()), x);
        let (ts_x_id, _) = b.fresh_local(ts_x_ty.clone());
        let (y_id, y) = b.fresh_local(type_u.clone());
        let ts_y_ty = Expr::app(topological_space(u_level.clone()), y);
        let (ts_y_id, _) = b.fresh_local(ts_y_ty.clone());
        let e = spectral_seq(u_level.clone());
        let e = b.mk_pi(ts_y_id, BinderInfo::InstImplicit, ts_y_ty, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(ts_x_id, BinderInfo::InstImplicit, ts_x_ty, e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        p.push(axiom("Topology.Spectral.adams", levels_u(), b.finish(e)));
    }

    // 17. adams_e2 : {X Y : Type u} → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, _) = b.fresh_local(type_u.clone());
        let (y_id, _) = b.fresh_local(type_u.clone());
        let e = prop.clone();
        let e = b.mk_pi(y_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        p.push(axiom("Topology.Spectral.adams_e2", levels_u(), b.finish(e)));
    }

    // 18. adams_converges : {X Y : Type u} → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, _) = b.fresh_local(type_u.clone());
        let (y_id, _) = b.fresh_local(type_u.clone());
        let e = prop.clone();
        let e = b.mk_pi(y_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        p.push(axiom(
            "Topology.Spectral.adams_converges",
            levels_u(),
            b.finish(e),
        ));
    }

    // 19. leray : {X : Type u} → [TS X] → {Y : Type u} → [TS Y] →
    //     {f : X → Y} → Continuous X Y inst_X inst_Y f → SS
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, x) = b.fresh_local(type_u.clone());
        let ts_x_ty = Expr::app(topological_space(u_level.clone()), x.clone());
        let (ts_x_id, ts_x) = b.fresh_local(ts_x_ty.clone());
        let (y_id, y) = b.fresh_local(type_u.clone());
        let ts_y_ty = Expr::app(topological_space(u_level.clone()), y.clone());
        let (ts_y_id, ts_y) = b.fresh_local(ts_y_ty.clone());
        // f : X → Y
        let f_ty = Expr::pi(BinderInfo::Default, x.clone(), y.clone());
        let (f_id, f_var) = b.fresh_local(f_ty.clone());
        // Continuous X Y inst_X inst_Y f
        let cont_app = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(continuous(u_level.clone(), u_level.clone()), x),
                        y,
                    ),
                    ts_x,
                ),
                ts_y,
            ),
            f_var,
        );
        let (cont_id, _) = b.fresh_local(cont_app.clone());

        let e = spectral_seq(u_level.clone());
        let e = b.mk_pi(cont_id, BinderInfo::Default, cont_app, e);
        let e = b.mk_pi(f_id, BinderInfo::Implicit, f_ty, e);
        let e = b.mk_pi(ts_y_id, BinderInfo::InstImplicit, ts_y_ty, e);
        let e = b.mk_pi(y_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(ts_x_id, BinderInfo::InstImplicit, ts_x_ty, e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        p.push(axiom("Topology.Spectral.leray", levels_u(), b.finish(e)));
    }

    // 20. leray_e2 : {X Y : Type u} → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (x_id, _) = b.fresh_local(type_u.clone());
        let (y_id, _) = b.fresh_local(type_u.clone());
        let e = prop.clone();
        let e = b.mk_pi(y_id, BinderInfo::Implicit, type_u.clone(), e);
        let e = b.mk_pi(x_id, BinderInfo::Implicit, type_u.clone(), e);
        p.push(axiom("Topology.Spectral.leray_e2", levels_u(), b.finish(e)));
    }

    // 21. grothendieck : SS
    p.push(axiom(
        "Topology.Spectral.grothendieck",
        levels_u(),
        spectral_seq(u_level.clone()),
    ));

    // 22. grothendieck_e2 : Prop (no level params)
    p.push(axiom(
        "Topology.Spectral.grothendieck_e2",
        vec![],
        prop.clone(),
    ));

    // 23. edge_horizontal : SS → Nat → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (ss_id, _) = b.fresh_local(spectral_seq(u_level.clone()));
        let (n_id, _) = b.fresh_local(nat_const());
        let e = type_u.clone();
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_const(), e);
        let e = b.mk_pi(ss_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        p.push(axiom(
            "Topology.Spectral.edge_horizontal",
            levels_u(),
            b.finish(e),
        ));
    }

    // 24. edge_vertical : SS → Nat → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (ss_id, _) = b.fresh_local(spectral_seq(u_level.clone()));
        let (n_id, _) = b.fresh_local(nat_const());
        let e = type_u.clone();
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_const(), e);
        let e = b.mk_pi(ss_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        p.push(axiom(
            "Topology.Spectral.edge_vertical",
            levels_u(),
            b.finish(e),
        ));
    }

    // 25. transgression : SS → Nat → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (ss_id, _) = b.fresh_local(spectral_seq(u_level.clone()));
        let (n_id, _) = b.fresh_local(nat_const());
        let e = type_u.clone();
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_const(), e);
        let e = b.mk_pi(ss_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        p.push(axiom(
            "Topology.Spectral.transgression",
            levels_u(),
            b.finish(e),
        ));
    }

    // 26-30: Simple SS → Prop predicates
    for name in &[
        "Topology.Spectral.is_first_quadrant",
        "Topology.Spectral.is_bounded",
        "Topology.Spectral.bounded_collapses",
    ] {
        p.push(axiom(
            name,
            levels_u(),
            Expr::pi(
                BinderInfo::Default,
                spectral_seq(u_level.clone()),
                prop.clone(),
            ),
        ));
    }

    // 29. collapses_at : SS → Nat → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (ss_id, _) = b.fresh_local(spectral_seq(u_level.clone()));
        let (n_id, _) = b.fresh_local(nat_const());
        let e = prop.clone();
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_const(), e);
        let e = b.mk_pi(ss_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        p.push(axiom(
            "Topology.Spectral.collapses_at",
            levels_u(),
            b.finish(e),
        ));
    }

    // 30-31: More SS → Prop predicates
    for name in &[
        "Topology.Spectral.degenerates",
        "Topology.Spectral.is_multiplicative",
    ] {
        p.push(axiom(
            name,
            levels_u(),
            Expr::pi(
                BinderInfo::Default,
                spectral_seq(u_level.clone()),
                prop.clone(),
            ),
        ));
    }

    // 32. product : SS → Nat → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (ss_id, _) = b.fresh_local(spectral_seq(u_level.clone()));
        let (n_id, _) = b.fresh_local(nat_const());
        let e = type_u.clone();
        let e = b.mk_pi(n_id, BinderInfo::Default, nat_const(), e);
        let e = b.mk_pi(ss_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        p.push(axiom("Topology.Spectral.product", levels_u(), b.finish(e)));
    }

    // 33. leibniz : SS → Prop
    p.push(axiom(
        "Topology.Spectral.leibniz",
        levels_u(),
        Expr::pi(
            BinderInfo::Default,
            spectral_seq(u_level.clone()),
            prop.clone(),
        ),
    ));

    // 34. ExactCouple : Type u
    p.push(axiom(
        "Topology.Spectral.ExactCouple",
        levels_u(),
        type_u.clone(),
    ));

    // 35. derived_couple : ExactCouple → ExactCouple
    p.push(axiom(
        "Topology.Spectral.derived_couple",
        levels_u(),
        Expr::pi(
            BinderInfo::Default,
            exact_couple(u_level.clone()),
            exact_couple(u_level.clone()),
        ),
    ));

    // 36. couple_to_spectral : ExactCouple → SS
    p.push(axiom(
        "Topology.Spectral.couple_to_spectral",
        levels_u(),
        Expr::pi(
            BinderInfo::Default,
            exact_couple(u_level.clone()),
            spectral_seq(u_level.clone()),
        ),
    ));

    // 37. from_filtered_complex : {R : Type u} → [Ring R] → FilteredComplex R [Ring R] → SS
    {
        let mut b = EnvDeclBuilder::new();
        let (r_id, r_var) = b.fresh_local(type_u.clone());
        let ring_r_ty = Expr::app(ring_class(u_level.clone()), r_var.clone());
        let (ring_id, ring_inst) = b.fresh_local(ring_r_ty.clone());
        let fc_ty = Expr::app(
            Expr::app(filtered_complex(u_level.clone()), r_var),
            ring_inst,
        );
        let (fc_id, _) = b.fresh_local(fc_ty.clone());

        let e = spectral_seq(u_level.clone());
        let e = b.mk_pi(fc_id, BinderInfo::Default, fc_ty, e);
        let e = b.mk_pi(ring_id, BinderInfo::InstImplicit, ring_r_ty, e);
        let e = b.mk_pi(r_id, BinderInfo::Implicit, type_u.clone(), e);
        p.push(axiom(
            "Topology.Spectral.from_filtered_complex",
            levels_u(),
            b.finish(e),
        ));
    }

    // 38. filtered_converges : {R : Type u} → [Ring R] → FilteredComplex R [Ring R] → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (r_id, r_var) = b.fresh_local(type_u.clone());
        let ring_r_ty = Expr::app(ring_class(u_level.clone()), r_var.clone());
        let (ring_id, ring_inst) = b.fresh_local(ring_r_ty.clone());
        let fc_ty = Expr::app(
            Expr::app(filtered_complex(u_level.clone()), r_var),
            ring_inst,
        );
        let (fc_id, _) = b.fresh_local(fc_ty.clone());

        let e = prop.clone();
        let e = b.mk_pi(fc_id, BinderInfo::Default, fc_ty, e);
        let e = b.mk_pi(ring_id, BinderInfo::InstImplicit, ring_r_ty, e);
        let e = b.mk_pi(r_id, BinderInfo::Implicit, type_u.clone(), e);
        p.push(axiom(
            "Topology.Spectral.filtered_converges",
            levels_u(),
            b.finish(e),
        ));
    }

    // 39. morphism : SS → SS → Type u
    {
        let mut b = EnvDeclBuilder::new();
        let (s1_id, _) = b.fresh_local(spectral_seq(u_level.clone()));
        let (s2_id, _) = b.fresh_local(spectral_seq(u_level.clone()));
        let e = type_u.clone();
        let e = b.mk_pi(s2_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        let e = b.mk_pi(s1_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        p.push(axiom("Topology.Spectral.morphism", levels_u(), b.finish(e)));
    }

    // 40. comparison_theorem : SS → SS → Prop
    {
        let mut b = EnvDeclBuilder::new();
        let (s1_id, _) = b.fresh_local(spectral_seq(u_level.clone()));
        let (s2_id, _) = b.fresh_local(spectral_seq(u_level.clone()));
        let e = prop.clone();
        let e = b.mk_pi(s2_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        let e = b.mk_pi(s1_id, BinderInfo::Default, spectral_seq(u_level.clone()), e);
        p.push(axiom(
            "Topology.Spectral.comparison_theorem",
            levels_u(),
            b.finish(e),
        ));
    }

    debug_assert_eq!(p.len(), DECL_COUNT, "payload size mismatch for {NAMESPACE}");
    debug_assert_eq!(
        p.iter().map(|c| c.name.to_string()).collect::<Vec<_>>(),
        DECL_NAMES.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
        "payload names mismatch for {NAMESPACE}"
    );
    p
}
