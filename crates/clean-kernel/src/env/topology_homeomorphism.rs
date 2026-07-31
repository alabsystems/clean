// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Homeomorphisms between topological spaces

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Build Topology.Homeomorphism declaration templates as a pure function.
///
/// Returns declarations in registration order. Conditional declarations are
/// controlled by boolean parameters:
/// - `include_connected`: adds `Topology.homeomorphism_connected` (requires Connected init)
/// - `include_compact`: adds `Topology.homeomorphism_compact` (requires Compact init)
///
/// This is a pure function with no side effects. Both the production init function
/// and the test harness can call it to get the same declaration list.
pub(crate) fn topology_homeomorphism_decl_templates(
    include_connected: bool,
    include_compact: bool,
) -> Vec<Declaration> {
    let mut decls = Vec::new();

    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let w = Name::from_string("w");
    let u_level = Level::param(u.clone());
    let v_level = Level::param(v.clone());
    let w_level = Level::param(w.clone());
    let type_u = Expr::sort(Level::succ(u_level.clone())); // Type u = Sort (u+1)
    let type_v = Expr::sort(Level::succ(v_level.clone())); // Type v = Sort (v+1)
    let type_w = Expr::sort(Level::succ(w_level.clone())); // Type w = Sort (w+1)
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let topological_space =
        |lvl: Level| Expr::const_(Name::from_string("TopologicalSpace"), vec![lvl]);
    let topology_continuous_const = |dom: Level, cod: Level| {
        Expr::const_(Name::from_string("Topology.Continuous"), vec![dom, cod])
    };
    let and_const = Expr::const_(Name::from_string("And"), vec![]);
    let iff_const = Expr::const_(Name::from_string("Iff"), vec![]);
    let eq_const_u = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_level.clone())]);
    let eq_const_v = Expr::const_(Name::from_string("Eq"), vec![Level::succ(v_level.clone())]);

    let homeomorphism = |dom: Level, cod: Level| {
        Expr::const_(Name::from_string("Topology.Homeomorphism"), vec![dom, cod])
    };

    // ================================================================
    // Topology.Homeomorphism
    // ================================================================
    let homeomorphism_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let (inst_alpha_id, _inst_alpha) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_beta_id, _inst_beta) =
            b.fresh_local(Expr::app(topological_space(v_level.clone()), beta.clone()));
        let f_ty = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, _f) = b.fresh_local(f_ty.clone());
        let g_ty = Expr::arrow(beta.clone(), alpha.clone());
        let (g_id, _g) = b.fresh_local(g_ty.clone());

        let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, prop.clone());
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
        let e = b.mk_pi(
            inst_beta_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(v_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_alpha_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.Homeomorphism"),
        level_params: vec![u.clone(), v.clone()],
        type_: homeomorphism_type,
    });

    // ================================================================
    // Topology.homeomorphism_def
    // ================================================================
    let homeomorphism_def_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let (inst_alpha_id, inst_alpha) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_beta_id, inst_beta) =
            b.fresh_local(Expr::app(topological_space(v_level.clone()), beta.clone()));
        let f_ty = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let g_ty = Expr::arrow(beta.clone(), alpha.clone());
        let (g_id, g) = b.fresh_local(g_ty.clone());

        let homeo_fg = Expr::apps(
            homeomorphism(u_level.clone(), v_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_alpha.clone(),
                inst_beta.clone(),
                f.clone(),
                g.clone(),
            ],
        );

        let continuous_f = Expr::apps(
            topology_continuous_const(u_level.clone(), v_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_alpha.clone(),
                inst_beta.clone(),
                f.clone(),
            ],
        );

        let continuous_g = Expr::apps(
            topology_continuous_const(v_level.clone(), u_level.clone()),
            [
                beta.clone(),
                alpha.clone(),
                inst_beta.clone(),
                inst_alpha.clone(),
                g.clone(),
            ],
        );

        let left_inv = {
            let mut sub = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = sub.fresh_local(alpha.clone());
            let gf_x = Expr::app(g.clone(), Expr::app(f.clone(), x.clone()));
            let eq_gf_x = Expr::apps(eq_const_u.clone(), [alpha.clone(), gf_x, x.clone()]);
            sub.mk_pi(x_id, BinderInfo::Default, alpha.clone(), eq_gf_x)
        };

        let right_inv = {
            let mut sub = EnvDeclBuilder::child_of(&b);
            let (y_id, y) = sub.fresh_local(beta.clone());
            let fg_y = Expr::app(f.clone(), Expr::app(g.clone(), y.clone()));
            let eq_fg_y = Expr::apps(eq_const_v.clone(), [beta.clone(), fg_y, y.clone()]);
            sub.mk_pi(y_id, BinderInfo::Default, beta.clone(), eq_fg_y)
        };

        let and_continuous = Expr::app(Expr::app(and_const.clone(), continuous_f), continuous_g);
        let and_left_inv = Expr::app(Expr::app(and_const.clone(), and_continuous), left_inv);
        let and_full = Expr::app(Expr::app(and_const.clone(), and_left_inv), right_inv);
        let homeo_def_iff = Expr::app(Expr::app(iff_const.clone(), homeo_fg), and_full);

        let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, homeo_def_iff);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
        let e = b.mk_pi(
            inst_beta_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(v_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_alpha_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.homeomorphism_def"),
        level_params: vec![u.clone(), v.clone()],
        type_: homeomorphism_def_type,
    });

    // ================================================================
    // Topology.homeomorphism_id
    // ================================================================
    let homeomorphism_id_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (inst_alpha_id, inst_alpha) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));

        let id_fn = {
            let mut sub = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = sub.fresh_local(alpha.clone());
            sub.mk_lam(x_id, BinderInfo::Default, alpha.clone(), x)
        };

        let result = Expr::apps(
            homeomorphism(u_level.clone(), u_level.clone()),
            [
                alpha.clone(),
                alpha.clone(),
                inst_alpha.clone(),
                inst_alpha.clone(),
                id_fn.clone(),
                id_fn,
            ],
        );

        let e = b.mk_pi(
            inst_alpha_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            result,
        );
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.homeomorphism_id"),
        level_params: vec![u.clone()],
        type_: homeomorphism_id_type,
    });

    // ================================================================
    // Topology.homeomorphism_symm
    // ================================================================
    let homeomorphism_symm_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let (inst_alpha_id, inst_alpha) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_beta_id, inst_beta) =
            b.fresh_local(Expr::app(topological_space(v_level.clone()), beta.clone()));
        let f_ty = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let g_ty = Expr::arrow(beta.clone(), alpha.clone());
        let (g_id, g) = b.fresh_local(g_ty.clone());

        let homeo_fg = Expr::apps(
            homeomorphism(u_level.clone(), v_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_alpha.clone(),
                inst_beta.clone(),
                f.clone(),
                g.clone(),
            ],
        );

        let homeo_gf = Expr::apps(
            homeomorphism(v_level.clone(), u_level.clone()),
            [
                beta.clone(),
                alpha.clone(),
                inst_beta.clone(),
                inst_alpha.clone(),
                g.clone(),
                f.clone(),
            ],
        );
        let (hfg_id, _hfg) = b.fresh_local(homeo_fg.clone());

        let e = b.mk_pi(hfg_id, BinderInfo::Default, homeo_fg, homeo_gf);
        let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, e);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
        let e = b.mk_pi(
            inst_beta_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(v_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_alpha_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.homeomorphism_symm"),
        level_params: vec![u.clone(), v.clone()],
        type_: homeomorphism_symm_type,
    });

    // ================================================================
    // Topology.homeomorphism_comp
    // ================================================================
    let homeomorphism_comp_type = {
        let mut b = EnvDeclBuilder::new();
        let (alpha_id, alpha) = b.fresh_local(type_u.clone());
        let (beta_id, beta) = b.fresh_local(type_v.clone());
        let (gamma_id, gamma) = b.fresh_local(type_w.clone());
        let (inst_alpha_id, inst_alpha) =
            b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
        let (inst_beta_id, inst_beta) =
            b.fresh_local(Expr::app(topological_space(v_level.clone()), beta.clone()));
        let (inst_gamma_id, inst_gamma) =
            b.fresh_local(Expr::app(topological_space(w_level.clone()), gamma.clone()));
        let f_ty = Expr::arrow(alpha.clone(), beta.clone());
        let (f_id, f) = b.fresh_local(f_ty.clone());
        let g_ty = Expr::arrow(beta.clone(), alpha.clone());
        let (g_id, g) = b.fresh_local(g_ty.clone());
        let f2_ty = Expr::arrow(beta.clone(), gamma.clone());
        let (f2_id, f2) = b.fresh_local(f2_ty.clone());
        let g2_ty = Expr::arrow(gamma.clone(), beta.clone());
        let (g2_id, g2) = b.fresh_local(g2_ty.clone());

        let homeo_fg = Expr::apps(
            homeomorphism(u_level.clone(), v_level.clone()),
            [
                alpha.clone(),
                beta.clone(),
                inst_alpha.clone(),
                inst_beta.clone(),
                f.clone(),
                g.clone(),
            ],
        );

        let homeo_f2g2 = Expr::apps(
            homeomorphism(v_level.clone(), w_level.clone()),
            [
                beta.clone(),
                gamma.clone(),
                inst_beta.clone(),
                inst_gamma.clone(),
                f2.clone(),
                g2.clone(),
            ],
        );

        let comp_forward = {
            let mut sub = EnvDeclBuilder::child_of(&b);
            let (x_id, x) = sub.fresh_local(alpha.clone());
            let f2_fx = Expr::app(f2.clone(), Expr::app(f.clone(), x.clone()));
            sub.mk_lam(x_id, BinderInfo::Default, alpha.clone(), f2_fx)
        };

        let comp_inverse = {
            let mut sub = EnvDeclBuilder::child_of(&b);
            let (z_id, z) = sub.fresh_local(gamma.clone());
            let g_g2z = Expr::app(g.clone(), Expr::app(g2.clone(), z.clone()));
            sub.mk_lam(z_id, BinderInfo::Default, gamma.clone(), g_g2z)
        };

        let homeo_comp = Expr::apps(
            homeomorphism(u_level.clone(), w_level.clone()),
            [
                alpha.clone(),
                gamma.clone(),
                inst_alpha.clone(),
                inst_gamma.clone(),
                comp_forward,
                comp_inverse,
            ],
        );

        let (hfg_id, _hfg) = b.fresh_local(homeo_fg.clone());
        let (hf2g2_id, _hf2g2) = b.fresh_local(homeo_f2g2.clone());

        let e = b.mk_pi(hf2g2_id, BinderInfo::Default, homeo_f2g2, homeo_comp);
        let e = b.mk_pi(hfg_id, BinderInfo::Default, homeo_fg, e);
        let e = b.mk_pi(g2_id, BinderInfo::Default, g2_ty, e);
        let e = b.mk_pi(f2_id, BinderInfo::Default, f2_ty, e);
        let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, e);
        let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
        let e = b.mk_pi(
            inst_gamma_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(w_level.clone()), gamma.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_beta_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(v_level.clone()), beta.clone()),
            e,
        );
        let e = b.mk_pi(
            inst_alpha_id,
            BinderInfo::InstImplicit,
            Expr::app(topological_space(u_level.clone()), alpha.clone()),
            e,
        );
        let e = b.mk_pi(gamma_id, BinderInfo::Implicit, type_w.clone(), e);
        let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
        let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
        b.finish(e)
    };

    decls.push(Declaration::Axiom {
        name: Name::from_string("Topology.homeomorphism_comp"),
        level_params: vec![u.clone(), v.clone(), w.clone()],
        type_: homeomorphism_comp_type,
    });

    // ================================================================
    // Topology.homeomorphism_connected (conditional)
    // ================================================================
    if include_connected {
        let topology_connected =
            |lvl: Level| Expr::const_(Name::from_string("Topology.Connected"), vec![lvl]);
        let homeomorphism_connected_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let (inst_alpha_id, inst_alpha) =
                b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
            let (inst_beta_id, inst_beta) =
                b.fresh_local(Expr::app(topological_space(v_level.clone()), beta.clone()));
            let f_ty = Expr::arrow(alpha.clone(), beta.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let g_ty = Expr::arrow(beta.clone(), alpha.clone());
            let (g_id, g) = b.fresh_local(g_ty.clone());

            let homeo_fg = Expr::apps(
                homeomorphism(u_level.clone(), v_level.clone()),
                [
                    alpha.clone(),
                    beta.clone(),
                    inst_alpha.clone(),
                    inst_beta.clone(),
                    f.clone(),
                    g.clone(),
                ],
            );
            let (hfg_id, _hfg) = b.fresh_local(homeo_fg.clone());

            let connected_alpha = Expr::app(
                Expr::app(topology_connected(u_level.clone()), alpha.clone()),
                inst_alpha.clone(),
            );
            let (hc_id, _hc) = b.fresh_local(connected_alpha.clone());

            let connected_beta = Expr::app(
                Expr::app(topology_connected(v_level.clone()), beta.clone()),
                inst_beta.clone(),
            );

            let e = b.mk_pi(hc_id, BinderInfo::Default, connected_alpha, connected_beta);
            let e = b.mk_pi(hfg_id, BinderInfo::Default, homeo_fg, e);
            let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, e);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_pi(
                inst_beta_id,
                BinderInfo::InstImplicit,
                Expr::app(topological_space(v_level.clone()), beta.clone()),
                e,
            );
            let e = b.mk_pi(
                inst_alpha_id,
                BinderInfo::InstImplicit,
                Expr::app(topological_space(u_level.clone()), alpha.clone()),
                e,
            );
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        decls.push(Declaration::Axiom {
            name: Name::from_string("Topology.homeomorphism_connected"),
            level_params: vec![u.clone(), v.clone()],
            type_: homeomorphism_connected_type,
        });
    }

    // ================================================================
    // Topology.homeomorphism_compact (conditional)
    // ================================================================
    if include_compact {
        let topology_compact =
            |lvl: Level| Expr::const_(Name::from_string("Topology.Compact"), vec![lvl]);
        let homeomorphism_compact_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let (inst_alpha_id, inst_alpha) =
                b.fresh_local(Expr::app(topological_space(u_level.clone()), alpha.clone()));
            let (inst_beta_id, inst_beta) =
                b.fresh_local(Expr::app(topological_space(v_level.clone()), beta.clone()));
            let f_ty = Expr::arrow(alpha.clone(), beta.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let g_ty = Expr::arrow(beta.clone(), alpha.clone());
            let (g_id, g) = b.fresh_local(g_ty.clone());

            let homeo_fg = Expr::apps(
                homeomorphism(u_level.clone(), v_level.clone()),
                [
                    alpha.clone(),
                    beta.clone(),
                    inst_alpha.clone(),
                    inst_beta.clone(),
                    f.clone(),
                    g.clone(),
                ],
            );
            let (hfg_id, _hfg) = b.fresh_local(homeo_fg.clone());

            let compact_alpha = Expr::app(
                Expr::app(topology_compact(u_level.clone()), alpha.clone()),
                inst_alpha.clone(),
            );
            let (hc_id, _hc) = b.fresh_local(compact_alpha.clone());

            let compact_beta = Expr::app(
                Expr::app(topology_compact(v_level.clone()), beta.clone()),
                inst_beta.clone(),
            );

            let e = b.mk_pi(hc_id, BinderInfo::Default, compact_alpha, compact_beta);
            let e = b.mk_pi(hfg_id, BinderInfo::Default, homeo_fg, e);
            let e = b.mk_pi(g_id, BinderInfo::Default, g_ty, e);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_pi(
                inst_beta_id,
                BinderInfo::InstImplicit,
                Expr::app(topological_space(v_level.clone()), beta.clone()),
                e,
            );
            let e = b.mk_pi(
                inst_alpha_id,
                BinderInfo::InstImplicit,
                Expr::app(topological_space(u_level.clone()), alpha.clone()),
                e,
            );
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        decls.push(Declaration::Axiom {
            name: Name::from_string("Topology.homeomorphism_compact"),
            level_params: vec![u.clone(), v.clone()],
            type_: homeomorphism_compact_type,
        });
    }

    decls
}

impl Environment {
    /// Initialize Topology.Homeomorphism for topological equivalences between spaces.
    ///
    /// A homeomorphism is a continuous bijection with a continuous inverse.
    ///
    /// This adds:
    /// - `Topology.Homeomorphism : {α : Type u} → {β : Type v} → [TopologicalSpace α] →
    ///     [TopologicalSpace β] → (α → β) → (β → α) → Prop`
    /// - `Topology.homeomorphism_def` : Homeomorphism iff both maps are continuous and inverse
    /// - `Topology.homeomorphism_id` : Identity is a homeomorphism
    /// - `Topology.homeomorphism_symm` : Inverse of a homeomorphism is a homeomorphism
    /// - `Topology.homeomorphism_comp` : Composition of homeomorphisms is a homeomorphism
    /// - `Topology.homeomorphism_connected` : Homeomorphisms preserve connectedness (when available)
    /// - `Topology.homeomorphism_compact` : Homeomorphisms preserve compactness (when available)
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.topology_homeomorphism_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_topology_homeomorphism(&mut self) -> Result<(), EnvError> {
        if self.topology_homeomorphism_init {
            return Ok(());
        }
        // #1483: dynamic stack growth for init chain
        crate::expr::stack_safe(|| {
            self.init_topology_continuous()?;
            self.init_and()?;
            self.init_eq()?;
            self.init_iff()?;

            let include_connected = self.topology_connected_init;
            let include_compact = self.topology_compact_init;
            self.add_init_decls(topology_homeomorphism_decl_templates(
                include_connected,
                include_compact,
            ))?;

            self.topology_homeomorphism_init = true;
            Ok(())
        })
    }

    /// Check if Topology.Homeomorphism has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.topology_homeomorphism_init == true`
    #[cfg(test)]
    pub(crate) fn has_topology_homeomorphism(&self) -> bool {
        self.topology_homeomorphism_init
    }
}
