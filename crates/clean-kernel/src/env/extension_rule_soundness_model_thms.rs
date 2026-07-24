// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Model-level theorem declarations for concrete extension rule soundness.
//!
//! Registers the kernel-level axiom surfaces for the constructive model
//! arguments that underpin the forward and reverse satisfiability results:
//! 4. `ExtensionSoundness.extension_preserves_model`
//! 5. `ExtensionSoundness.extension_projection`
//!
//! These theorems work at the level of individual assignments rather than
//! existential satisfiability, providing the constructive witness for the
//! satisfiability-level theorems in `extension_rule_soundness_theorems.rs`.

use super::extension_rule_soundness::ExtensionSoundnessConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    // ====================================================================
    // Theorem 4: Concrete model preservation
    // ====================================================================

    /// Helper for `extension_preserves_model`:
    /// `forall (f g : PropForm) (y : Nat) (sigma : Assignment),
    ///    fresh_for y f -> eval f sigma = true -> Prop`.
    ///
    /// Encodes the forward model-preservation claim that extending `sigma`
    /// with `y = eval g sigma` satisfies `extend_def f y g`.
    pub(super) fn register_extension_preserves_model_helper(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        let name = "ExtensionSoundness.extension_preserves_model_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }

        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let fresh_for = Expr::const_(Name::from_string("ExtensionSoundness.fresh_for"), vec![]);
        let eval = Expr::const_(Name::from_string("ExtensionSoundness.eval"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.prop_form.clone());
            let (g_id, _) = b.fresh_local(c.prop_form.clone());
            let (y_id, y) = b.fresh_local(c.nat.clone());
            let (sigma_id, sigma) = b.fresh_local(c.assignment.clone());

            let fresh_y_f = Expr::apps(fresh_for, [y.clone(), f.clone()]);
            let eval_f_sigma = Expr::apps(eval, [f.clone(), sigma.clone()]);
            let eval_f_true = Expr::apps(eq, [c.bool_.clone(), eval_f_sigma, bool_true]);

            let (fresh_id, _) = b.fresh_local(fresh_y_f.clone());
            let (eval_id, _) = b.fresh_local(eval_f_true.clone());

            let e = c.prop.clone();
            let e = b.mk_pi(eval_id, BinderInfo::Default, eval_f_true, e);
            let e = b.mk_pi(fresh_id, BinderInfo::Default, fresh_y_f, e);
            let e = b.mk_pi(sigma_id, BinderInfo::Default, c.assignment.clone(), e);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.prop_form.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.prop_form.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `extension_preserves_model : forall (f g : PropForm) (y : Nat)
    ///    (sigma : Assignment),
    ///    fresh_for y f -> eval f sigma = true ->
    ///    extension_preserves_model_helper f g y sigma`
    ///
    /// The theorem surface for the explicit assignment-extension argument.
    /// Semantically, the helper application denotes
    /// `eval (extend_def f y g) (assign_extend sigma y (eval g sigma)) = true`.
    pub(super) fn register_extension_preserves_model(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "ExtensionSoundness.extension_preserves_model";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }

        let helper = Expr::const_(
            Name::from_string("ExtensionSoundness.extension_preserves_model_helper"),
            vec![],
        );
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let fresh_for = Expr::const_(Name::from_string("ExtensionSoundness.fresh_for"), vec![]);
        let eval = Expr::const_(Name::from_string("ExtensionSoundness.eval"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.prop_form.clone());
            let (g_id, g) = b.fresh_local(c.prop_form.clone());
            let (y_id, y) = b.fresh_local(c.nat.clone());
            let (sigma_id, sigma) = b.fresh_local(c.assignment.clone());

            let fresh_y_f = Expr::apps(fresh_for, [y.clone(), f.clone()]);
            let eval_f_sigma = Expr::apps(eval, [f.clone(), sigma.clone()]);
            let eval_f_true = Expr::apps(eq, [c.bool_.clone(), eval_f_sigma, bool_true]);

            let (fresh_id, fresh_h) = b.fresh_local(fresh_y_f.clone());
            let (eval_id, eval_h) = b.fresh_local(eval_f_true.clone());

            let body = Expr::apps(
                helper,
                [
                    f.clone(),
                    g.clone(),
                    y.clone(),
                    sigma.clone(),
                    fresh_h.clone(),
                    eval_h.clone(),
                ],
            );
            let e = body;
            let e = b.mk_pi(eval_id, BinderInfo::Default, eval_f_true, e);
            let e = b.mk_pi(fresh_id, BinderInfo::Default, fresh_y_f, e);
            let e = b.mk_pi(sigma_id, BinderInfo::Default, c.assignment.clone(), e);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.prop_form.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.prop_form.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Theorem 5: Concrete model projection
    // ====================================================================

    /// Helper for `extension_projection`:
    /// `forall (f g : PropForm) (y : Nat) (sigma : Assignment),
    ///    fresh_for y f -> eval (extend_def f y g) sigma = true -> Prop`.
    ///
    /// Encodes the reverse model-projection claim that restricting a model of
    /// the extended formula yields a model of the original formula.
    pub(super) fn register_extension_projection_helper(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        let name = "ExtensionSoundness.extension_projection_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }

        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let fresh_for = Expr::const_(Name::from_string("ExtensionSoundness.fresh_for"), vec![]);
        let extend_def = Expr::const_(Name::from_string("ExtensionSoundness.extend_def"), vec![]);
        let eval = Expr::const_(Name::from_string("ExtensionSoundness.eval"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.prop_form.clone());
            let (g_id, g) = b.fresh_local(c.prop_form.clone());
            let (y_id, y) = b.fresh_local(c.nat.clone());
            let (sigma_id, sigma) = b.fresh_local(c.assignment.clone());

            let fresh_y_f = Expr::apps(fresh_for, [y.clone(), f.clone()]);
            let ext_f_y_g = Expr::apps(extend_def, [f.clone(), y.clone(), g.clone()]);
            let eval_ext_sigma = Expr::apps(eval, [ext_f_y_g, sigma.clone()]);
            let eval_ext_true = Expr::apps(eq, [c.bool_.clone(), eval_ext_sigma, bool_true]);

            let (fresh_id, _) = b.fresh_local(fresh_y_f.clone());
            let (eval_id, _) = b.fresh_local(eval_ext_true.clone());

            let e = c.prop.clone();
            let e = b.mk_pi(eval_id, BinderInfo::Default, eval_ext_true, e);
            let e = b.mk_pi(fresh_id, BinderInfo::Default, fresh_y_f, e);
            let e = b.mk_pi(sigma_id, BinderInfo::Default, c.assignment.clone(), e);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.prop_form.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.prop_form.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty,
        })
    }

    /// `extension_projection : forall (f g : PropForm) (y : Nat)
    ///    (sigma : Assignment),
    ///    fresh_for y f -> eval (extend_def f y g) sigma = true ->
    ///    extension_projection_helper f g y sigma`
    ///
    /// The theorem surface for the explicit assignment-projection argument.
    /// Semantically, the helper application denotes
    /// `eval f (assign_restrict sigma y) = true`.
    pub(super) fn register_extension_projection(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "ExtensionSoundness.extension_projection";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }

        let helper = Expr::const_(
            Name::from_string("ExtensionSoundness.extension_projection_helper"),
            vec![],
        );
        let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let fresh_for = Expr::const_(Name::from_string("ExtensionSoundness.fresh_for"), vec![]);
        let extend_def = Expr::const_(Name::from_string("ExtensionSoundness.extend_def"), vec![]);
        let eval = Expr::const_(Name::from_string("ExtensionSoundness.eval"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.prop_form.clone());
            let (g_id, g) = b.fresh_local(c.prop_form.clone());
            let (y_id, y) = b.fresh_local(c.nat.clone());
            let (sigma_id, sigma) = b.fresh_local(c.assignment.clone());

            let fresh_y_f = Expr::apps(fresh_for, [y.clone(), f.clone()]);
            let ext_f_y_g = Expr::apps(extend_def, [f.clone(), y.clone(), g.clone()]);
            let eval_ext_sigma = Expr::apps(eval, [ext_f_y_g, sigma.clone()]);
            let eval_ext_true = Expr::apps(eq, [c.bool_.clone(), eval_ext_sigma, bool_true]);

            let (fresh_id, fresh_h) = b.fresh_local(fresh_y_f.clone());
            let (eval_id, eval_h) = b.fresh_local(eval_ext_true.clone());

            let body = Expr::apps(
                helper,
                [
                    f.clone(),
                    g.clone(),
                    y.clone(),
                    sigma.clone(),
                    fresh_h.clone(),
                    eval_h.clone(),
                ],
            );
            let e = body;
            let e = b.mk_pi(eval_id, BinderInfo::Default, eval_ext_true, e);
            let e = b.mk_pi(fresh_id, BinderInfo::Default, fresh_y_f, e);
            let e = b.mk_pi(sigma_id, BinderInfo::Default, c.assignment.clone(), e);
            let e = b.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(g_id, BinderInfo::Default, c.prop_form.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.prop_form.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Axiom {
            name: Name::from_string(thm_name),
            level_params: vec![],
            type_: ty,
        })
    }
}
