// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theorem declarations for the concrete extension rule soundness formalization.
//!
//! Registers the kernel-level axiom surfaces for the satisfiability-level
//! theorems:
//! 1. `ExtensionSoundness.extension_forward`
//! 2. `ExtensionSoundness.extension_reverse`
//! 3. `ExtensionSoundness.extension_equisatisfiable`
//!
//! Model-level theorems (4, 5) live in `extension_rule_soundness_model_thms.rs`.
//!
//! Each theorem follows the local helper-axiom pattern: a `_helper` constant
//! packages the proposition body as an opaque proposition-valued predicate, and
//! the theorem constant universally quantifies the data and hypothesis binders
//! before concluding with the applied helper.

use super::extension_rule_soundness::ExtensionSoundnessConsts;
use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;

impl Environment {
    // ====================================================================
    // Theorem 1: Forward satisfiability preservation
    // ====================================================================

    /// Helper for `extension_forward`:
    /// `forall (f g : PropForm) (y : Nat),
    ///    fresh_for y f -> satisfiable f -> Prop`.
    ///
    /// Encodes the forward direction of extension-rule soundness: if `f` is
    /// satisfiable and `y` is fresh for `f`, then `extend_def f y g` is
    /// satisfiable.
    pub(super) fn register_extension_forward_helper(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        let name = "ExtensionSoundness.extension_forward_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }

        let fresh_for = Expr::const_(Name::from_string("ExtensionSoundness.fresh_for"), vec![]);
        let satisfiable = Expr::const_(Name::from_string("ExtensionSoundness.satisfiable"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.prop_form.clone());
            let (g_id, _) = b.fresh_local(c.prop_form.clone());
            let (y_id, y) = b.fresh_local(c.nat.clone());

            let fresh_y_f = Expr::apps(fresh_for, [y.clone(), f.clone()]);
            let sat_f = Expr::app(satisfiable, f.clone());

            let (fresh_id, _) = b.fresh_local(fresh_y_f.clone());
            let (sat_id, _) = b.fresh_local(sat_f.clone());

            let e = c.prop.clone();
            let e = b.mk_pi(sat_id, BinderInfo::Default, sat_f, e);
            let e = b.mk_pi(fresh_id, BinderInfo::Default, fresh_y_f, e);
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

    /// `extension_forward : forall (f g : PropForm) (y : Nat),
    ///    fresh_for y f -> satisfiable f -> extension_forward_helper f g y`
    ///
    /// The theorem surface for forward extension soundness. Semantically, the
    /// helper application denotes `satisfiable (extend_def f y g)`.
    pub(super) fn register_extension_forward(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "ExtensionSoundness.extension_forward";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }

        let helper = Expr::const_(
            Name::from_string("ExtensionSoundness.extension_forward_helper"),
            vec![],
        );
        let fresh_for = Expr::const_(Name::from_string("ExtensionSoundness.fresh_for"), vec![]);
        let satisfiable = Expr::const_(Name::from_string("ExtensionSoundness.satisfiable"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.prop_form.clone());
            let (g_id, g) = b.fresh_local(c.prop_form.clone());
            let (y_id, y) = b.fresh_local(c.nat.clone());

            let fresh_y_f = Expr::apps(fresh_for, [y.clone(), f.clone()]);
            let sat_f = Expr::app(satisfiable, f.clone());

            let (fresh_id, fresh_h) = b.fresh_local(fresh_y_f.clone());
            let (sat_id, sat_h) = b.fresh_local(sat_f.clone());

            let body = Expr::apps(
                helper,
                [
                    f.clone(),
                    g.clone(),
                    y.clone(),
                    fresh_h.clone(),
                    sat_h.clone(),
                ],
            );
            let e = body;
            let e = b.mk_pi(sat_id, BinderInfo::Default, sat_f, e);
            let e = b.mk_pi(fresh_id, BinderInfo::Default, fresh_y_f, e);
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
    // Theorem 2: Reverse satisfiability preservation
    // ====================================================================

    /// Helper for `extension_reverse`:
    /// `forall (f g : PropForm) (y : Nat),
    ///    fresh_for y f -> satisfiable (extend_def f y g) -> Prop`.
    ///
    /// Encodes the reverse direction of extension-rule soundness: any model of
    /// the extended formula projects to a model of the original formula.
    pub(super) fn register_extension_reverse_helper(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        let name = "ExtensionSoundness.extension_reverse_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }

        let fresh_for = Expr::const_(Name::from_string("ExtensionSoundness.fresh_for"), vec![]);
        let satisfiable = Expr::const_(Name::from_string("ExtensionSoundness.satisfiable"), vec![]);
        let extend_def = Expr::const_(Name::from_string("ExtensionSoundness.extend_def"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.prop_form.clone());
            let (g_id, g) = b.fresh_local(c.prop_form.clone());
            let (y_id, y) = b.fresh_local(c.nat.clone());

            let fresh_y_f = Expr::apps(fresh_for, [y.clone(), f.clone()]);
            let ext_f_y_g = Expr::apps(extend_def, [f.clone(), y.clone(), g.clone()]);
            let sat_ext = Expr::app(satisfiable, ext_f_y_g);

            let (fresh_id, _) = b.fresh_local(fresh_y_f.clone());
            let (sat_id, _) = b.fresh_local(sat_ext.clone());

            let e = c.prop.clone();
            let e = b.mk_pi(sat_id, BinderInfo::Default, sat_ext, e);
            let e = b.mk_pi(fresh_id, BinderInfo::Default, fresh_y_f, e);
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

    /// `extension_reverse : forall (f g : PropForm) (y : Nat),
    ///    fresh_for y f -> satisfiable (extend_def f y g) ->
    ///    extension_reverse_helper f g y`
    ///
    /// The theorem surface for reverse extension soundness. Semantically, the
    /// helper application denotes `satisfiable f`.
    pub(super) fn register_extension_reverse(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "ExtensionSoundness.extension_reverse";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }

        let helper = Expr::const_(
            Name::from_string("ExtensionSoundness.extension_reverse_helper"),
            vec![],
        );
        let fresh_for = Expr::const_(Name::from_string("ExtensionSoundness.fresh_for"), vec![]);
        let satisfiable = Expr::const_(Name::from_string("ExtensionSoundness.satisfiable"), vec![]);
        let extend_def = Expr::const_(Name::from_string("ExtensionSoundness.extend_def"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.prop_form.clone());
            let (g_id, g) = b.fresh_local(c.prop_form.clone());
            let (y_id, y) = b.fresh_local(c.nat.clone());

            let fresh_y_f = Expr::apps(fresh_for, [y.clone(), f.clone()]);
            let ext_f_y_g = Expr::apps(extend_def, [f.clone(), y.clone(), g.clone()]);
            let sat_ext = Expr::app(satisfiable, ext_f_y_g);

            let (fresh_id, fresh_h) = b.fresh_local(fresh_y_f.clone());
            let (sat_id, sat_h) = b.fresh_local(sat_ext.clone());

            let body = Expr::apps(
                helper,
                [
                    f.clone(),
                    g.clone(),
                    y.clone(),
                    fresh_h.clone(),
                    sat_h.clone(),
                ],
            );
            let e = body;
            let e = b.mk_pi(sat_id, BinderInfo::Default, sat_ext, e);
            let e = b.mk_pi(fresh_id, BinderInfo::Default, fresh_y_f, e);
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
    // Theorem 3: Equisatisfiability
    // ====================================================================

    /// Helper for `extension_equisatisfiable`:
    /// `forall (f g : PropForm) (y : Nat), fresh_for y f -> Prop`.
    ///
    /// Encodes the combined iff statement that `f` is satisfiable exactly when
    /// `extend_def f y g` is satisfiable, with the biconditional understood as
    /// the conjunction of the two implication directions.
    pub(super) fn register_extension_equisatisfiable_helper(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        let name = "ExtensionSoundness.extension_equisatisfiable_helper";
        if self.get_const(&Name::from_string(name)).is_some() {
            return Ok(());
        }

        let fresh_for = Expr::const_(Name::from_string("ExtensionSoundness.fresh_for"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.prop_form.clone());
            let (g_id, _) = b.fresh_local(c.prop_form.clone());
            let (y_id, y) = b.fresh_local(c.nat.clone());

            let fresh_y_f = Expr::apps(fresh_for, [y.clone(), f.clone()]);
            let (fresh_id, _) = b.fresh_local(fresh_y_f.clone());

            let e = c.prop.clone();
            let e = b.mk_pi(fresh_id, BinderInfo::Default, fresh_y_f, e);
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

    /// `extension_equisatisfiable : forall (f g : PropForm) (y : Nat),
    ///    fresh_for y f -> extension_equisatisfiable_helper f g y`
    ///
    /// The theorem surface for the equisatisfiability claim. Semantically, the
    /// helper application denotes `(satisfiable f <-> satisfiable (extend_def f y g))`,
    /// encoded as a conjunction of implications.
    pub(super) fn register_extension_equisatisfiable(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        let thm_name = "ExtensionSoundness.extension_equisatisfiable";
        if self.get_const(&Name::from_string(thm_name)).is_some() {
            return Ok(());
        }

        let helper = Expr::const_(
            Name::from_string("ExtensionSoundness.extension_equisatisfiable_helper"),
            vec![],
        );
        let fresh_for = Expr::const_(Name::from_string("ExtensionSoundness.fresh_for"), vec![]);

        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(c.prop_form.clone());
            let (g_id, g) = b.fresh_local(c.prop_form.clone());
            let (y_id, y) = b.fresh_local(c.nat.clone());

            let fresh_y_f = Expr::apps(fresh_for, [y.clone(), f.clone()]);
            let (fresh_id, fresh_h) = b.fresh_local(fresh_y_f.clone());

            let body = Expr::apps(helper, [f.clone(), g.clone(), y.clone(), fresh_h.clone()]);
            let e = body;
            let e = b.mk_pi(fresh_id, BinderInfo::Default, fresh_y_f, e);
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
