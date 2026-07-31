// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level declarations for concrete extension rule soundness.
//!
//! Registers the concrete propositional syntax and semantic operations needed
//! to state soundness of the extension rule in propositional logic. Unlike the
//! abstract `extension_rule.rs` declarations, this module uses an explicit
//! formula type with native biconditional and semantic operations on total
//! Boolean assignments.
//!
//! The extension rule introduces a fresh variable `y` together with a
//! definitional extension `F ∧ (y ↔ g)`. Soundness states that adding such a
//! fresh definitional extension preserves satisfiability after extending or
//! restricting assignments appropriately.
//!
//! Type and operation definitions live here; theorem registrations belong in a
//! separate `_theorems.rs` file.

#[cfg(test)]
use crate::env::decl_builder::EnvDeclBuilder;
#[cfg(test)]
use crate::env::{Declaration, EnvError, Environment};
#[cfg(test)]
use crate::expr::{BinderInfo, Expr, ExprKind};
#[cfg(test)]
use crate::level::Level;
#[cfg(test)]
use crate::name::Name;

/// Shared constants used across all concrete extension soundness declarations.
#[cfg(test)]
pub(super) struct ExtensionSoundnessConsts {
    pub(super) nat: Expr,
    pub(super) bool_: Expr,
    pub(super) prop: Expr,
    pub(super) type0: Expr,
    /// ExtensionSoundness.PropForm : Type
    pub(super) prop_form: Expr,
    /// ExtensionSoundness.Assignment : Type
    pub(super) assignment: Expr,
    /// ProofTheory.VarSet : Type (reused from craig_interpolation)
    pub(super) var_set: Expr,
}

#[cfg(test)]
impl ExtensionSoundnessConsts {
    /// Construct the shared constant expressions referenced by this module.
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            bool_: Expr::const_(Name::from_string("Bool"), vec![]),
            prop: Expr::from_kind(ExprKind::Sort(Level::zero())),
            type0: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            prop_form: Expr::const_(Name::from_string("ExtensionSoundness.PropForm"), vec![]),
            assignment: Expr::const_(Name::from_string("ExtensionSoundness.Assignment"), vec![]),
            var_set: Expr::const_(Name::from_string("ProofTheory.VarSet"), vec![]),
        }
    }
}

#[cfg(test)]
impl Environment {
    /// Initialize the concrete extension rule soundness declarations.
    ///
    /// Depends on: `init_bool()`, `init_nat()`, `init_craig_interpolation()`.
    #[cfg(test)]
    pub(crate) fn init_extension_rule_soundness(&mut self) -> Result<(), EnvError> {
        if self.extension_rule_soundness_init {
            return Ok(());
        }
        self.init_bool()?;
        self.init_nat()?;
        self.init_eq()?;
        self.init_craig_interpolation()?;

        let c = ExtensionSoundnessConsts::new();
        self.register_extension_soundness_prop_form(&c)?;
        self.register_extension_soundness_assignment(&c)?;
        self.register_extension_soundness_eval(&c)?;
        self.register_extension_soundness_satisfiable(&c)?;
        self.register_extension_soundness_vars_of(&c)?;
        self.register_extension_soundness_fresh_for(&c)?;
        self.register_extension_soundness_extend_def(&c)?;
        self.register_extension_soundness_assign_extend(&c)?;
        self.register_extension_soundness_assign_restrict(&c)?;
        // Theorem registrations (in extension_rule_soundness_theorems.rs)
        self.register_extension_forward_helper(&c)?;
        self.register_extension_forward(&c)?;
        self.register_extension_reverse_helper(&c)?;
        self.register_extension_reverse(&c)?;
        self.register_extension_equisatisfiable_helper(&c)?;
        self.register_extension_equisatisfiable(&c)?;
        self.register_extension_preserves_model_helper(&c)?;
        self.register_extension_preserves_model(&c)?;
        self.register_extension_projection_helper(&c)?;
        self.register_extension_projection(&c)?;

        self.extension_rule_soundness_init = true;
        Ok(())
    }

    // ====================================================================
    // Definition 1: PropForm — concrete propositional formula syntax
    // ====================================================================

    /// `PropForm : Type` — concrete propositional formulas with native
    /// biconditional.
    ///
    /// Constructors:
    /// - `Var (v : Nat)` — propositional variable
    /// - `Neg (f : PropForm)` — negation
    /// - `Conj (a b : PropForm)` — conjunction
    /// - `Disj (a b : PropForm)` — disjunction
    /// - `Impl (a b : PropForm)` — implication
    /// - `Iff (a b : PropForm)` — biconditional
    #[cfg(test)]
    fn register_extension_soundness_prop_form(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ExtensionSoundness.PropForm"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.PropForm"),
            level_params: vec![],
            type_: c.type0.clone(),
        })?;

        let var_ty = Expr::pi(BinderInfo::Default, c.nat.clone(), c.prop_form.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.PropForm.Var"),
            level_params: vec![],
            type_: var_ty,
        })?;

        let neg_ty = Expr::pi(
            BinderInfo::Default,
            c.prop_form.clone(),
            c.prop_form.clone(),
        );
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.PropForm.Neg"),
            level_params: vec![],
            type_: neg_ty,
        })?;

        let conj_ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.prop_form.clone());
            let (b_id, _) = b.fresh_local(c.prop_form.clone());
            let e = b.mk_pi(
                b_id,
                BinderInfo::Default,
                c.prop_form.clone(),
                c.prop_form.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_form.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.PropForm.Conj"),
            level_params: vec![],
            type_: conj_ty,
        })?;

        let disj_ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.prop_form.clone());
            let (b_id, _) = b.fresh_local(c.prop_form.clone());
            let e = b.mk_pi(
                b_id,
                BinderInfo::Default,
                c.prop_form.clone(),
                c.prop_form.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_form.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.PropForm.Disj"),
            level_params: vec![],
            type_: disj_ty,
        })?;

        let impl_ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.prop_form.clone());
            let (b_id, _) = b.fresh_local(c.prop_form.clone());
            let e = b.mk_pi(
                b_id,
                BinderInfo::Default,
                c.prop_form.clone(),
                c.prop_form.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_form.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.PropForm.Impl"),
            level_params: vec![],
            type_: impl_ty,
        })?;

        let iff_ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.prop_form.clone());
            let (b_id, _) = b.fresh_local(c.prop_form.clone());
            let e = b.mk_pi(
                b_id,
                BinderInfo::Default,
                c.prop_form.clone(),
                c.prop_form.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, c.prop_form.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.PropForm.Iff"),
            level_params: vec![],
            type_: iff_ty,
        })
    }

    // ====================================================================
    // Definition 2: Assignment — total Boolean valuation
    // ====================================================================

    /// `Assignment : Type` — a total variable assignment, intended
    /// concretely as a valuation `Nat -> Bool`.
    #[cfg(test)]
    fn register_extension_soundness_assignment(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ExtensionSoundness.Assignment"))
            .is_some()
        {
            return Ok(());
        }
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.Assignment"),
            level_params: vec![],
            type_: c.type0.clone(),
        })
    }

    // ====================================================================
    // Definition 3: eval — Boolean evaluation
    // ====================================================================

    /// `eval (f : PropForm) (a : Assignment) : Bool`
    ///
    /// Evaluates a propositional formula under a total Boolean assignment.
    #[cfg(test)]
    fn register_extension_soundness_eval(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ExtensionSoundness.eval"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, _) = b.fresh_local(c.prop_form.clone());
            let (a_id, _) = b.fresh_local(c.assignment.clone());
            let e = b.mk_pi(
                a_id,
                BinderInfo::Default,
                c.assignment.clone(),
                c.bool_.clone(),
            );
            let e = b.mk_pi(f_id, BinderInfo::Default, c.prop_form.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.eval"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 4: satisfiable — semantic satisfiability
    // ====================================================================

    /// `satisfiable (f : PropForm) : Prop`
    ///
    /// States that there exists an assignment under which `f` evaluates to
    /// `true`.
    #[cfg(test)]
    fn register_extension_soundness_satisfiable(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ExtensionSoundness.satisfiable"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.prop_form.clone(), c.prop.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.satisfiable"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 5: vars_of — variables appearing in a formula
    // ====================================================================

    /// `vars_of (f : PropForm) : VarSet`
    ///
    /// Returns the set of variable indices occurring in a propositional
    /// formula.
    #[cfg(test)]
    fn register_extension_soundness_vars_of(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ExtensionSoundness.vars_of"))
            .is_some()
        {
            return Ok(());
        }
        let ty = Expr::pi(BinderInfo::Default, c.prop_form.clone(), c.var_set.clone());
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.vars_of"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 6: fresh_for — freshness of an extension variable
    // ====================================================================

    /// `fresh_for (y : Nat) (f : PropForm) : Prop`
    ///
    /// States that variable `y` does not occur in `f`, equivalently that
    /// `y` is not a member of `vars_of f`.
    #[cfg(test)]
    fn register_extension_soundness_fresh_for(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ExtensionSoundness.fresh_for"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (y_id, _) = b.fresh_local(c.nat.clone());
            let (f_id, _) = b.fresh_local(c.prop_form.clone());
            let e = b.mk_pi(
                f_id,
                BinderInfo::Default,
                c.prop_form.clone(),
                c.prop.clone(),
            );
            let e = b.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.fresh_for"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 7: extend_def — definitional extension formula
    // ====================================================================

    /// `extend_def (f : PropForm) (y : Nat) (g : PropForm) : PropForm`
    ///
    /// Forms the definitional extension `f ∧ (Var y ↔ g)` obtained by
    /// introducing the fresh variable `y` as an abbreviation for `g`.
    #[cfg(test)]
    fn register_extension_soundness_extend_def(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ExtensionSoundness.extend_def"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, _) = b.fresh_local(c.prop_form.clone());
            let (y_id, _) = b.fresh_local(c.nat.clone());
            let (g_id, _) = b.fresh_local(c.prop_form.clone());
            let e = b.mk_pi(
                g_id,
                BinderInfo::Default,
                c.prop_form.clone(),
                c.prop_form.clone(),
            );
            let e = b.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(f_id, BinderInfo::Default, c.prop_form.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.extend_def"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 8: assign_extend — extend an assignment at one variable
    // ====================================================================

    /// `assign_extend (a : Assignment) (y : Nat) (v : Bool) : Assignment`
    ///
    /// Overrides assignment `a` at variable `y` with value `v`, leaving all
    /// other variables unchanged.
    #[cfg(test)]
    fn register_extension_soundness_assign_extend(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ExtensionSoundness.assign_extend"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.assignment.clone());
            let (y_id, _) = b.fresh_local(c.nat.clone());
            let (v_id, _) = b.fresh_local(c.bool_.clone());
            let e = b.mk_pi(
                v_id,
                BinderInfo::Default,
                c.bool_.clone(),
                c.assignment.clone(),
            );
            let e = b.mk_pi(y_id, BinderInfo::Default, c.nat.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Default, c.assignment.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.assign_extend"),
            level_params: vec![],
            type_: ty,
        })
    }

    // ====================================================================
    // Definition 9: assign_restrict — project away an extension variable
    // ====================================================================

    /// `assign_restrict (a : Assignment) (y : Nat) : Assignment`
    ///
    /// Projects an assignment away from the distinguished extension variable
    /// `y`, forgetting the value assigned at that coordinate.
    #[cfg(test)]
    fn register_extension_soundness_assign_restrict(
        &mut self,
        c: &ExtensionSoundnessConsts,
    ) -> Result<(), EnvError> {
        if self
            .get_const(&Name::from_string("ExtensionSoundness.assign_restrict"))
            .is_some()
        {
            return Ok(());
        }
        let ty = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(c.assignment.clone());
            let (y_id, _) = b.fresh_local(c.nat.clone());
            let e = b.mk_pi(
                y_id,
                BinderInfo::Default,
                c.nat.clone(),
                c.assignment.clone(),
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, c.assignment.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Axiom {
            name: Name::from_string("ExtensionSoundness.assign_restrict"),
            level_params: vec![],
            type_: ty,
        })
    }
}
