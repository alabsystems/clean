// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Or disjunction type: Or.inl, Or.inr, Or.rec
//!
//! Split from logic_connectives.rs for #1207.

use super::decl_builder::EnvDeclBuilder;
use super::*;

impl Environment {
    /// Initialize Or disjunction type
    ///
    /// Or a b (written a ∨ b) is the coproduct type in Prop.
    /// inductive Or (a b : Prop) : Prop where
    ///   | inl (h : a) : Or a b
    ///   | inr (h : b) : Or a b
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.has_or() == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    /// ENSURES: Adds Or, Or.inl, Or.inr, Or.rec
    pub fn init_or(&mut self) -> Result<(), EnvError> {
        if self.or_init {
            return Ok(());
        }

        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let or_const = Expr::const_(Name::from_string("Or"), vec![]);

        let or_type = Self::build_or_type(&prop);
        let or_inl_type = Self::build_or_inl_type(&prop, &or_const);
        let or_inr_type = Self::build_or_inr_type(&prop, &or_const);

        let or_decl = InductiveDecl {
            level_params: vec![],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("Or"),
                type_: or_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Or.inl"),
                        type_: or_inl_type,
                    },
                    Constructor {
                        name: Name::from_string("Or.inr"),
                        type_: or_inr_type,
                    },
                ],
            }],
        };

        self.add_inductive(or_decl)?;

        self.or_init = true;
        Ok(())
    }

    /// Or : Prop → Prop → Prop
    fn build_or_type(prop: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (a_id, _) = b.fresh_local(prop.clone());
        let (bb_id, _) = b.fresh_local(prop.clone());
        let r = prop.clone();
        let r = b.mk_pi(bb_id, BinderInfo::Default, prop.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Default, prop.clone(), r);
        b.finish(r)
    }

    /// Or.inl : ∀ {a b : Prop}, a → Or a b
    fn build_or_inl_type(prop: &Expr, or_const: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a_var) = b.fresh_local(prop.clone());
        let (bb_id, bb_var) = b.fresh_local(prop.clone());
        let (h_id, _) = b.fresh_local(a_var.clone());
        let r = Expr::app(Expr::app(or_const.clone(), a_var.clone()), bb_var);
        let r = b.mk_pi(h_id, BinderInfo::Default, a_var, r);
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, prop.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), r);
        b.finish(r)
    }

    /// Or.inr : ∀ {a b : Prop}, b → Or a b
    fn build_or_inr_type(prop: &Expr, or_const: &Expr) -> Expr {
        let mut b = EnvDeclBuilder::new();
        let (a_id, a_var) = b.fresh_local(prop.clone());
        let (bb_id, bb_var) = b.fresh_local(prop.clone());
        let (h_id, _) = b.fresh_local(bb_var.clone());
        let r = Expr::app(Expr::app(or_const.clone(), a_var), bb_var.clone());
        let r = b.mk_pi(h_id, BinderInfo::Default, bb_var, r);
        let r = b.mk_pi(bb_id, BinderInfo::Implicit, prop.clone(), r);
        let r = b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), r);
        b.finish(r)
    }

    /// Check if Or disjunction has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_or()` has been called successfully
    /// ENSURES: Pure function - no side effects
    #[cfg(test)]
    pub(crate) fn has_or(&self) -> bool {
        self.or_init
    }
}
