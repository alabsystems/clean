// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! True, False, Not, Ne, and absurd definitions
//!
//! This module contains:
//! - True inductive type (True.intro)
//! - False inductive type (no constructors)
//! - False.elim, absurd, Not, Ne
//!
//! Split from logic.rs for #307.

use super::decl_builder::EnvDeclBuilder;
use super::*;

impl Environment {
    /// Initialize True and False inductive types
    ///
    /// True: Prop with constructor True.intro : True
    /// False: Prop with no constructors (empty type)
    ///
    /// These are the fundamental logical constants.
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.has_true_false() == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    /// ENSURES: Adds True, True.intro, False, False.rec, Not, absurd
    pub fn init_true_false(&mut self) -> Result<(), EnvError> {
        if self.true_false_init {
            return Ok(());
        }

        // Ne (defined below) depends on Eq
        if !self.eq_init {
            self.init_eq()?;
        }

        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        // True : Prop
        // inductive True : Prop where
        //   | intro : True
        let true_const = Expr::const_(Name::from_string("True"), vec![]);

        // True.intro : True
        let true_intro_type = true_const.clone();

        let true_decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("True"),
                type_: prop.clone(),
                constructors: vec![Constructor {
                    name: Name::from_string("True.intro"),
                    type_: true_intro_type,
                }],
            }],
        };

        self.add_inductive(true_decl)?;

        // False : Prop
        // inductive False : Prop
        // (no constructors - uninhabited type)
        let false_decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("False"),
                type_: prop.clone(),
                constructors: vec![], // No constructors!
            }],
        };

        self.add_inductive(false_decl)?;

        // False.elim : {C : Sort u} → False → C
        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        let false_rec_const = Expr::const_(
            Name::from_string("False.rec"),
            vec![Level::param(u.clone())],
        );

        let false_elim_type = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c_var) = b.fresh_local(sort_u.clone());
            let (h_id, _) = b.fresh_local(false_const.clone());
            let r = c_var;
            let r = b.mk_pi(h_id, BinderInfo::Default, false_const.clone(), r);
            let r = b.mk_pi(c_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        let false_elim_value = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c_var) = b.fresh_local(sort_u.clone());
            let (h_id, h_var) = b.fresh_local(false_const.clone());
            // motive = λ (_ : False), C
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m_id, _) = c.fresh_local(false_const.clone());
                c.mk_lam(m_id, BinderInfo::Default, false_const.clone(), c_var)
            };
            let body = Expr::app(Expr::app(false_rec_const, motive), h_var);
            let r = body;
            let r = b.mk_lam(h_id, BinderInfo::Default, false_const.clone(), r);
            let r = b.mk_lam(c_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("False.elim"),
            level_params: vec![u.clone()],
            type_: false_elim_type,
            value: false_elim_value,
            is_reducible: true,
        })?;

        // absurd : {a : Prop} → {b : Sort u} → a → ¬a → b
        let false_elim_const = Expr::const_(
            Name::from_string("False.elim"),
            vec![Level::param(u.clone())],
        );

        let absurd_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(sort_u.clone());
            let (h1_id, _) = b.fresh_local(a_var.clone());
            // ¬a = a → False
            let not_a = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = c.fresh_local(a_var.clone());
                c.mk_pi(
                    x_id,
                    BinderInfo::Default,
                    a_var.clone(),
                    false_const.clone(),
                )
            };
            let (h2_id, _) = b.fresh_local(not_a.clone());
            let r = bb_var;
            let r = b.mk_pi(h2_id, BinderInfo::Default, not_a, r);
            let r = b.mk_pi(h1_id, BinderInfo::Default, a_var, r);
            let r = b.mk_pi(bb_id, BinderInfo::Implicit, sort_u.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        let absurd_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(sort_u.clone());
            let (h1_id, h1_var) = b.fresh_local(a_var.clone());
            let not_a = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = c.fresh_local(a_var.clone());
                c.mk_pi(
                    x_id,
                    BinderInfo::Default,
                    a_var.clone(),
                    false_const.clone(),
                )
            };
            let (h2_id, h2_var) = b.fresh_local(not_a.clone());
            // False.elim {b} (h2 h1)
            let body = Expr::app(
                Expr::app(false_elim_const, bb_var),
                Expr::app(h2_var, h1_var),
            );
            let r = body;
            let r = b.mk_lam(h2_id, BinderInfo::Default, not_a, r);
            let r = b.mk_lam(h1_id, BinderInfo::Default, a_var, r);
            let r = b.mk_lam(bb_id, BinderInfo::Implicit, sort_u.clone(), r);
            let r = b.mk_lam(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("absurd"),
            level_params: vec![u.clone()],
            type_: absurd_type,
            value: absurd_value,
            is_reducible: true,
        })?;

        // Not : Prop → Prop  where Not a := a → False
        let not_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(prop.clone());
            let r = prop.clone();
            let r = b.mk_pi(a_id, BinderInfo::Default, prop.clone(), r);
            b.finish(r)
        };

        let not_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let body = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = c.fresh_local(a_var.clone());
                c.mk_pi(x_id, BinderInfo::Default, a_var, false_const.clone())
            };
            let r = b.mk_lam(a_id, BinderInfo::Default, prop.clone(), body);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Not"),
            level_params: vec![],
            type_: not_type,
            value: not_value,
            is_reducible: true,
        })?;

        // Ne : {α : Sort u} → α → α → Prop  where Ne a b := Not (Eq α a b)
        let u_level = Level::param(u.clone());

        let ne_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (a_id, _) = b.fresh_local(alpha.clone());
            let (bb_id, _) = b.fresh_local(alpha.clone());
            let r = prop.clone();
            let r = b.mk_pi(bb_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        let ne_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (a_id, a_var) = b.fresh_local(alpha.clone());
            let (bb_id, bb_var) = b.fresh_local(alpha.clone());
            // Not (Eq α a b)
            let eq_ab = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("Eq"), vec![u_level]),
                        alpha.clone(),
                    ),
                    a_var,
                ),
                bb_var,
            );
            let body = Expr::app(Expr::const_(Name::from_string("Not"), vec![]), eq_ab);
            let r = body;
            let r = b.mk_lam(bb_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha, r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Ne"),
            level_params: vec![u],
            type_: ne_type,
            value: ne_value,
            is_reducible: true,
        })?;

        self.true_false_init = true;
        Ok(())
    }

    /// Check if True/False types have been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_true_false()` has been called successfully
    /// ENSURES: Pure function - no side effects
    #[cfg(test)]
    pub(crate) fn has_true_false(&self) -> bool {
        self.true_false_init
    }
}
