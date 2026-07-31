// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Logical connectives: And (conjunction) and Exists (existential quantification)
//!
//! This module contains:
//! - And inductive type with And.intro, And.left, And.right, And.symm
//! - Exists inductive type with Exists.intro, Exists.elim
//!
//! Split from logic.rs for #307.

use super::decl_builder::EnvDeclBuilder;
use super::*;

impl Environment {
    /// Initialize And structure (conjunction)
    ///
    /// And a b (written a ∧ b) is the product type in Prop.
    /// structure And (a b : Prop) : Prop where
    ///   intro :: (left : a) (right : b)
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.has_and() == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    /// ENSURES: Adds And, And.intro, And.left, And.right, And.rec
    pub fn init_and(&mut self) -> Result<(), EnvError> {
        if self.and_init {
            return Ok(());
        }

        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        let and_const = Expr::const_(Name::from_string("And"), vec![]);

        // And : Prop → Prop → Prop
        let and_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, _) = b.fresh_local(prop.clone());
            let (bb_id, _) = b.fresh_local(prop.clone());
            let r = prop.clone();
            let r = b.mk_pi(bb_id, BinderInfo::Default, prop.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, prop.clone(), r);
            b.finish(r)
        };

        // And.intro : Π {a b : Prop}, a → b → And a b
        let and_intro_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let (l_id, _) = b.fresh_local(a_var.clone());
            let (r_id, _) = b.fresh_local(bb_var.clone());
            let result = Expr::app(Expr::app(and_const.clone(), a_var.clone()), bb_var.clone());
            let e = result;
            let e = b.mk_pi(r_id, BinderInfo::Default, bb_var, e);
            let e = b.mk_pi(l_id, BinderInfo::Default, a_var, e);
            let e = b.mk_pi(bb_id, BinderInfo::Implicit, prop.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), e);
            b.finish(e)
        };

        let and_decl = InductiveDecl {
            level_params: vec![],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("And"),
                type_: and_type,
                constructors: vec![Constructor {
                    name: Name::from_string("And.intro"),
                    type_: and_intro_type,
                }],
            }],
        };

        self.add_inductive(and_decl)?;

        // And.left : {a b : Prop} → And a b → a
        let and_left_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let and_ab = Expr::app(Expr::app(and_const.clone(), a_var.clone()), bb_var);
            let (h_id, _) = b.fresh_local(and_ab.clone());
            let r = a_var;
            let r = b.mk_pi(h_id, BinderInfo::Default, and_ab, r);
            let r = b.mk_pi(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        let and_left_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let and_ab = Expr::app(Expr::app(and_const.clone(), a_var), bb_var);
            let (h_id, h_var) = b.fresh_local(and_ab.clone());
            let body = Expr::proj(Name::from_string("And"), 0, h_var);
            let r = body;
            let r = b.mk_lam(h_id, BinderInfo::Default, and_ab, r);
            let r = b.mk_lam(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_lam(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("And.left"),
            level_params: vec![],
            type_: and_left_type,
            value: and_left_value,
            is_reducible: true,
        })?;

        // And.right : {a b : Prop} → And a b → b
        let and_right_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let and_ab = Expr::app(Expr::app(and_const.clone(), a_var), bb_var.clone());
            let (h_id, _) = b.fresh_local(and_ab.clone());
            let r = bb_var;
            let r = b.mk_pi(h_id, BinderInfo::Default, and_ab, r);
            let r = b.mk_pi(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        let and_right_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let and_ab = Expr::app(Expr::app(and_const.clone(), a_var), bb_var);
            let (h_id, h_var) = b.fresh_local(and_ab.clone());
            let body = Expr::proj(Name::from_string("And"), 1, h_var);
            let r = body;
            let r = b.mk_lam(h_id, BinderInfo::Default, and_ab, r);
            let r = b.mk_lam(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_lam(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("And.right"),
            level_params: vec![],
            type_: and_right_type,
            value: and_right_value,
            is_reducible: true,
        })?;

        // And.symm : {a b : Prop} → And a b → And b a
        let and_intro_const = Expr::const_(Name::from_string("And.intro"), vec![]);
        let and_left_const = Expr::const_(Name::from_string("And.left"), vec![]);
        let and_right_const = Expr::const_(Name::from_string("And.right"), vec![]);

        let and_symm_type = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let and_ab = Expr::app(Expr::app(and_const.clone(), a_var.clone()), bb_var.clone());
            let (h_id, _) = b.fresh_local(and_ab.clone());
            let and_ba = Expr::app(Expr::app(and_const.clone(), bb_var), a_var);
            let r = and_ba;
            let r = b.mk_pi(h_id, BinderInfo::Default, and_ab, r);
            let r = b.mk_pi(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        let and_symm_value = {
            let mut b = EnvDeclBuilder::new();
            let (a_id, a_var) = b.fresh_local(prop.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let and_ab = Expr::app(Expr::app(and_const.clone(), a_var.clone()), bb_var.clone());
            let (h_id, h_var) = b.fresh_local(and_ab.clone());
            // And.intro {b} {a} (And.right {a} {b} h) (And.left {a} {b} h)
            let body = Expr::app(
                Expr::app(
                    Expr::app(Expr::app(and_intro_const, bb_var.clone()), a_var.clone()),
                    Expr::app(
                        Expr::app(Expr::app(and_right_const, a_var.clone()), bb_var.clone()),
                        h_var.clone(),
                    ),
                ),
                Expr::app(Expr::app(Expr::app(and_left_const, a_var), bb_var), h_var),
            );
            let r = body;
            let r = b.mk_lam(h_id, BinderInfo::Default, and_ab, r);
            let r = b.mk_lam(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_lam(a_id, BinderInfo::Implicit, prop.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("And.symm"),
            level_params: vec![],
            type_: and_symm_type,
            value: and_symm_value,
            is_reducible: true,
        })?;

        self.and_init = true;
        Ok(())
    }

    /// Check if And structure has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_and()` has been called successfully
    /// ENSURES: Pure function - no side effects
    #[cfg(test)]
    pub(crate) fn has_and(&self) -> bool {
        self.and_init
    }

    /// Initialize Exists inductive type (existential quantification)
    ///
    /// Exists {α : Sort u} (p : α → Prop) : Prop
    /// inductive Exists {α : Sort u} (p : α → Prop) : Prop where
    ///   | intro (w : α) (h : p w) : Exists p
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.has_exists() == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())`
    /// ENSURES: Adds Exists, Exists.intro, Exists.rec
    pub fn init_exists(&mut self) -> Result<(), EnvError> {
        if self.exists_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

        let exists_const = Expr::const_(Name::from_string("Exists"), vec![Level::param(u.clone())]);

        // Exists : {α : Sort u} → (α → Prop) → Prop
        let exists_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let p_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = c.fresh_local(alpha.clone());
                c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), prop.clone())
            };
            let (p_id, _) = b.fresh_local(p_ty.clone());
            let r = prop.clone();
            let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        // Exists.intro : Π {α : Sort u}, Π (p : α → Prop), Π (w : α), p w → Exists {α} p
        let exists_intro_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let p_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = c.fresh_local(alpha.clone());
                c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), prop.clone())
            };
            let (p_id, p_var) = b.fresh_local(p_ty.clone());
            let (w_id, w_var) = b.fresh_local(alpha.clone());
            let pw = Expr::app(p_var.clone(), w_var);
            let (h_id, _) = b.fresh_local(pw.clone());
            let result = Expr::app(Expr::app(exists_const.clone(), alpha.clone()), p_var);
            let r = result;
            let r = b.mk_pi(h_id, BinderInfo::Default, pw, r);
            let r = b.mk_pi(w_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        let exists_decl = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("Exists"),
                type_: exists_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Exists.intro"),
                    type_: exists_intro_type,
                }],
            }],
        };

        self.add_inductive(exists_decl)?;

        let exists_rec_const = Expr::const_(
            Name::from_string("Exists.rec"),
            vec![Level::param(u.clone())],
        );

        // Exists.elim : {α : Sort u} → {p : α → Prop} → {b : Prop} →
        //               Exists p → (∀ x, p x → b) → b
        let exists_elim_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let p_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = c.fresh_local(alpha.clone());
                c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), prop.clone())
            };
            let (p_id, p_var) = b.fresh_local(p_ty.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone()); // b : Prop
            let exists_p = Expr::app(
                Expr::app(exists_const.clone(), alpha.clone()),
                p_var.clone(),
            );
            let (h1_id, _) = b.fresh_local(exists_p.clone());
            // h2 : ∀ x, p x → b  i.e.  Π (x : α), p x → b
            let h2_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x_var) = c.fresh_local(alpha.clone());
                let px = Expr::app(p_var.clone(), x_var);
                let (px_id, _) = c.fresh_local(px.clone());
                let r = bb_var.clone();
                let r = c.mk_pi(px_id, BinderInfo::Default, px, r);
                c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r)
            };
            let (h2_id, _) = b.fresh_local(h2_ty.clone());
            let r = bb_var;
            let r = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, r);
            let r = b.mk_pi(h1_id, BinderInfo::Default, exists_p, r);
            let r = b.mk_pi(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_pi(p_id, BinderInfo::Implicit, p_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        // Exists.elim value: λ {α} {p} {b} h1 h2, Exists.rec {α} {p} {motive} h2 h1
        let exists_elim_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let p_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _) = c.fresh_local(alpha.clone());
                c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), prop.clone())
            };
            let (p_id, p_var) = b.fresh_local(p_ty.clone());
            let (bb_id, bb_var) = b.fresh_local(prop.clone());
            let exists_p = Expr::app(
                Expr::app(exists_const.clone(), alpha.clone()),
                p_var.clone(),
            );
            let (h1_id, h1_var) = b.fresh_local(exists_p.clone());
            let h2_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x_var) = c.fresh_local(alpha.clone());
                let px = Expr::app(p_var.clone(), x_var);
                let (px_id, _) = c.fresh_local(px.clone());
                let r = bb_var.clone();
                let r = c.mk_pi(px_id, BinderInfo::Default, px, r);
                c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r)
            };
            let (h2_id, h2_var) = b.fresh_local(h2_ty.clone());
            // motive = λ (_ : Exists p), b
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (m_id, _) = c.fresh_local(exists_p.clone());
                c.mk_lam(m_id, BinderInfo::Default, exists_p.clone(), bb_var)
            };
            // Exists.rec {α} {p} {motive} h2 h1
            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(exists_rec_const, alpha.clone()), p_var),
                        motive,
                    ),
                    h2_var,
                ),
                h1_var,
            );
            let r = body;
            let r = b.mk_lam(h2_id, BinderInfo::Default, h2_ty, r);
            let r = b.mk_lam(h1_id, BinderInfo::Default, exists_p.clone(), r);
            let r = b.mk_lam(bb_id, BinderInfo::Implicit, prop.clone(), r);
            let r = b.mk_lam(p_id, BinderInfo::Implicit, p_ty, r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Exists.elim"),
            level_params: vec![u.clone()],
            type_: exists_elim_type,
            value: exists_elim_value,
            is_reducible: true,
        })?;

        // Exists.choose (requires Classical.choice) - we'll add it if Classical is available
        // For now, just the basic Exists and Exists.elim

        self.exists_init = true;
        Ok(())
    }

    /// Check if Exists type has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_exists()` has been called successfully
    /// ENSURES: Pure function - no side effects
    #[cfg(test)]
    pub(crate) fn has_exists(&self) -> bool {
        self.exists_init
    }
}
