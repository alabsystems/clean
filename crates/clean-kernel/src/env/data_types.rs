// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fundamental algebraic data type initialization: Option, Sum, PSum, PSigma, Empty, PEmpty
//!
//! Numeric types (Bool, Nat, Int) are in `data_types_nat`.
//! Collection types (ULift, Char, List, String) are in `data_types_collections`.
//! Arithmetic operations and lemmas are in `data_types_arithmetic`.
//! UInt/Float/USize types are in `data_types_uint`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Option inductive type
    ///
    /// inductive Option (α : Sort u) : Sort u where
    ///   | none : Option α
    ///   | some (a : α) : Option α
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.option_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_option(&mut self) -> Result<(), EnvError> {
        if self.option_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));

        // Option : Sort u → Sort u (Type u)
        let option_type = Expr::pi(BinderInfo::Implicit, sort_u.clone(), sort_u.clone());

        let option_const = Expr::const_(Name::from_string("Option"), vec![Level::param(u.clone())]);

        // Option.none : {α : Sort u} → Option α
        // Built with EnvDeclBuilder (#1444)
        let option_none_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let body = Expr::app(option_const.clone(), alpha);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), body);
            b.finish(e)
        };

        // Option.some : {α : Sort u} → α → Option α
        // Built with EnvDeclBuilder (#1444)
        let option_some_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let body = Expr::app(option_const.clone(), alpha.clone());
            let e = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        let option_decl = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Option"),
                type_: option_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Option.none"),
                        type_: option_none_type,
                    },
                    Constructor {
                        name: Name::from_string("Option.some"),
                        type_: option_some_type,
                    },
                ],
            }],
        };

        self.add_inductive(option_decl)?;
        self.option_init = true;
        Ok(())
    }

    /// Check if Option has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_option` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_option(&self) -> bool {
        self.option_init
    }

    /// Initialize Sum disjoint union type
    ///
    /// Sum : Type u → Type v → Type (max u v)
    /// inductive Sum (α : Type u) (β : Type v) where
    ///   | inl (val : α) : Sum α β
    ///   | inr (val : β) : Sum α β
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.sum_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_sum(&mut self) -> Result<(), EnvError> {
        if self.sum_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let v = Name::from_string("v");

        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(v.clone()))));
        let result_sort = Expr::from_kind(ExprKind::Sort(Level::max(
            Level::succ(Level::param(u.clone())),
            Level::succ(Level::param(v.clone())),
        )));

        // Sum : Type u → Type v → Type (max u v)
        let sum_type = Expr::pi(
            BinderInfo::Default,
            type_u.clone(),
            Expr::pi(BinderInfo::Default, type_v.clone(), result_sort.clone()),
        );

        let sum_const = Expr::const_(
            Name::from_string("Sum"),
            vec![Level::param(u.clone()), Level::param(v.clone())],
        );

        // Sum.inl : {α : Type u} → {β : Type v} → α → Sum α β
        // Built with EnvDeclBuilder (#1444)
        let sum_inl_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let body = Expr::app(Expr::app(sum_const.clone(), alpha.clone()), beta.clone());
            let e = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // Sum.inr : {α : Type u} → {β : Type v} → β → Sum α β
        // Built with EnvDeclBuilder (#1444)
        let sum_inr_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let (val_id, _val) = b.fresh_local(beta.clone());
            let body = Expr::app(Expr::app(sum_const.clone(), alpha.clone()), beta.clone());
            let e = b.mk_pi(val_id, BinderInfo::Default, beta.clone(), body);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let sum_decl = InductiveDecl {
            level_params: vec![u.clone(), v.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("Sum"),
                type_: sum_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Sum.inl"),
                        type_: sum_inl_type,
                    },
                    Constructor {
                        name: Name::from_string("Sum.inr"),
                        type_: sum_inr_type,
                    },
                ],
            }],
        };

        self.add_inductive(sum_decl)?;
        self.sum_init = true;
        Ok(())
    }

    /// Check if Sum has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_sum` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_sum(&self) -> bool {
        self.sum_init
    }

    /// Initialize PSum (universe-polymorphic disjoint union)
    ///
    /// PSum : Sort u → Sort v → Sort (max (max 1 u) v)
    /// inductive PSum (α : Sort u) (β : Sort v) where
    ///   | inl (val : α) : PSum α β
    ///   | inr (val : β) : PSum α β
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.psum_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_psum(&mut self) -> Result<(), EnvError> {
        if self.psum_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let v = Name::from_string("v");

        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));
        let result_sort = Expr::from_kind(ExprKind::Sort(Level::max(
            Level::max(Level::succ(Level::zero()), Level::param(u.clone())),
            Level::param(v.clone()),
        )));

        // PSum : Sort u → Sort v → Sort (max (max 1 u) v)
        let psum_type = Expr::pi(
            BinderInfo::Default,
            sort_u.clone(),
            Expr::pi(BinderInfo::Default, sort_v.clone(), result_sort.clone()),
        );

        let psum_const = Expr::const_(
            Name::from_string("PSum"),
            vec![Level::param(u.clone()), Level::param(v.clone())],
        );

        // PSum.inl : {α : Sort u} → {β : Sort v} → α → PSum α β
        // Built with EnvDeclBuilder (#1444)
        let psum_inl_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let body = Expr::app(Expr::app(psum_const.clone(), alpha.clone()), beta.clone());
            let e = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        // PSum.inr : {α : Sort u} → {β : Sort v} → β → PSum α β
        // Built with EnvDeclBuilder (#1444)
        let psum_inr_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let (val_id, _val) = b.fresh_local(beta.clone());
            let body = Expr::app(Expr::app(psum_const.clone(), alpha.clone()), beta.clone());
            let e = b.mk_pi(val_id, BinderInfo::Default, beta.clone(), body);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        let psum_decl = InductiveDecl {
            level_params: vec![u.clone(), v.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("PSum"),
                type_: psum_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("PSum.inl"),
                        type_: psum_inl_type,
                    },
                    Constructor {
                        name: Name::from_string("PSum.inr"),
                        type_: psum_inr_type,
                    },
                ],
            }],
        };

        self.add_inductive(psum_decl)?;
        self.psum_init = true;
        Ok(())
    }

    /// Check if PSum has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_psum` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_psum(&self) -> bool {
        self.psum_init
    }

    /// Initialize PSigma (universe-polymorphic dependent pair)
    ///
    /// structure PSigma {α : Sort u} (β : α → Sort v) : Sort (max (max 1 u) v) where
    ///   fst : α
    ///   snd : β fst
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.psigma_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_psigma(&mut self) -> Result<(), EnvError> {
        if self.psigma_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let v = Name::from_string("v");

        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));
        let result_sort = Expr::from_kind(ExprKind::Sort(Level::max(
            Level::max(Level::succ(Level::zero()), Level::param(u.clone())),
            Level::param(v.clone()),
        )));

        let psigma_const = Expr::const_(
            Name::from_string("PSigma"),
            vec![Level::param(u.clone()), Level::param(v.clone())],
        );

        // PSigma : {α : Sort u} → (α → Sort v) → Sort (max (max 1 u) v)
        let psigma_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let beta_ty = Expr::pi(BinderInfo::Default, alpha.clone(), sort_v.clone());
            let (beta_id, _beta) = b.fresh_local(beta_ty.clone());
            let e = b.mk_pi(beta_id, BinderInfo::Default, beta_ty, result_sort.clone());
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        // PSigma.mk : {α : Sort u} → {β : α → Sort v} → (a : α) → β a → PSigma β
        //
        // Lean fidelity (`Init/Core.lean:301` structure PSigma, oracle
        // `#check @PSigma.mk` on v4.30.0-rc2): BOTH structure parameters are
        // implicit in the constructor — `{α}` AND `{β}`. β was previously
        // registered as an explicit binder, which mis-slots the first explicit
        // operand of any plain `PSigma.mk`/anonymous-constructor application
        // (same defect as `Sigma.mk`, audit rows e08/e09).
        let psigma_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) =
                b.fresh_local(Expr::pi(BinderInfo::Default, alpha.clone(), sort_v.clone()));
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (ba_id, _ba) = b.fresh_local(Expr::app(beta.clone(), a.clone()));
            let body = Expr::app(Expr::app(psigma_const.clone(), alpha.clone()), beta.clone());
            let e = b.mk_pi(
                ba_id,
                BinderInfo::Default,
                Expr::app(beta.clone(), a.clone()),
                body,
            );
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(
                beta_id,
                BinderInfo::Implicit,
                Expr::pi(BinderInfo::Default, alpha.clone(), sort_v.clone()),
                e,
            );
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        let psigma_decl = InductiveDecl {
            level_params: vec![u.clone(), v.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("PSigma"),
                type_: psigma_type,
                constructors: vec![Constructor {
                    name: Name::from_string("PSigma.mk"),
                    type_: psigma_mk_type,
                }],
            }],
        };

        self.add_inductive(psigma_decl)?;

        // PSigma.fst : {α : Sort u} {β : α → Sort v} → PSigma β → α
        let psigma_fst_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let beta_ty = Expr::pi(BinderInfo::Default, alpha.clone(), sort_v.clone());
            let (beta_id, beta) = b.fresh_local(beta_ty.clone());
            let psigma_app =
                Expr::app(Expr::app(psigma_const.clone(), alpha.clone()), beta.clone());
            let (p_id, _p) = b.fresh_local(psigma_app.clone());
            let e = b.mk_pi(p_id, BinderInfo::Default, psigma_app, alpha.clone());
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, beta_ty, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        // Value: fun {α} {β} (p : PSigma α β) => Expr.proj("PSigma", 0, p)
        let psigma_fst_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let beta_ty = Expr::pi(BinderInfo::Default, alpha.clone(), sort_v.clone());
            let (beta_id, beta) = b.fresh_local(beta_ty.clone());
            let psigma_app =
                Expr::app(Expr::app(psigma_const.clone(), alpha.clone()), beta.clone());
            let (p_id, p) = b.fresh_local(psigma_app.clone());
            let body = Expr::proj(Name::from_string("PSigma"), 0, p);
            let e = b.mk_lam(p_id, BinderInfo::Default, psigma_app, body);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, beta_ty, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("PSigma.fst"),
            level_params: vec![u.clone(), v.clone()],
            type_: psigma_fst_type,
            value: psigma_fst_value,
            is_reducible: true,
        })?;

        let psigma_fst_const = Expr::const_(
            Name::from_string("PSigma.fst"),
            vec![Level::param(u.clone()), Level::param(v.clone())],
        );

        // PSigma.snd : {α : Sort u} {β : α → Sort v} → (p : PSigma β) → β p.fst
        let psigma_snd_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let beta_ty = Expr::pi(BinderInfo::Default, alpha.clone(), sort_v.clone());
            let (beta_id, beta) = b.fresh_local(beta_ty.clone());
            let psigma_app =
                Expr::app(Expr::app(psigma_const.clone(), alpha.clone()), beta.clone());
            let (p_id, p) = b.fresh_local(psigma_app.clone());
            let p_fst = Expr::apps(psigma_fst_const.clone(), [alpha.clone(), beta.clone(), p]);
            let body = Expr::app(beta.clone(), p_fst);
            let e = b.mk_pi(p_id, BinderInfo::Default, psigma_app, body);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, beta_ty, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        // Value: fun {α} {β} (p : PSigma α β) => Expr.proj("PSigma", 1, p)
        let psigma_snd_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let beta_ty = Expr::pi(BinderInfo::Default, alpha.clone(), sort_v.clone());
            let (beta_id, beta) = b.fresh_local(beta_ty.clone());
            let psigma_app =
                Expr::app(Expr::app(psigma_const.clone(), alpha.clone()), beta.clone());
            let (p_id, p) = b.fresh_local(psigma_app.clone());
            let body = Expr::proj(Name::from_string("PSigma"), 1, p);
            let e = b.mk_lam(p_id, BinderInfo::Default, psigma_app, body);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, beta_ty, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("PSigma.snd"),
            level_params: vec![u.clone(), v.clone()],
            type_: psigma_snd_type,
            value: psigma_snd_value,
            is_reducible: true,
        })?;

        // Register structure fields
        self.register_structure_fields(
            Name::from_string("PSigma"),
            vec![Name::from_string("fst"), Name::from_string("snd")],
        )?;

        self.psigma_init = true;
        Ok(())
    }

    /// Check if PSigma has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_psigma` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_psigma(&self) -> bool {
        self.psigma_init
    }

    /// Initialize Empty type (uninhabited type at Type level)
    ///
    /// inductive Empty : Type where
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.empty_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_empty(&mut self) -> Result<(), EnvError> {
        if self.empty_init {
            return Ok(());
        }

        // Empty : Type
        let empty_type = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        let empty_decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("Empty"),
                type_: empty_type,
                constructors: vec![], // No constructors - uninhabited
            }],
        };

        self.add_inductive(empty_decl)?;

        // Add Empty.elim : {C : Sort u} → Empty → C
        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

        let empty_const = Expr::const_(Name::from_string("Empty"), vec![]);

        // Built with EnvDeclBuilder (#1444)
        let empty_elim_type = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(sort_u.clone());
            let (e_id, _e) = b.fresh_local(empty_const.clone());
            let e = b.mk_pi(e_id, BinderInfo::Default, empty_const.clone(), c.clone());
            let e = b.mk_pi(c_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        // Value: fun {C} e => Empty.rec (fun _ => C) e
        // Built with EnvDeclBuilder (#1444)
        let empty_rec_const = Expr::const_(
            Name::from_string("Empty.rec"),
            vec![Level::param(u.clone())],
        );

        let empty_elim_value = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(sort_u.clone());
            let (e_id, e_var) = b.fresh_local(empty_const.clone());
            // motive: fun _ : Empty => C
            let (dummy_id, _dummy) = b.fresh_local(empty_const.clone());
            let motive = b.mk_lam(
                dummy_id,
                BinderInfo::Default,
                empty_const.clone(),
                c.clone(),
            );
            let body = Expr::app(Expr::app(empty_rec_const.clone(), motive), e_var);
            let e = b.mk_lam(e_id, BinderInfo::Default, empty_const.clone(), body);
            let e = b.mk_lam(c_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Empty.elim"),
            level_params: vec![u.clone()],
            type_: empty_elim_type,
            value: empty_elim_value,
            is_reducible: true,
        })?;

        self.empty_init = true;
        Ok(())
    }

    /// Check if Empty has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_empty` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_empty(&self) -> bool {
        self.empty_init
    }

    /// Initialize PEmpty type (universe-polymorphic uninhabited type)
    ///
    /// inductive PEmpty : Sort u where
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.pempty_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_pempty(&mut self) -> Result<(), EnvError> {
        if self.pempty_init {
            return Ok(());
        }
        // PEmpty.elim's Lean-faithful value references False/False.elim
        // (idempotent dependency init, same convention as init_ordering in
        // data_typeclasses).
        self.init_true_false()?;

        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));

        // PEmpty : Sort u
        let pempty_type = sort_u.clone();

        let pempty_decl = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 0,
            types: vec![InductiveType {
                name: Name::from_string("PEmpty"),
                type_: pempty_type,
                constructors: vec![], // No constructors - uninhabited
            }],
        };

        self.add_inductive(pempty_decl)?;

        // Add PEmpty.elim : {C : Sort v} → PEmpty → C
        let v = Name::from_string("v");
        let sort_v = Expr::from_kind(ExprKind::Sort(Level::param(v.clone())));

        let pempty_const = Expr::const_(Name::from_string("PEmpty"), vec![Level::param(u.clone())]);

        // Built with EnvDeclBuilder (#1444)
        let pempty_elim_type = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(sort_v.clone());
            let (e_id, _e) = b.fresh_local(pempty_const.clone());
            let e = b.mk_pi(e_id, BinderInfo::Default, pempty_const.clone(), c.clone());
            let e = b.mk_pi(c_id, BinderInfo::Implicit, sort_v.clone(), e);
            b.finish(e)
        };

        // Value: fun {C} a => False.elim (PEmpty.rec (fun _ => False) a)
        //
        // FIDELITY (v4.30 matcher compilation): Lean compiles
        // `def PEmpty.elim {C : Sort _} : PEmpty → C := fun a => nomatch a` to
        // `fun {C} a => PEmpty.elim.match_1 (fun _ => C) a` with
        // `match_1 := fun motive a => False.elim (motive a)
        //             (PEmpty.casesOn (fun _ => False) a)` — the stuck head is
        // False.rec, NOT PEmpty.rec. The old direct spelling
        // `fun {C} e => PEmpty.rec (fun _ => C) e` is only PROPOSITIONALLY equal
        // (empty scrutinee), never kernel-defeq with a free scrutinee, so the
        // olean twin failed the value-defeq dedup (census root: Init.Core).
        // This delta-normal form of Lean's value closes under match_1/casesOn
        // delta + beta.
        // Built with EnvDeclBuilder (#1444)
        let pempty_rec_prop_const = Expr::const_(
            Name::from_string("PEmpty.rec"),
            vec![Level::zero(), Level::param(u.clone())],
        );
        let false_elim_const = Expr::const_(
            Name::from_string("False.elim"),
            vec![Level::param(v.clone())],
        );
        let false_const = Expr::const_(Name::from_string("False"), vec![]);

        let pempty_elim_value = {
            let mut b = EnvDeclBuilder::new();
            let (c_id, c) = b.fresh_local(sort_v.clone());
            let (e_id, e_var) = b.fresh_local(pempty_const.clone());
            let (dummy_id, _dummy) = b.fresh_local(pempty_const.clone());
            let motive = b.mk_lam(
                dummy_id,
                BinderInfo::Default,
                pempty_const.clone(),
                false_const.clone(),
            );
            let absurd = Expr::app(Expr::app(pempty_rec_prop_const.clone(), motive), e_var);
            let body = Expr::app(Expr::app(false_elim_const.clone(), c.clone()), absurd);
            let e = b.mk_lam(e_id, BinderInfo::Default, pempty_const.clone(), body);
            let e = b.mk_lam(c_id, BinderInfo::Implicit, sort_v.clone(), e);
            b.finish(e)
        };

        // FIDELITY: Lean's real `PEmpty.elim` (Init/Core.lean:58,
        // `def PEmpty.elim {C : Sort _} : PEmpty → C := fun a => nomatch a`)
        // elaborates to `PEmpty.elim.{u_1, u_2} : {C : Sort u_1} → PEmpty.{u_2} → C`
        // — level params in ORDER OF FIRST APPEARANCE in the signature: `C`'s
        // universe (`Sort u_1`) FIRST, then `PEmpty`'s universe (`PEmpty.{u_2}`).
        // Applications supply level args in that order, e.g. `PEmpty.elim.{S w, S u}`
        // inside `FirstOrder.Language.funMap₂` (C = M : Type w, PEmpty : Type u) and
        // `PEmpty.elim.{S 0, S v}` inside `RelMap₂`. Here `v` is C's universe and `u`
        // is PEmpty's, so the param LIST must be `[v, u]` (C-univ first, PEmpty-univ
        // second) for those applications to bind `C ↦ S w / S 0` and `PEmpty ↦ S u /
        // S v` correctly. The previous `[u, v]` bound them REVERSED, yielding a
        // `Sort(Succ u)` vs `Sort(Succ w)` / `Sort(Succ v)` vs `Sort(Succ 0)`
        // TypeMismatch on the `mk₂`-family FirstOrder decls (`funMap₂`, `RelMap₂`,
        // `subsingleton_mk₂_functions`, `subsingleton_mk₂_relations`). The
        // type/value EXPRESSIONS are unchanged — only the param LIST order matters,
        // exactly as with the `Prod.swap` fidelity fix. No kernel/defeq change.
        self.add_decl(Declaration::Definition {
            name: Name::from_string("PEmpty.elim"),
            level_params: vec![v.clone(), u.clone()],
            type_: pempty_elim_type,
            value: pempty_elim_value,
            is_reducible: true,
        })?;

        self.pempty_init = true;
        Ok(())
    }

    /// Check if PEmpty has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_pempty` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_pempty(&self) -> bool {
        self.pempty_init
    }
}
