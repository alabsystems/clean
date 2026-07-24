// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `Insert` / `Singleton` collection-literal classes (Brick P1 —
//! unregistered prelude heads).
//!
//! Registers the Lean 4 core classes behind the `{a, b, c}` collection
//! literal as fully kernel-checked single-constructor structures (no axioms),
//! their projections, and `List` instances with real `List.cons` bodies:
//!
//! ```text
//! class Insert (α : outParam <| Type u) (γ : Type v) where
//!   insert : α → γ → γ
//! class Singleton (α : outParam <| Type u) (β : Type v) where
//!   singleton : α → β
//! ```
//!
//! Lean sources (toolchain `v4.30.0-rc2`): `Init/Core.lean:590` (`Insert`),
//! `:599` (`Singleton`) — note `α` (the ELEMENT type) is the outParam in
//! both. Lean core ships no `List` instances for these (they live in
//! Mathlib: `Insert α (List α) := ⟨List.cons⟩`,
//! `Singleton α (List α) := ⟨fun x => [x]⟩` — Mathlib.Data.List.Basic); the
//! Clean-native `instInsertList` / `instSingletonList` here mirror those
//! Mathlib bodies so `{1, 2, 3} : List Nat` elaborates end-to-end.
//!
//! Without these heads, `{1,2,3}` (audit row e07 in
//! `docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md`) resolved `insert`/`singleton`
//! via auto-implicit and failed `TooManyArguments { Sort(u) }`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Which of the two collection-literal classes is being built.
#[derive(Clone, Copy)]
enum CollLitShape {
    /// `insert : α → γ → γ`
    Insert,
    /// `singleton : α → β`
    Singleton,
}

impl CollLitShape {
    fn class_name(self) -> &'static str {
        match self {
            CollLitShape::Insert => "Insert",
            CollLitShape::Singleton => "Singleton",
        }
    }

    fn field_name(self) -> &'static str {
        match self {
            CollLitShape::Insert => "insert",
            CollLitShape::Singleton => "singleton",
        }
    }
}

/// `α → γ → γ` (Insert) or `α → β` (Singleton).
fn coll_lit_field_ty(
    parent: &EnvDeclBuilder,
    alpha: &Expr,
    gamma: &Expr,
    shape: CollLitShape,
) -> Expr {
    let mut c = EnvDeclBuilder::child_of(parent);
    let (a_id, _a) = c.fresh_local(alpha.clone());
    let r = match shape {
        CollLitShape::Insert => {
            let (xs_id, _xs) = c.fresh_local(gamma.clone());
            c.mk_pi(xs_id, BinderInfo::Default, gamma.clone(), gamma.clone())
        }
        CollLitShape::Singleton => gamma.clone(),
    };
    let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
    c.finish_child(r)
}

impl Environment {
    /// Register the `Insert` / `Singleton` classes and their
    /// `Insert.insert` / `Singleton.singleton` projections, all as
    /// fully-checked declarations.
    ///
    /// Lean fidelity: `Init/Core.lean:590/599` — two-parameter classes at
    /// `Type (max u v)` whose FIRST parameter (the element type `α`) is the
    /// outParam.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.insert_singleton_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_insert_singleton(&mut self) -> Result<(), EnvError> {
        if self.insert_singleton_init {
            return Ok(());
        }

        for shape in [CollLitShape::Insert, CollLitShape::Singleton] {
            self.init_coll_lit_class(shape)?;
        }

        self.insert_singleton_init = true;
        Ok(())
    }

    fn init_coll_lit_class(&mut self, shape: CollLitShape) -> Result<(), EnvError> {
        let class_name = Name::from_string(shape.class_name());
        let ctor_name = Name::from_string(&format!("{}.mk", shape.class_name()));
        let proj_name =
            Name::from_string(&format!("{}.{}", shape.class_name(), shape.field_name()));

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let type_v = Expr::sort(Level::succ(v_level.clone()));
        // Type (max u v)
        let result_sort = Expr::sort(Level::succ(Level::max(u_level.clone(), v_level.clone())));
        let class_const = Expr::const_(class_name.clone(), vec![u_level, v_level]);

        // <Class>.mk : {α : Type u} → {γ : Type v} → (field : …) → <Class> α γ
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (gamma_id, gamma) = b.fresh_local(type_v.clone());
            let field_ty = coll_lit_field_ty(&b, &alpha, &gamma, shape);
            let (field_id, _) = b.fresh_local(field_ty.clone());
            let class_ty = Expr::apps(class_const.clone(), [alpha.clone(), gamma.clone()]);
            let r = b.mk_pi(field_id, BinderInfo::Default, field_ty, class_ty);
            let r = b.mk_pi(gamma_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_inductive(InductiveDecl {
            level_params: vec![u.clone(), v.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: class_name.clone(),
                type_: Expr::pi(
                    BinderInfo::Default,
                    type_u.clone(),
                    Expr::pi(BinderInfo::Default, type_v.clone(), result_sort),
                ),
                constructors: vec![Constructor {
                    name: ctor_name,
                    type_: ctor_type,
                }],
            }],
        })?;

        self.register_structure_fields(
            class_name.clone(),
            vec![Name::from_string(shape.field_name())],
        )?;

        self.register_class(KernelClassInfo {
            name: class_name.clone(),
            num_params: 2,
            // α — the ELEMENT type — is the outParam (Init/Core.lean:590/599).
            out_params: vec![0],
            semi_out_params: vec![],
        });

        // Projection: <Class>.<field> : {α γ} → [self] → <field type>
        let proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (gamma_id, gamma) = b.fresh_local(type_v.clone());
            let class_ty = Expr::apps(class_const.clone(), [alpha.clone(), gamma.clone()]);
            let (inst_id, _) = b.fresh_local(class_ty.clone());
            let field_ty = coll_lit_field_ty(&b, &alpha, &gamma, shape);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, class_ty, field_ty);
            let r = b.mk_pi(gamma_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        let proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (gamma_id, gamma) = b.fresh_local(type_v.clone());
            let class_ty = Expr::apps(class_const.clone(), [alpha.clone(), gamma.clone()]);
            let (inst_id, inst) = b.fresh_local(class_ty.clone());
            let body = Expr::proj(class_name.clone(), 0, inst);
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, class_ty, body);
            let r = b.mk_lam(gamma_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: proj_name,
            level_params: vec![u, v],
            type_: proj_type,
            value: proj_value,
            is_reducible: true,
        })?;

        Ok(())
    }

    /// Register the parametric `List` instances backing `{a, b, c} : List _`:
    ///
    /// ```text
    /// instInsertList    : {α : Type u} → Insert α (List α)    := ⟨List.cons⟩
    /// instSingletonList : {α : Type u} → Singleton α (List α) := ⟨fun a => List.cons a List.nil⟩
    /// ```
    ///
    /// Checked Definitions built from the `List.cons`/`List.nil` constructors
    /// — no axioms, no sorry. Bodies mirror Mathlib's
    /// `instance : Insert α (List α) := ⟨List.cons⟩` /
    /// `instance : Singleton α (List α) := ⟨fun x => [x]⟩`
    /// (Mathlib.Data.List.Basic; Lean CORE ships no List instances for these
    /// classes).
    ///
    /// IMPORT MODE (`suppress_lossy_structure_stubs`): withheld — these are
    /// Clean-native instance names over classes whose genuine instance web
    /// (Mathlib's) arrives with the imported closure; pre-seeding competing
    /// instances would only pollute the import prelude (same policy as
    /// `instHAppendListList`). The default lane is unchanged.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.list_insert_singleton_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_list_insert_singleton_inst(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.list_insert_singleton_inst_init {
            return Ok(());
        }

        self.init_insert_singleton()?;
        self.init_list()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let uu = vec![u_level.clone(), u_level.clone()];
        let list_const = Expr::const_(Name::from_string("List"), vec![u_level.clone()]);
        let list_cons = Expr::const_(Name::from_string("List.cons"), vec![u_level.clone()]);
        let list_nil = Expr::const_(Name::from_string("List.nil"), vec![u_level.clone()]);

        for shape in [CollLitShape::Insert, CollLitShape::Singleton] {
            let inst_name = format!("inst{}List", shape.class_name());
            let class_const = Expr::const_(Name::from_string(shape.class_name()), uu.clone());
            let class_mk = Expr::const_(
                Name::from_string(&format!("{}.mk", shape.class_name())),
                uu.clone(),
            );

            // {α : Type u} → <Class> α (List α)
            let inst_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let r = Expr::apps(class_const.clone(), [alpha.clone(), list_alpha]);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            // fun {α} => <Class>.mk α (List α) <field>
            let inst_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let field = match shape {
                    // List.cons α : α → List α → List α
                    CollLitShape::Insert => Expr::app(list_cons.clone(), alpha.clone()),
                    // fun (a : α) => List.cons α a (List.nil α)
                    CollLitShape::Singleton => {
                        let mut c = EnvDeclBuilder::child_of(&b);
                        let (a_id, a) = c.fresh_local(alpha.clone());
                        let body = Expr::apps(
                            list_cons.clone(),
                            [alpha.clone(), a, Expr::app(list_nil.clone(), alpha.clone())],
                        );
                        let r = c.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
                        c.finish_child(r)
                    }
                };
                let body = Expr::apps(class_mk.clone(), [alpha.clone(), list_alpha, field]);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string(&inst_name),
                level_params: vec![u.clone()],
                type_: inst_type,
                value: inst_value,
                is_reducible: true,
            })?;

            self.register_instance(KernelInstanceInfo {
                name: Name::from_string(&inst_name),
                class_name: Name::from_string(shape.class_name()),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        self.list_insert_singleton_inst_init = true;
        Ok(())
    }
}
