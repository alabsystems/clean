// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `Functor` type class (Brick P1 — unregistered prelude heads).
//!
//! Registers the Lean 4 core `Functor` class as a fully kernel-checked
//! single-constructor structure (no axioms), its `map`/`mapConst`
//! projections, the `Functor.mapRev` combinator behind `<&>`, and the
//! `Option`/`List` instances:
//!
//! ```text
//! class Functor (f : Type u → Type v) : Type (max (u+1) v) where
//!   map      : {α β : Type u} → (α → β) → f α → f β
//!   mapConst : {α β : Type u} → α → f β → f α
//! ```
//!
//! Lean sources (toolchain `v4.30.0-rc2`):
//! - `Init/Prelude.lean:3746` — `class Functor`
//! - `Init/Control/Basic.lean:65` — `def Functor.mapRev [Functor f] : f α → (α → β) → f β`
//! - `Init/Data/Option/Basic.lean:571` — `instance : Functor Option where map := Option.map`
//! - `Init/Data/List/Control.lean:488` — `instance : Functor List where map := List.map`
//!
//! Without the class head, `<$>`/`<&>` (audit rows a03/a12 in
//! `docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md`) resolved `Functor.map` via
//! auto-implicit and failed with `TooManyArguments { func_type: "Sort(u)" }`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// `map : {α β : Type u} → (α → β) → f α → f β` (field 0 of `Functor`).
fn functor_map_field_ty(parent: &EnvDeclBuilder, type_u: &Expr, f: &Expr) -> Expr {
    let mut c = EnvDeclBuilder::child_of(parent);
    let (alpha_id, alpha) = c.fresh_local(type_u.clone());
    let (beta_id, beta) = c.fresh_local(type_u.clone());
    let g_ty = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
    let (g_id, _g) = c.fresh_local(g_ty.clone());
    let f_alpha = Expr::app(f.clone(), alpha.clone());
    let f_beta = Expr::app(f.clone(), beta.clone());
    let (x_id, _x) = c.fresh_local(f_alpha.clone());
    let r = f_beta;
    let r = c.mk_pi(x_id, BinderInfo::Default, f_alpha, r);
    let r = c.mk_pi(g_id, BinderInfo::Default, g_ty, r);
    let r = c.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), r);
    let r = c.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
    c.finish_child(r)
}

/// `mapConst : {α β : Type u} → α → f β → f α` (field 1 of `Functor`).
fn functor_map_const_field_ty(parent: &EnvDeclBuilder, type_u: &Expr, f: &Expr) -> Expr {
    let mut c = EnvDeclBuilder::child_of(parent);
    let (alpha_id, alpha) = c.fresh_local(type_u.clone());
    let (beta_id, beta) = c.fresh_local(type_u.clone());
    let (a_id, _a) = c.fresh_local(alpha.clone());
    let f_alpha = Expr::app(f.clone(), alpha.clone());
    let f_beta = Expr::app(f.clone(), beta.clone());
    let (v_id, _v) = c.fresh_local(f_beta.clone());
    let r = f_alpha;
    let r = c.mk_pi(v_id, BinderInfo::Default, f_beta, r);
    let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
    let r = c.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), r);
    let r = c.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
    c.finish_child(r)
}

impl Environment {
    /// Register the `Functor` class, its `map`/`mapConst` projections, and
    /// `Functor.mapRev` (the `<&>` head), all as fully-checked declarations.
    ///
    /// Lean fidelity: `Init/Prelude.lean:3746`
    /// `class Functor (f : Type u → Type v) : Type (max (u+1) v)` with fields
    /// `map : {α β : Type u} → (α → β) → f α → f β` and
    /// `mapConst : {α β : Type u} → α → f β → f α` (whose Lean default impl
    /// `Function.comp map (Function.const _)` only affects `where` blocks that
    /// omit the field, not the constructor arity mirrored here);
    /// `Init/Control/Basic.lean:65` `Functor.mapRev := fun a f => f <$> a`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.functor_class_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_functor_class(&mut self) -> Result<(), EnvError> {
        if self.functor_class_init {
            return Ok(());
        }

        let functor_name = Name::from_string("Functor");
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let type_v = Expr::sort(Level::succ(v_level.clone()));
        // f : Type u → Type v
        let m_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone());
        // Type (max (u+1) v)
        let result_sort = Expr::sort(Level::succ(Level::max(
            Level::succ(u_level.clone()),
            v_level.clone(),
        )));
        let functor_const = Expr::const_(functor_name.clone(), vec![u_level.clone(), v_level]);

        // Functor.mk : {f : Type u → Type v} → (map : …) → (mapConst : …) → Functor f
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(m_type.clone());
            let map_ty = functor_map_field_ty(&b, &type_u, &f);
            let (map_id, _) = b.fresh_local(map_ty.clone());
            let map_const_ty = functor_map_const_field_ty(&b, &type_u, &f);
            let (mc_id, _) = b.fresh_local(map_const_ty.clone());
            let class_ty = Expr::app(functor_const.clone(), f.clone());
            let r = b.mk_pi(mc_id, BinderInfo::Default, map_const_ty, class_ty);
            let r = b.mk_pi(map_id, BinderInfo::Default, map_ty, r);
            let r = b.mk_pi(f_id, BinderInfo::Implicit, m_type.clone(), r);
            b.finish(r)
        };

        self.add_inductive(InductiveDecl {
            level_params: vec![u.clone(), v.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: functor_name.clone(),
                // (f : Type u → Type v) → Type (max (u+1) v) — explicit binder,
                // exactly Lean's class-former signature.
                type_: Expr::pi(BinderInfo::Default, m_type.clone(), result_sort),
                constructors: vec![Constructor {
                    name: Name::from_string("Functor.mk"),
                    type_: ctor_type,
                }],
            }],
        })?;

        self.register_structure_fields(
            functor_name.clone(),
            vec![Name::from_string("map"), Name::from_string("mapConst")],
        )?;

        self.register_class(KernelClassInfo {
            name: functor_name.clone(),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // Projections: Functor.map (field 0), Functor.mapConst (field 1).
        for (proj_name, field_idx) in [("Functor.map", 0u32), ("Functor.mapConst", 1u32)] {
            let proj_type = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, f) = b.fresh_local(m_type.clone());
                let class_ty = Expr::app(functor_const.clone(), f.clone());
                let (inst_id, _) = b.fresh_local(class_ty.clone());
                let field_ty = if field_idx == 0 {
                    functor_map_field_ty(&b, &type_u, &f)
                } else {
                    functor_map_const_field_ty(&b, &type_u, &f)
                };
                let r = field_ty;
                let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, class_ty, r);
                let r = b.mk_pi(f_id, BinderInfo::Implicit, m_type.clone(), r);
                b.finish(r)
            };
            let proj_value = {
                let mut b = EnvDeclBuilder::new();
                let (f_id, f) = b.fresh_local(m_type.clone());
                let class_ty = Expr::app(functor_const.clone(), f.clone());
                let (inst_id, inst) = b.fresh_local(class_ty.clone());
                let body = Expr::proj(functor_name.clone(), field_idx, inst);
                let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, class_ty, body);
                let r = b.mk_lam(f_id, BinderInfo::Implicit, m_type.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(proj_name),
                level_params: vec![u.clone(), v.clone()],
                type_: proj_type,
                value: proj_value,
                is_reducible: true,
            })?;
        }

        // Functor.mapRev : {f} → [Functor f] → {α β : Type u} → f α → (α → β) → f β
        //   := fun a f => f <$> a   (Init/Control/Basic.lean:65)
        let map_rev_type = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(m_type.clone());
            let class_ty = Expr::app(functor_const.clone(), f.clone());
            let (inst_id, _) = b.fresh_local(class_ty.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let f_alpha = Expr::app(f.clone(), alpha.clone());
            let f_beta = Expr::app(f.clone(), beta.clone());
            let (x_id, _x) = b.fresh_local(f_alpha.clone());
            let g_ty = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
            let (g_id, _g) = b.fresh_local(g_ty.clone());
            let r = f_beta;
            let r = b.mk_pi(g_id, BinderInfo::Default, g_ty, r);
            let r = b.mk_pi(x_id, BinderInfo::Default, f_alpha, r);
            let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, class_ty, r);
            let r = b.mk_pi(f_id, BinderInfo::Implicit, m_type.clone(), r);
            b.finish(r)
        };
        let map_rev_value = {
            let map_const = Expr::const_(
                Name::from_string("Functor.map"),
                vec![Level::param(u.clone()), Level::param(v.clone())],
            );
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(m_type.clone());
            let class_ty = Expr::app(functor_const.clone(), f.clone());
            let (inst_id, inst) = b.fresh_local(class_ty.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let f_alpha = Expr::app(f.clone(), alpha.clone());
            let (x_id, x) = b.fresh_local(f_alpha.clone());
            let g_ty = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
            let (g_id, g) = b.fresh_local(g_ty.clone());
            // Functor.map f inst α β g x
            let body = Expr::apps(
                map_const,
                [f.clone(), inst, alpha.clone(), beta.clone(), g, x],
            );
            let r = b.mk_lam(g_id, BinderInfo::Default, g_ty, body);
            let r = b.mk_lam(x_id, BinderInfo::Default, f_alpha, r);
            let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, class_ty, r);
            let r = b.mk_lam(f_id, BinderInfo::Implicit, m_type.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("Functor.mapRev"),
            level_params: vec![u, v],
            type_: map_rev_type,
            value: map_rev_value,
            is_reducible: true,
        })?;

        self.functor_class_init = true;
        Ok(())
    }

    /// Register `instFunctorOption : Functor Option` and
    /// `instFunctorList : Functor List` (checked Definitions with REAL map
    /// bodies — `Option.map` / `List.map` — no axioms, no sorry).
    ///
    /// Lean fidelity: `Init/Data/Option/Basic.lean:571` and
    /// `Init/Data/List/Control.lean:488`. The `mapConst` field uses Lean's
    /// omitted-field default semantics (`Function.comp map (Function.const _)`)
    /// spelled as the beta-equivalent explicit lambda
    /// `fun a v => map (fun _ => a) v`, since Clean's prelude does not carry
    /// `Function.comp`/`Function.const`.
    ///
    /// IMPORT MODE (`suppress_lossy_structure_stubs`): these carry the genuine
    /// upstream instance NAMES but a Clean-native `mapConst` value spelling, so
    /// pre-seeding them would make the import dedup filter DROP the genuine
    /// olean values (same masking class as the `Nat.min` overlay — see
    /// `init_prelude_core`). They also wrap `List.map`, which the import
    /// prelude suppresses. Withheld in import mode so the genuine instances
    /// flow through the checked import path; the default proof-execution lane
    /// is unchanged.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.functor_instances_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_functor_instances(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.functor_instances_init {
            return Ok(());
        }

        self.init_functor_class()?;
        self.init_option()?;
        self.init_option_ops()?; // Option.map
        self.init_list()?;
        self.init_list_ops()?; // List.map

        for (inst_name, carrier, map_op) in [
            ("instFunctorOption", "Option", "Option.map"),
            ("instFunctorList", "List", "List.map"),
        ] {
            self.add_mono_functor_instance(inst_name, carrier, map_op)?;
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string(inst_name),
                class_name: Name::from_string("Functor"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        self.functor_instances_init = true;
        Ok(())
    }

    /// Build `inst : Functor.{u,u} C := Functor.mk C C.map (fun a v => C.map (fun _ => a) v)`
    /// for a unary type constructor `C : Type u → Type u` whose `map` op has
    /// Lean's two-universe `{α : Type u} → {β : Type v} → (α → β) → C α → C β`
    /// signature (instantiated here at `{u, u}`).
    fn add_mono_functor_instance(
        &mut self,
        inst_name: &str,
        carrier_name: &str,
        map_op_name: &str,
    ) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let carrier = Expr::const_(Name::from_string(carrier_name), vec![u_level.clone()]);
        // Option.map / List.map are two-universe (u, v); the Functor field is
        // homogeneous in `Type u`, so instantiate both at `u`.
        let map_op = Expr::const_(
            Name::from_string(map_op_name),
            vec![u_level.clone(), u_level.clone()],
        );
        let functor_levels = vec![u_level.clone(), u_level.clone()];
        let functor_const = Expr::const_(Name::from_string("Functor"), functor_levels.clone());
        let functor_mk = Expr::const_(Name::from_string("Functor.mk"), functor_levels);

        let inst_type = Expr::app(functor_const, carrier.clone());

        // mapConst : {α β : Type u} → α → C β → C α
        //   := fun {α β} (a : α) (v : C β) => C.map β α (fun _ : β => a) v
        let map_const_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let c_beta = Expr::app(carrier.clone(), beta.clone());
            let (v_id, v) = b.fresh_local(c_beta.clone());
            let const_fun = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(beta.clone());
                let r = c.mk_lam(w_id, BinderInfo::Default, beta.clone(), a.clone());
                c.finish_child(r)
            };
            let body = Expr::apps(map_op.clone(), [beta.clone(), alpha.clone(), const_fun, v]);
            let r = b.mk_lam(v_id, BinderInfo::Default, c_beta, body);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let inst_value = Expr::apps(functor_mk, [carrier, map_op, map_const_value]);

        self.add_decl(Declaration::Definition {
            name: Name::from_string(inst_name),
            level_params: vec![u],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        Ok(())
    }
}
