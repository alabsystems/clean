// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Repr and ToString typeclass initialization for Environment.
//!
//! This module bootstraps the `Repr` and `ToString` typeclasses into the
//! prelude so that explicit `instance : Repr X` / `instance : ToString X`
//! declarations (and `deriving Repr`) resolve the class name to a real
//! environment constant instead of falling back to an auto-implicit fvar of
//! type `Sort u_0` (which then over-applies and raises `TooManyArguments`).
//!
//! Both classes are modelled with `String`-valued fields — matching the
//! `derive_repr_ext` handler, which emits `Repr.mk (fun _ _ => "<TypeName>")`
//! of type `α → Nat → String`.  All registered terms are axiom-free
//! `Declaration::Definition`s built from the class recursor, mirroring the
//! `BEq` / `Hashable` bootstrap pattern.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, LEAN_DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the `Repr` typeclass.
    ///
    /// ```lean
    /// class Repr (α : Type u) where
    ///   reprPrec : α → Nat → String
    /// ```
    ///
    /// Also registers the `repr` convenience function
    /// (`repr a := Repr.reprPrec a 0`) and core instances for `Nat`, `String`,
    /// `Bool`, `Int`, and `List`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.repr_init == true`
    /// ENSURES: On success, required dependencies (`nat`, `string`, `bool`, `int`, `list`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_repr(&mut self) -> Result<(), EnvError> {
        if self.repr_init {
            return Ok(());
        }

        // Dependencies.
        self.init_nat()?;
        self.init_string()?;
        self.init_bool()?;
        self.init_int()?;
        self.init_list()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let string_const = Expr::const_(Name::from_string("String"), vec![]);

        let repr_const = |u: Level| Expr::const_(Name::from_string("Repr"), vec![u]);

        // `α → Nat → String`
        let mk_repr_fn_ty = |b: &EnvDeclBuilder, alpha: &Expr| {
            let mut c = EnvDeclBuilder::child_of(b);
            let (x_id, _x) = c.fresh_local(alpha.clone());
            let (n_id, _n) = c.fresh_local(nat_const.clone());
            let r = string_const.clone();
            let r = c.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
            let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
            c.finish_child(r)
        };

        // Repr : Type u → Type u
        let repr_type = Expr::pi(
            BinderInfo::Implicit,
            type_u.clone(),
            Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))),
        );

        // Repr.mk : {α : Type u} → (α → Nat → String) → Repr α
        let repr_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let fn_ty = mk_repr_fn_ty(&b, &alpha);
            let (f_id, _f) = b.fresh_local(fn_ty.clone());
            let r = Expr::app(repr_const(u_level.clone()), alpha.clone());
            let r = b.mk_pi(f_id, BinderInfo::Default, fn_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let repr_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Repr"),
                type_: repr_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Repr.mk"),
                    type_: repr_mk_type,
                }],
            }],
        };

        self.add_inductive(repr_ind)?;
        self.register_structure_fields(
            Name::from_string("Repr"),
            vec![Name::from_string("reprPrec")],
        )?;
        self.register_class(KernelClassInfo {
            name: Name::from_string("Repr"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // Repr.reprPrec : {α : Type u} → [inst : Repr α] → α → Nat → String
        let reprprec_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let repr_alpha = Expr::app(repr_const(u_level.clone()), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(repr_alpha.clone());
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let (n_id, _n) = b.fresh_local(nat_const.clone());
            let r = string_const.clone();
            let r = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, repr_alpha, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let repr_rec =
            |u1: Level, u2: Level| Expr::const_(Name::from_string("Repr.rec"), vec![u1, u2]);

        // Repr.reprPrec value: λ {α} [inst] (a : α) (n : Nat) =>
        //   (Repr.rec α motive minor inst) a n
        let reprprec_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let repr_alpha = Expr::app(repr_const(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(repr_alpha.clone());
            let (a_id, a_var) = b.fresh_local(alpha.clone());
            let (n_id, n_var) = b.fresh_local(nat_const.clone());

            // Motive: λ (_ : Repr α) => α → Nat → String
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(repr_alpha.clone());
                let inner = mk_repr_fn_ty(&c, &alpha);
                let r = c.mk_lam(w_id, BinderInfo::Default, repr_alpha.clone(), inner);
                c.finish_child(r)
            };

            // Minor: λ (f : α → Nat → String) => f
            let minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let fn_ty = mk_repr_fn_ty(&c, &alpha);
                let (f_id, f) = c.fresh_local(fn_ty.clone());
                let r = c.mk_lam(f_id, BinderInfo::Default, fn_ty, f);
                c.finish_child(r)
            };

            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                repr_rec(Level::succ(u_level.clone()), u_level.clone()),
                                alpha.clone(),
                            ),
                            motive,
                        ),
                        minor,
                    ),
                    inst,
                ),
                a_var,
            );
            let body = Expr::app(body, n_var);
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, repr_alpha, r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Repr.reprPrec"),
            level_params: vec![u.clone()],
            type_: reprprec_type,
            value: reprprec_value,
            is_reducible: true,
        })?;

        // repr : {α : Type u} → [inst : Repr α] → α → String
        //   := λ {α} [inst] (a : α) => Repr.reprPrec a 0
        let repr_type_def = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let repr_alpha = Expr::app(repr_const(u_level.clone()), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(repr_alpha.clone());
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let r = string_const.clone();
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, repr_alpha, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let repr_value_def = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let repr_alpha = Expr::app(repr_const(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(repr_alpha.clone());
            let (a_id, a_var) = b.fresh_local(alpha.clone());
            // Repr.reprPrec α inst a 0
            let reprprec = Expr::const_(Name::from_string("Repr.reprPrec"), vec![u_level.clone()]);
            let body = Expr::app(
                Expr::app(Expr::app(Expr::app(reprprec, alpha.clone()), inst), a_var),
                nat_zero.clone(),
            );
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, repr_alpha, r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("repr"),
            level_params: vec![u.clone()],
            type_: repr_type_def,
            value: repr_value_def,
            is_reducible: true,
        })?;

        // Core instances. The `reprPrec` bodies are placeholder String values;
        // they are sound (well-typed, axiom-free) and exist solely so instance
        // synthesis can satisfy `[Repr Nat]` / `[Repr (List α)]` etc. during
        // elaboration of explicit `Repr` instances.
        self.add_repr_const_instance("instReprNat", &nat_const, Level::zero())?;
        self.add_repr_const_instance("instReprString", &string_const, Level::zero())?;
        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
        self.add_repr_const_instance("instReprBool", &bool_const, Level::zero())?;
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        self.add_repr_const_instance("instReprInt", &int_const, Level::zero())?;

        // instReprList : {α : Type u} → [Repr α] → Repr (List α)
        self.add_repr_list_instance(&u, &u_level, &type_u)?;

        self.repr_init = true;
        Ok(())
    }

    /// Register a `Repr T` instance for a closed type `T` with the placeholder
    /// `reprPrec := fun _ _ => ""` body.
    fn add_repr_const_instance(
        &mut self,
        inst_name: &str,
        ty: &Expr,
        level: Level,
    ) -> Result<(), EnvError> {
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let repr_ty = Expr::app(
            Expr::const_(Name::from_string("Repr"), vec![level.clone()]),
            ty.clone(),
        );
        // fun (_ : T) (_ : Nat) => ""
        let reprprec_fn = {
            let mut b = EnvDeclBuilder::new();
            let (x_id, _x) = b.fresh_local(ty.clone());
            let (n_id, _n) = b.fresh_local(nat_const.clone());
            let body = Expr::str_lit("");
            let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
            let r = b.mk_lam(x_id, BinderInfo::Default, ty.clone(), r);
            b.finish(r)
        };
        let value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Repr.mk"), vec![level]),
                ty.clone(),
            ),
            reprprec_fn,
        );
        self.add_decl(Declaration::Definition {
            name: Name::from_string(inst_name),
            level_params: vec![],
            type_: repr_ty,
            value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string(inst_name),
            class_name: Name::from_string("Repr"),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Register `instReprList : {α : Type u} → [Repr α] → Repr (List α)`.
    /// The `reprPrec` body is the placeholder `fun _ _ => ""`.
    fn add_repr_list_instance(
        &mut self,
        u: &Name,
        u_level: &Level,
        type_u: &Expr,
    ) -> Result<(), EnvError> {
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let string_const = Expr::const_(Name::from_string("String"), vec![]);
        let repr_const = |u: Level| Expr::const_(Name::from_string("Repr"), vec![u]);
        let list_const = |u: Level| Expr::const_(Name::from_string("List"), vec![u]);

        // {α : Type u} → [inst : Repr α] → Repr (List α)
        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let repr_alpha = Expr::app(repr_const(u_level.clone()), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(repr_alpha.clone());
            let list_alpha = Expr::app(list_const(u_level.clone()), alpha.clone());
            let r = Expr::app(repr_const(u_level.clone()), list_alpha);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, repr_alpha, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let repr_alpha = Expr::app(repr_const(u_level.clone()), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(repr_alpha.clone());
            let list_alpha = Expr::app(list_const(u_level.clone()), alpha.clone());

            // fun (_ : List α) (_ : Nat) => ""
            let reprprec_fn = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(list_alpha.clone());
                let (n_id, _n) = c.fresh_local(nat_const.clone());
                let body = Expr::str_lit("");
                let r = c.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body);
                let r = c.mk_lam(x_id, BinderInfo::Default, list_alpha.clone(), r);
                c.finish_child(r)
            };
            let _ = string_const;

            let body = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Repr.mk"), vec![u_level.clone()]),
                    list_alpha,
                ),
                reprprec_fn,
            );
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, repr_alpha, body);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instReprList"),
            level_params: vec![u.clone()],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instReprList"),
            class_name: Name::from_string("Repr"),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Initialize the `ToString` typeclass.
    ///
    /// ```lean
    /// class ToString (α : Type u) where
    ///   toString : α → String
    /// ```
    ///
    /// Also registers the `toString` convenience function and core instances
    /// for `Nat`, `String`, and `Bool`.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.to_string_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_to_string(&mut self) -> Result<(), EnvError> {
        if self.to_string_init {
            return Ok(());
        }

        self.init_nat()?;
        self.init_string()?;
        self.init_bool()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let string_const = Expr::const_(Name::from_string("String"), vec![]);

        let tostring_const = |u: Level| Expr::const_(Name::from_string("ToString"), vec![u]);

        // ToString : Type u → Type u
        let tostring_type = Expr::pi(
            BinderInfo::Implicit,
            type_u.clone(),
            Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone()))),
        );

        // ToString.mk : {α : Type u} → (α → String) → ToString α
        let tostring_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let fn_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(alpha.clone());
                let r = string_const.clone();
                let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (f_id, _f) = b.fresh_local(fn_ty.clone());
            let r = Expr::app(tostring_const(u_level.clone()), alpha.clone());
            let r = b.mk_pi(f_id, BinderInfo::Default, fn_ty, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let tostring_ind = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("ToString"),
                type_: tostring_type,
                constructors: vec![Constructor {
                    name: Name::from_string("ToString.mk"),
                    type_: tostring_mk_type,
                }],
            }],
        };

        self.add_inductive(tostring_ind)?;
        self.register_structure_fields(
            Name::from_string("ToString"),
            vec![Name::from_string("toString")],
        )?;
        self.register_class(KernelClassInfo {
            name: Name::from_string("ToString"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // ToString.toString : {α : Type u} → [inst : ToString α] → α → String
        let tostring_field_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ts_alpha = Expr::app(tostring_const(u_level.clone()), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(ts_alpha.clone());
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let r = string_const.clone();
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let tostring_rec =
            |u1: Level, u2: Level| Expr::const_(Name::from_string("ToString.rec"), vec![u1, u2]);

        let tostring_field_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ts_alpha = Expr::app(tostring_const(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
            let (a_id, a_var) = b.fresh_local(alpha.clone());

            let alpha_to_string = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(alpha.clone());
                let r = string_const.clone();
                let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };

            // Motive: λ (_ : ToString α) => α → String
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(ts_alpha.clone());
                let r = c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    ts_alpha.clone(),
                    alpha_to_string.clone(),
                );
                c.finish_child(r)
            };

            // Minor: λ (f : α → String) => f
            let minor = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (f_id, f) = c.fresh_local(alpha_to_string.clone());
                let r = c.mk_lam(f_id, BinderInfo::Default, alpha_to_string.clone(), f);
                c.finish_child(r)
            };

            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                tostring_rec(Level::succ(u_level.clone()), u_level.clone()),
                                alpha.clone(),
                            ),
                            motive,
                        ),
                        minor,
                    ),
                    inst,
                ),
                a_var,
            );
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, ts_alpha, r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("ToString.toString"),
            level_params: vec![u.clone()],
            type_: tostring_field_type,
            value: tostring_field_value,
            is_reducible: true,
        })?;

        // toString : {α : Type u} → [inst : ToString α] → α → String
        //   := λ {α} [inst] a => ToString.toString a
        let tostring_alias_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ts_alpha = Expr::app(tostring_const(u_level.clone()), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(ts_alpha.clone());
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let r = string_const.clone();
            let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        let tostring_alias_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ts_alpha = Expr::app(tostring_const(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
            let (a_id, a_var) = b.fresh_local(alpha.clone());
            let field = Expr::const_(
                Name::from_string("ToString.toString"),
                vec![u_level.clone()],
            );
            let body = Expr::app(Expr::app(Expr::app(field, alpha.clone()), inst), a_var);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, ts_alpha, r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("toString"),
            level_params: vec![u.clone()],
            type_: tostring_alias_type,
            value: tostring_alias_value,
            is_reducible: true,
        })?;

        // NOTE (B04): the core `ToString` INSTANCES register later, in
        // `init_to_string_instances` (wired after `init_char_defs` in
        // `init_prelude_extended`) — their genuine bodies need `Char.ofNat`
        // via `Nat.repr`, which does not exist yet at this point of prelude
        // construction.
        self.to_string_init = true;
        Ok(())
    }

    /// Register the core `ToString` instances with REAL value-producing
    /// bodies (B04, GAP_SWEEP_2026-07-09). The previous placeholder bodies
    /// (`toString := fun _ => ""`) made the kernel rfl-CERTIFY wrong values
    /// (`s!"one {1 + 1} three" = "one  three"` was provable).
    ///
    /// Lean ground truth (lean4 `Init/Data/ToString/Basic.lean`):
    ///   instance : ToString Nat    := ⟨fun n => Nat.repr n⟩
    ///   instance : ToString String := ⟨fun s => s⟩
    ///   instance : ToString Bool   := ⟨fun b => cond b "true" "false"⟩
    ///
    /// Wired after `init_char_defs` in `init_prelude_extended`: `Nat.repr`'s
    /// digit chain needs `Char.ofNat`, which only exists from that point.
    /// Idempotent; import mode skips (the genuine instances import through
    /// the checked `.olean` path, same gate as `init_to_string`).
    pub(crate) fn init_to_string_instances(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self
            .get_const(&Name::from_string("instToStringNat"))
            .is_some()
        {
            return Ok(());
        }
        self.init_to_string()?;
        self.init_nat_repr()?;

        let string_const = Expr::const_(Name::from_string("String"), vec![]);
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let tostring_nat_fn = Expr::lam(
            BinderInfo::Default,
            nat_const.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Nat.repr"), vec![]),
                Expr::bvar(0),
            ),
        );
        self.add_tostring_const_instance("instToStringNat", &nat_const, tostring_nat_fn)?;

        let tostring_string_fn =
            Expr::lam(BinderInfo::Default, string_const.clone(), Expr::bvar(0));
        self.add_tostring_const_instance("instToStringString", &string_const, tostring_string_fn)?;

        // `cond b "true" "false"` spelled as the `Bool.rec` it unfolds to
        // (`cond` is not a prelude head yet; `Bool.rec (motive := fun _ =>
        // String) "false" "true" b` — false-minor first, matching the
        // `Bool.false | Bool.true` constructor order — is defeq to it).
        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
        let tostring_bool_fn = Expr::lam(
            BinderInfo::Default,
            bool_const.clone(),
            Expr::apps(
                Expr::const_(
                    Name::from_string("Bool.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [
                    Expr::lam(
                        BinderInfo::Default,
                        bool_const.clone(),
                        string_const.clone(),
                    ),
                    Expr::str_lit("false"),
                    Expr::str_lit("true"),
                    Expr::bvar(0),
                ],
            ),
        );
        self.add_tostring_const_instance("instToStringBool", &bool_const, tostring_bool_fn)?;

        self.init_to_string_extended_instances()?;

        Ok(())
    }

    /// Register the rest of Lean's core `ToString` family — `Int`, `Char`,
    /// `UInt32`, `UInt64` and `List α`.
    ///
    /// Measured 2026-08-27 through `clean run`, before this: `toString` on any
    /// of those five failed elaboration outright with "failed to synthesize
    /// instance `ToString <T>`". Only `Nat`/`String`/`Bool` were registered,
    /// which is also why `List.foldl (·+·) 0 [1,2,3,4]` could not be printed —
    /// its result defaults to `UInt64`.
    ///
    /// ORDERING. Every body below renders through an instance rather than
    /// open-coding a number, so registering them was correctly blocked until
    /// `cdd16e470` taught the `l_toString` shim to APPLY its instance. Before
    /// that fix each of these would have printed a `Nat` reading of whatever
    /// pointer or tag the value happened to be — more silently-wrong output,
    /// not less.
    ///
    /// Lean ground truth (`Init/Data/ToString/Basic.lean`, `Init/Data/Repr.lean`):
    ///
    /// ```lean
    /// instance : ToString Int    := ⟨fun i => Int.repr i⟩
    /// instance : ToString Char   := ⟨fun c => String.singleton c⟩
    /// instance : ToString UInt32 := ⟨fun n => toString n.toNat⟩
    /// instance : ToString UInt64 := ⟨fun n => toString n.toNat⟩
    /// instance [ToString α] : ToString (List α) := ⟨List.toString⟩
    /// ```
    ///
    /// `Int.repr` and `String.singleton` are not declared in this prelude, so
    /// their Lean bodies are inlined at the constant that needs them:
    /// `Int.repr` IS the two-constructor split written here on `Int.rec`
    /// (`negSucc n` denotes `-(n+1)`, hence the `Nat.succ`), and
    /// `String.singleton c` IS `String.mk [c]`. `List.toString`'s accumulator
    /// `foldl` is written as the equivalent right fold on `List.rec` — the
    /// rendered text is identical, `[]` for nil and `[x, y, z]` otherwise.
    ///
    /// Wired from `init_to_string_instances`, so it inherits that function's
    /// import-mode suppression and idempotence: in import mode the genuine
    /// instances arrive through the checked `.olean` path instead.
    fn init_to_string_extended_instances(&mut self) -> Result<(), EnvError> {
        self.init_int()?;
        self.init_list()?;
        // Every body below concatenates with `String.append`; `Int.rec`'s
        // negative arm and the whole `List` rendering are unwritable without
        // it. Idempotent, and it pulls in its own `List.append` dependency.
        self.init_string_append()?;

        // A cut-down environment that never registered one of these carriers
        // skips that instance rather than failing prelude construction — the
        // same shape `init_char_defs` uses. Skipping leaves the pre-existing
        // "failed to synthesize instance" behaviour, never a wrong rendering.
        let registered =
            |env: &Environment, n: &str| env.get_const(&Name::from_string(n)).is_some();
        if !registered(self, "String.append") {
            return Ok(());
        }

        let string_const = Expr::const_(Name::from_string("String"), vec![]);
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let append = Expr::const_(Name::from_string("String.append"), vec![]);

        // `toString (n : Nat)` spelled through the class, i.e.
        // `@ToString.toString.{0} Nat instToStringNat n`. Going through the
        // projection rather than calling `Nat.repr` directly is what keeps the
        // rendering an INSTANCE application all the way down, which is the
        // representation the compiler's `l_toString` / `l_instToStringNat`
        // pair implements.
        let render_nat = |arg: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("ToString.toString"), vec![Level::zero()]),
                [
                    nat_const.clone(),
                    Expr::const_(Name::from_string("instToStringNat"), vec![]),
                    arg,
                ],
            )
        };

        // ── ToString Int ────────────────────────────────────────────────────
        // fun (i : Int) => Int.rec (motive := fun _ => String)
        //   (fun n => toString n)                   -- Int.ofNat n
        //   (fun n => "-" ++ toString (Nat.succ n)) -- Int.negSucc n = -(n+1)
        //   i
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        let tostring_int_fn = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(int_const.clone());
            let motive = {
                let (m_id, _m) = b.fresh_local(int_const.clone());
                b.mk_lam(
                    m_id,
                    BinderInfo::Default,
                    int_const.clone(),
                    string_const.clone(),
                )
            };
            let of_nat_minor = {
                let (n_id, n) = b.fresh_local(nat_const.clone());
                b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), render_nat(n))
            };
            let neg_succ_minor = {
                let (n_id, n) = b.fresh_local(nat_const.clone());
                let succ_n = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), n);
                let body = Expr::apps(append.clone(), [Expr::str_lit("-"), render_nat(succ_n)]);
                b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), body)
            };
            // `Int.rec.{1}`: the motive lands in `Sort 1`, i.e. `Type 0`, which
            // is where `String` lives.
            let rec = Expr::apps(
                Expr::const_(
                    Name::from_string("Int.rec"),
                    vec![Level::succ(Level::zero())],
                ),
                [motive, of_nat_minor, neg_succ_minor, i],
            );
            let r = b.mk_lam(i_id, BinderInfo::Default, int_const.clone(), rec);
            b.finish(r)
        };
        self.add_tostring_const_instance("instToStringInt", &int_const, tostring_int_fn)?;

        // ── ToString Char ───────────────────────────────────────────────────
        // fun (c : Char) => String.mk (List.cons Char c (List.nil Char))
        // — Lean's `String.singleton c`, which this prelude does not declare.
        let char_const = Expr::const_(Name::from_string("Char"), vec![]);
        if registered(self, "Char") && registered(self, "String.mk") {
            let tostring_char_fn = {
                let mut b = EnvDeclBuilder::new();
                let (c_id, c) = b.fresh_local(char_const.clone());
                let nil = Expr::app(
                    Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
                    char_const.clone(),
                );
                let one = Expr::apps(
                    Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                    [char_const.clone(), c, nil],
                );
                let body = Expr::app(Expr::const_(Name::from_string("String.mk"), vec![]), one);
                let r = b.mk_lam(c_id, BinderInfo::Default, char_const.clone(), body);
                b.finish(r)
            };
            self.add_tostring_const_instance("instToStringChar", &char_const, tostring_char_fn)?;
        }

        // ── ToString UInt32 / UInt64 ────────────────────────────────────────
        // fun (n : UIntW) => toString (UIntW.toNat n)
        for (inst_name, ty_name, to_nat) in [
            ("instToStringUInt32", "UInt32", "UInt32.toNat"),
            ("instToStringUInt64", "UInt64", "UInt64.toNat"),
        ] {
            if !registered(self, ty_name) || !registered(self, to_nat) {
                continue;
            }
            let ty = Expr::const_(Name::from_string(ty_name), vec![]);
            let f = {
                let mut b = EnvDeclBuilder::new();
                let (n_id, n) = b.fresh_local(ty.clone());
                let as_nat = Expr::app(Expr::const_(Name::from_string(to_nat), vec![]), n);
                let r = b.mk_lam(n_id, BinderInfo::Default, ty.clone(), render_nat(as_nat));
                b.finish(r)
            };
            self.add_tostring_const_instance(inst_name, &ty, f)?;
        }

        self.add_tostring_list_instance()?;

        Ok(())
    }

    /// Register `instToStringList : {α : Type u} → [ToString α] → ToString (List α)`.
    ///
    /// The body is Lean's `List.toString` written as a right fold:
    ///
    /// ```text
    /// []      ↦ "[]"
    /// x :: xs ↦ "[" ++ toString x ++ join xs ++ "]"
    /// join []        = ""
    /// join (y :: ys) = ", " ++ toString y ++ join ys
    /// ```
    ///
    /// so `[1, 2, 3]` renders as `[1, 2, 3]`, `[7]` as `[7]`, and `[]` as `[]`
    /// — byte-for-byte what Lean prints. Both folds are `List.rec` at
    /// `Sort 1` over the element universe, and the element rendering is
    /// `@ToString.toString.{u} α inst`, so the ELEMENT instance is what
    /// renders each element; nothing here assumes `Nat`.
    fn add_tostring_list_instance(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let string_const = Expr::const_(Name::from_string("String"), vec![]);
        let append = Expr::const_(Name::from_string("String.append"), vec![]);
        let tostring_const = |l: Level| Expr::const_(Name::from_string("ToString"), vec![l]);
        let list_const = |l: Level| Expr::const_(Name::from_string("List"), vec![l]);

        // {α : Type u} → [inst : ToString α] → ToString (List α)
        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ts_alpha = Expr::app(tostring_const(u_level.clone()), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(ts_alpha.clone());
            let list_alpha = Expr::app(list_const(u_level.clone()), alpha.clone());
            let r = Expr::app(tostring_const(u_level.clone()), list_alpha);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ts_alpha = Expr::app(tostring_const(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
            let list_alpha = Expr::app(list_const(u_level.clone()), alpha.clone());

            // @ToString.toString.{u} α inst x — the ELEMENT's own rendering.
            let render_elem = |x: Expr| {
                Expr::apps(
                    Expr::const_(
                        Name::from_string("ToString.toString"),
                        vec![u_level.clone()],
                    ),
                    [alpha.clone(), inst.clone(), x],
                )
            };
            // `List.rec.{1, u}`: motive into `Sort 1`, elements at `Type u`.
            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(Level::zero()), u_level.clone()],
            );
            // motive := fun (_ : List α) => String
            let motive = {
                let (m_id, _m) = b.fresh_local(list_alpha.clone());
                b.mk_lam(
                    m_id,
                    BinderInfo::Default,
                    list_alpha.clone(),
                    string_const.clone(),
                )
            };

            // join (y :: ys) = ", " ++ toString y ++ join ys
            let join_cons = {
                let (y_id, y) = b.fresh_local(alpha.clone());
                let (ys_id, _ys) = b.fresh_local(list_alpha.clone());
                let (ih_id, ih) = b.fresh_local(string_const.clone());
                let body = Expr::apps(
                    append.clone(),
                    [
                        Expr::apps(append.clone(), [Expr::str_lit(", "), render_elem(y)]),
                        ih,
                    ],
                );
                let r = b.mk_lam(ih_id, BinderInfo::Default, string_const.clone(), body);
                let r = b.mk_lam(ys_id, BinderInfo::Default, list_alpha.clone(), r);
                b.mk_lam(y_id, BinderInfo::Default, alpha.clone(), r)
            };

            // x :: xs ↦ "[" ++ toString x ++ join xs ++ "]"
            // The recursive result for `xs` is deliberately unused: the head is
            // bracketed and every later element is comma-prefixed, which is a
            // different fold from the one the outer recursion is running.
            let outer_cons = {
                let (x_id, x) = b.fresh_local(alpha.clone());
                let (xs_id, xs) = b.fresh_local(list_alpha.clone());
                let (ih_id, _ih) = b.fresh_local(string_const.clone());
                let join_xs = Expr::apps(
                    list_rec.clone(),
                    [
                        alpha.clone(),
                        motive.clone(),
                        Expr::str_lit(""),
                        join_cons,
                        xs,
                    ],
                );
                let body = Expr::apps(
                    append.clone(),
                    [
                        Expr::apps(append.clone(), [Expr::str_lit("["), render_elem(x)]),
                        Expr::apps(append.clone(), [join_xs, Expr::str_lit("]")]),
                    ],
                );
                let r = b.mk_lam(ih_id, BinderInfo::Default, string_const.clone(), body);
                let r = b.mk_lam(xs_id, BinderInfo::Default, list_alpha.clone(), r);
                b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), r)
            };

            let (l_id, l) = b.fresh_local(list_alpha.clone());
            let rendered = Expr::apps(
                list_rec,
                [alpha.clone(), motive, Expr::str_lit("[]"), outer_cons, l],
            );
            let tostring_fn = b.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), rendered);
            let value = Expr::apps(
                Expr::const_(Name::from_string("ToString.mk"), vec![u_level.clone()]),
                [list_alpha, tostring_fn],
            );
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, ts_alpha, value);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instToStringList"),
            level_params: vec![u],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instToStringList"),
            class_name: Name::from_string("ToString"),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Register a `ToString T` instance for a closed type `T` at level 0 with
    /// the given `toString : T → String` body. The instance value is the
    /// fully-checked `ToString.mk T body` — no placeholder lane remains (B04).
    fn add_tostring_const_instance(
        &mut self,
        inst_name: &str,
        ty: &Expr,
        tostring_fn: Expr,
    ) -> Result<(), EnvError> {
        let level = Level::zero();
        let ts_ty = Expr::app(
            Expr::const_(Name::from_string("ToString"), vec![level.clone()]),
            ty.clone(),
        );
        let value = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("ToString.mk"), vec![level]),
                ty.clone(),
            ),
            tostring_fn,
        );
        self.add_decl(Declaration::Definition {
            name: Name::from_string(inst_name),
            level_params: vec![],
            type_: ts_ty,
            value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string(inst_name),
            class_name: Name::from_string("ToString"),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Check if the `Repr` typeclass has been initialized.
    #[cfg(test)]
    pub(crate) fn has_repr(&self) -> bool {
        self.repr_init
    }

    /// Check if the `ToString` typeclass has been initialized.
    #[cfg(test)]
    pub(crate) fn has_to_string(&self) -> bool {
        self.to_string_init
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    /// `Repr` / `ToString` classes and their core members are registered by
    /// `with_prelude` and are recognized as classes by instance synthesis.
    #[test]
    fn test_repr_tostring_classes_registered() {
        let env = Environment::with_prelude();
        assert!(env.has_repr(), "Repr must be initialized by the prelude");
        assert!(
            env.has_to_string(),
            "ToString must be initialized by the prelude"
        );
        assert!(
            env.is_class(&Name::from_string("Repr")),
            "Repr must be a registered class"
        );
        assert!(
            env.is_class(&Name::from_string("ToString")),
            "ToString must be a registered class"
        );
        assert!(
            env.get_inductive(&Name::from_string("Repr")).is_some(),
            "Repr inductive must exist"
        );
        assert!(
            env.get_inductive(&Name::from_string("ToString")).is_some(),
            "ToString inductive must exist"
        );
    }

    /// Every member / instance is a `Definition` (not an axiom) and its declared
    /// type type-checks via `infer_type` — proving the closed terms are
    /// well-formed.
    #[test]
    fn test_repr_tostring_members_type_check() {
        let env = Environment::with_prelude();

        // Universe-polymorphic members (one level param) vs monomorphic
        // instances (no level params).
        let poly = ["Repr.reprPrec", "repr", "ToString.toString", "toString"];
        let mono = [
            "instReprNat",
            "instReprString",
            "instReprBool",
            "instReprInt",
            "instToStringNat",
            "instToStringString",
            "instToStringBool",
            "instToStringInt",
            "instToStringChar",
            "instToStringUInt32",
            "instToStringUInt64",
        ];

        for name in poly {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be a Definition, not an Axiom"
            );
            assert!(info.value.is_some(), "{name} must retain its value");
            let tc = TypeChecker::with_mode(&env, env.mode());
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(name), vec![Level::zero()]))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        }

        for name in mono.iter().chain(["instReprList"].iter()) {
            let info = env
                .get_const(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} should be registered"));
            assert_eq!(
                info.kind,
                ConstantKind::Definition,
                "{name} must be a Definition, not an Axiom"
            );
            assert!(info.value.is_some(), "{name} must retain its value");
        }

        // instReprList is universe-polymorphic; check it type-checks at level 0.
        let tc = TypeChecker::with_mode(&env, env.mode());
        let _ = tc
            .infer_type(&Expr::const_(
                Name::from_string("instReprList"),
                vec![Level::zero()],
            ))
            .expect("instReprList should type-check");
        for name in mono {
            let tc = TypeChecker::with_mode(&env, env.mode());
            let _ = tc
                .infer_type(&Expr::const_(Name::from_string(name), vec![]))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));
        }
    }

    /// The axiom closure of every registered `Repr`/`ToString` member and
    /// instance is EMPTY — no `sorryAx`, no trusted/fake axiom. No-fake guard.
    #[test]
    fn test_repr_tostring_axiom_closure_empty() {
        let env = Environment::with_prelude();
        for name in [
            "Repr.reprPrec",
            "repr",
            "ToString.toString",
            "toString",
            "instReprNat",
            "instReprString",
            "instReprBool",
            "instReprInt",
            "instReprList",
            "instToStringNat",
            "instToStringString",
            "instToStringBool",
        ] {
            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} is registered"));
            let names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                names.is_empty(),
                "{name} must have empty axiom closure, got {names:?}"
            );
        }
    }
}
