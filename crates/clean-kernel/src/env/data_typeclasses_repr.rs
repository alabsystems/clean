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
//! Both classes are modelled with `String`-valued fields (Lean's `Repr` is
//! `Std.Format`-valued). All registered terms are axiom-free: the class
//! members are `Declaration::Definition`s built from the class recursor,
//! mirroring the `BEq` / `Hashable` bootstrap pattern, and every `Repr`
//! instance renders through the OPAQUE `Clean.Repr.render`
//! (`data_typeclasses_repr_compound`), so no two values Lean renders
//! differently are definitionally equal renderings here.

use super::data_typeclasses_repr_compound::{packed_render_fn, repr_render_at};
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

        // Dependencies. `Prod` packs a compound instance's element instances
        // with the rendered value (`packed_render_fn`).
        self.init_nat()?;
        self.init_string()?;
        self.init_bool()?;
        self.init_int()?;
        self.init_list()?;
        self.init_prod()?;

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
            BinderInfo::Default,
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

        // Core instances. Their `reprPrec` is the opaque `Clean.Repr.render`
        // (never Lean's text, never a collapsing constant): they exist so
        // instance synthesis can satisfy `[Repr Nat]` / `[Repr (List α)]` etc.
        // for `deriving Repr` and explicit `Repr` instances.
        self.init_repr_render()?;
        self.add_repr_const_instance("instReprNat", &nat_const, Level::zero())?;
        self.add_repr_const_instance("instReprString", &string_const, Level::zero())?;
        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
        self.add_repr_const_instance("instReprBool", &bool_const, Level::zero())?;
        let int_const = Expr::const_(Name::from_string("Int"), vec![]);
        self.add_repr_const_instance("instReprInt", &int_const, Level::zero())?;

        // instReprList : {α : Type u} → [Repr α] → Repr (List α)
        self.add_repr_list_instance(&u, &u_level, &type_u)?;

        // instReprOption / Clean.instReprProdOfRepr — the compound carriers a
        // `deriving Repr` field most often has (`Option Nat`, `List (α × β)`).
        self.init_repr_compound_instances()?;

        self.repr_init = true;
        Ok(())
    }

    /// Register a `Repr T` instance for a closed type `T` whose `reprPrec` is
    /// the opaque `@Clean.Repr.render T`.
    fn add_repr_const_instance(
        &mut self,
        inst_name: &str,
        ty: &Expr,
        level: Level,
    ) -> Result<(), EnvError> {
        let repr_ty = Expr::app(
            Expr::const_(Name::from_string("Repr"), vec![level.clone()]),
            ty.clone(),
        );
        let reprprec_fn = repr_render_at(level.clone(), ty.clone());
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
    /// `reprPrec` is the opaque renderer applied to `(inst, l)`, so the
    /// rendering depends on the element instance as well as the list.
    fn add_repr_list_instance(
        &mut self,
        u: &Name,
        u_level: &Level,
        type_u: &Expr,
    ) -> Result<(), EnvError> {
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
            let (inst_id, inst) = b.fresh_local(repr_alpha.clone());
            let list_alpha = Expr::app(list_const(u_level.clone()), alpha.clone());

            // fun (l : List α) => Clean.Repr.render (inst, l)
            let reprprec_fn =
                packed_render_fn(&b, &repr_alpha, u_level, &inst, &list_alpha, u_level);

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
            BinderInfo::Default,
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
    /// every fixed-width unsigned carrier (`UInt8`, `UInt16`, `UInt32`,
    /// `UInt64`, `USize`), `List α`, `Option α` and `Prod α β`.
    ///
    /// Measured 2026-08-27 through `clean run`, before the first five landed:
    /// `toString` on an `Int`, a `Char`, a `UInt32`, a `UInt64` or a `List`
    /// failed elaboration outright with "failed to synthesize instance
    /// `ToString <T>`". Only `Nat`/`String`/`Bool` were registered, which is
    /// also why `List.foldl (·+·) 0 [1,2,3,4]` could not be printed — its
    /// result defaults to `UInt64`. `UInt8`, `UInt16` and `USize` still failed
    /// exactly that way when measured on 2026-09-16, and are registered here
    /// for the same reason.
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
    /// instance : ToString UInt8  := ⟨fun n => toString n.toNat⟩
    /// instance : ToString UInt16 := ⟨fun n => toString n.toNat⟩
    /// instance : ToString UInt32 := ⟨fun n => toString n.toNat⟩
    /// instance : ToString UInt64 := ⟨fun n => toString n.toNat⟩
    /// instance : ToString USize  := ⟨fun n => toString n.toNat⟩
    /// instance [ToString α] : ToString (List α) := ⟨List.toString⟩
    /// ```
    ///
    /// The five unsigned bodies are transcribed, not paraphrased:
    /// `#print instToStringUInt8` on the pinned Lean v4.30.0-rc2 prints
    /// `{ toString := fun n => toString n.toNat }`, and all five are declared
    /// in `Init.Data.ToString.Basic` — measured 2026-09-16 through
    /// `Lean.Environment.getModuleIdxFor?`, i.e. inside the same `Init`
    /// closure `data/prelude_instance_priority_census.json` walks, which is
    /// why all five are collisions in that census rather than Clean-only names.
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

        // ── ToString UInt8 / UInt16 / UInt32 / UInt64 / USize ───────────────
        // fun (n : UIntW) => toString (UIntW.toNat n)
        //
        // `UInt8`, `UInt16` and `USize` were added 2026-09-16. What was missing
        // was the REGISTRATION and nothing else, measured rather than inferred:
        // on the same binary that refused `toString (7 : UInt8)` with "failed
        // to synthesize instance `ToString UInt8`", the program
        // `IO.println (toString (UInt8.toNat (7 : UInt8)))` and its `UInt16` /
        // `USize` siblings elaborated, compiled, linked and ran through
        // `clean run`, printing `7` / `65535` / `12345`. In the C that run
        // emits (`clean compile ... --emit c`), `l_UInt8_toNat`,
        // `l_UInt16_toNat` and `l_USize_toNat` appear as DEFINITIONS lowered
        // from the prelude's own `<W>.toNat` bodies, not as externs, so no shim
        // table in `clean-cli/src/native_build.rs` had to grow for them;
        // `UInt32` and `UInt64` are the exception there, their `toNat` being
        // denylisted and shimmed. The carriers are in place well before this
        // point: `init_uint_types` and `init_usize` run in the same
        // `with_prelude` chain (`env/mod.rs`), ahead of the
        // `init_to_string_instances` call that reaches here.
        //
        // Registration order is ascending by width. `register_instance`
        // (`env/registries.rs`) inserts a new instance BEFORE the first entry
        // of equal-or-lower priority, i.e. most-recent-first among equals, so
        // no arrangement of this loop leaves `UInt32`/`UInt64` at their former
        // candidate index once three siblings join them at priority 1000;
        // ascending order moves them the least. It is inert either way — all
        // five target distinct closed types, so at most one candidate unifies
        // with any concrete `ToString` goal.
        //
        // The rendered bytes are pinned against the Lean v4.30.0-rc2 binary in
        // `crates/clean/tests/tostring_instances_cli.rs`, including the one
        // value on which Clean and Lean DISAGREE for a reason outside this
        // function: a `USize` at or above `2^63` does not fit the runtime's
        // tagged scalar box and is truncated with no `ToString` involved.
        for (inst_name, ty_name, to_nat) in [
            ("instToStringUInt8", "UInt8", "UInt8.toNat"),
            ("instToStringUInt16", "UInt16", "UInt16.toNat"),
            ("instToStringUInt32", "UInt32", "UInt32.toNat"),
            ("instToStringUInt64", "UInt64", "UInt64.toNat"),
            ("instToStringUSize", "USize", "USize.toNat"),
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

        // ── ToString Float ──────────────────────────────────────────────────
        // `instToStringFloat := ⟨Float.toString⟩` over the OPAQUE extern
        // `Float.toString` (G27; `data_typeclasses_tostring_float.rs`).
        self.add_tostring_float_instance()?;

        self.add_tostring_list_instance()?;
        self.add_tostring_option_instance()?;
        self.add_tostring_prod_instance()?;

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

    /// Register `instToStringOption : {α : Type u} → [ToString α] → ToString (Option α)`.
    ///
    /// Lean ground truth, `Init/Data/ToString/Basic.lean:95`:
    ///
    /// ```lean
    /// instance {α : Type u} [ToString α] : ToString (Option α) := ⟨fun
    ///   | none     => "none"
    ///   | (some a) => "(some " ++ addParenHeuristic (toString a) ++ ")"⟩
    /// ```
    ///
    /// The element is rendered through `@ToString.toString.{u} α inst`, so the
    /// ELEMENT's own instance does the work and nothing here assumes `Nat` —
    /// the same discipline as `add_tostring_list_instance`. The split is
    /// `Option.rec.{1, u}`: motive into `Sort 1` (where `String` lives), carrier
    /// at `Type u`, minors in constructor order `none` then `some`.
    ///
    /// # The one measured divergence: `addParenHeuristic` is NOT applied
    ///
    /// Lean wraps the element's rendering in `addParenHeuristic`
    /// (`Init/Data/ToString/Basic.lean:90`), which parenthesizes a rendering
    /// that contains whitespace unless it already starts with `(`, `[`, `{` or
    /// `#[`. Measured against the pinned `lean 4.30.0-rc2`, the heuristic is the
    /// IDENTITY on every rendering the rest of this prelude can produce — a
    /// `Nat`/`Int`/`UInt` decimal, `true`/`false`, a nested `(some …)` or
    /// `(a, b)` (starts with `(`), a `[…]` list (starts with `[`) — so those all
    /// agree byte for byte:
    ///
    /// ```text
    /// toString (some 3)             "(some 3)"           agrees
    /// toString (none : Option Nat)  "none"               agrees
    /// toString (some (some 3))      "(some (some 3))"    agrees
    /// toString (some ((1,2)))       "(some (1, 2))"      agrees
    /// toString (some [1,2])         "(some [1, 2])"      agrees
    /// toString (some "ab")          "(some ab)"          agrees
    /// ```
    ///
    /// It DIVERGES only when the element's rendering contains whitespace and
    /// does not already start with one of those four openers, which in this
    /// prelude means a `String` or `Char` element:
    ///
    /// ```text
    /// toString (some "a b")   Lean "(some (a b))"   here "(some a b)"
    /// toString (some ' ')     Lean "(some ( ))"     here "(some  )"
    /// ```
    ///
    /// Closing it is not a change to this function: `addParenHeuristic` needs
    /// `String.isPrefixOf` / `Char.isWhitespace`, which exist here only as
    /// native whnf reducers and not as declarations, and any body that reaches
    /// them through `String.data` is refused by the native build —
    /// `select_shims_from_tables` (clean-cli `native_build.rs`) bails with
    /// "native build refuses source-lowered String body `l_String_data`: the
    /// runtime `String` carrier is a flat byte string", measured 2026-09-16. So
    /// the heuristic needs a declared helper AND its own C shim. The divergence
    /// is pinned by `clean_run_option_element_paren_heuristic_is_not_applied`
    /// in `crates/clean/tests/tostring_instances_cli.rs`, which asserts the
    /// bytes THIS body produces and quotes Lean's beside them, so the day the
    /// helper lands that test fails and is read.
    fn add_tostring_option_instance(&mut self) -> Result<(), EnvError> {
        // A cut-down environment that never registered `Option` skips this
        // instance rather than failing prelude construction, the same shape the
        // `Char` / `UInt32` arms above use. `Option.rec` is what the body
        // splits on, so it is the constant that has to be there.
        if self.get_const(&Name::from_string("Option.rec")).is_none() {
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let string_const = Expr::const_(Name::from_string("String"), vec![]);
        let append = Expr::const_(Name::from_string("String.append"), vec![]);
        let tostring_const = |l: Level| Expr::const_(Name::from_string("ToString"), vec![l]);
        let option_const = |l: Level| Expr::const_(Name::from_string("Option"), vec![l]);

        // {α : Type u} → [inst : ToString α] → ToString (Option α)
        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ts_alpha = Expr::app(tostring_const(u_level.clone()), alpha.clone());
            let (inst_id, _inst) = b.fresh_local(ts_alpha.clone());
            let option_alpha = Expr::app(option_const(u_level.clone()), alpha.clone());
            let r = Expr::app(tostring_const(u_level.clone()), option_alpha);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, ts_alpha, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let ts_alpha = Expr::app(tostring_const(u_level.clone()), alpha.clone());
            let (inst_id, inst) = b.fresh_local(ts_alpha.clone());
            let option_alpha = Expr::app(option_const(u_level.clone()), alpha.clone());

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
            // `Option.rec.{1, u}`: motive into `Sort 1`, carrier at `Type u` —
            // the [motive-elim, type] order `Option.map` already uses.
            let option_rec = Expr::const_(
                Name::from_string("Option.rec"),
                vec![Level::succ(Level::zero()), u_level.clone()],
            );
            // motive := fun (_ : Option α) => String
            let motive = {
                let (m_id, _m) = b.fresh_local(option_alpha.clone());
                b.mk_lam(
                    m_id,
                    BinderInfo::Default,
                    option_alpha.clone(),
                    string_const.clone(),
                )
            };

            // some a ↦ "(some " ++ toString a ++ ")"
            let some_minor = {
                let (a_id, a) = b.fresh_local(alpha.clone());
                let body = Expr::apps(
                    append.clone(),
                    [
                        Expr::apps(append.clone(), [Expr::str_lit("(some "), render_elem(a)]),
                        Expr::str_lit(")"),
                    ],
                );
                b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body)
            };

            let (o_id, o) = b.fresh_local(option_alpha.clone());
            let rendered = Expr::apps(
                option_rec,
                [alpha.clone(), motive, Expr::str_lit("none"), some_minor, o],
            );
            let tostring_fn = b.mk_lam(o_id, BinderInfo::Default, option_alpha.clone(), rendered);
            let value = Expr::apps(
                Expr::const_(Name::from_string("ToString.mk"), vec![u_level.clone()]),
                [option_alpha, tostring_fn],
            );
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, ts_alpha, value);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instToStringOption"),
            level_params: vec![u],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instToStringOption"),
            class_name: Name::from_string("ToString"),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// Register
    /// `instToStringProd : {α : Type u} → {β : Type v} → [ToString α] → [ToString β] → ToString (Prod α β)`.
    ///
    /// Lean ground truth, `Init/Data/ToString/Basic.lean:103`:
    ///
    /// ```lean
    /// instance {α : Type u} {β : Type v} [ToString α] [ToString β] : ToString (α × β) :=
    ///   ⟨fun (a, b) => "(" ++ toString a ++ ", " ++ toString b ++ ")"⟩
    /// ```
    ///
    /// No `addParenHeuristic` on this one — Lean appends the two renderings
    /// raw, which is why `toString ((1, 2, 3) : Nat × Nat × Nat)` is
    /// `"(1, (2, 3))"` and not `"(1, 2, 3)"`: the right component is itself a
    /// `Prod` and brings its own parentheses. Measured on the pinned
    /// `lean 4.30.0-rc2`, so this instance is byte-exact with Lean at every
    /// element instance in this prelude, `String` and `Char` included.
    ///
    /// TWO universe parameters and TWO instance premises, which is the part
    /// that had not been exercised by a hand-rolled prelude instance before.
    /// Both halves were measured against the shipped binary before this landed:
    /// the search already discharges a two-premise candidate (`instDecidableAnd`
    /// resolves `Decidable (1 < 2 ∧ 3 < 4)`), and the same `{α} {β} [_] [_]`
    /// shape written as a SOURCE `instance` elaborates, kernel-checks, lowers
    /// and runs through `clean run` at the bytes quoted above.
    ///
    /// The result universe is `max u v`: `Prod.{u,v} α β : Sort (max (u+1) (v+1))`
    /// and `ToString.{w}` wants `Sort (w+1)`, so `w = max u v`.
    fn add_tostring_prod_instance(&mut self) -> Result<(), EnvError> {
        // Same skip-rather-than-fail contract as the `Option` arm: a cut-down
        // environment without the `Prod` projections keeps the pre-existing
        // "failed to synthesize instance" behaviour, never a wrong rendering.
        if self.get_const(&Name::from_string("Prod.fst")).is_none()
            || self.get_const(&Name::from_string("Prod.snd")).is_none()
        {
            return Ok(());
        }

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        // `ToString.{max v u} (Prod α β)`: Lean spells the level `max u_2 u_1`
        // (pinned v4.30.0-rc2, `#check @instToStringProd` under
        // `pp.universes`), and the collision census compares spellings.
        let uv_level = Level::max(v_level.clone(), u_level.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(v_level.clone())));
        let append = Expr::const_(Name::from_string("String.append"), vec![]);
        let tostring_const = |l: Level| Expr::const_(Name::from_string("ToString"), vec![l]);
        let prod_const = || {
            Expr::const_(
                Name::from_string("Prod"),
                vec![u_level.clone(), v_level.clone()],
            )
        };

        // {α : Type u} → {β : Type v} → [ia : ToString α] → [ib : ToString β]
        //   → ToString (Prod α β)
        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let ts_alpha = Expr::app(tostring_const(u_level.clone()), alpha.clone());
            let (ia_id, _ia) = b.fresh_local(ts_alpha.clone());
            let ts_beta = Expr::app(tostring_const(v_level.clone()), beta.clone());
            let (ib_id, _ib) = b.fresh_local(ts_beta.clone());
            let prod_ab = Expr::apps(prod_const(), [alpha.clone(), beta.clone()]);
            let r = Expr::app(tostring_const(uv_level.clone()), prod_ab);
            let r = b.mk_pi(ib_id, BinderInfo::InstImplicit, ts_beta, r);
            let r = b.mk_pi(ia_id, BinderInfo::InstImplicit, ts_alpha, r);
            let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let ts_alpha = Expr::app(tostring_const(u_level.clone()), alpha.clone());
            let (ia_id, ia) = b.fresh_local(ts_alpha.clone());
            let ts_beta = Expr::app(tostring_const(v_level.clone()), beta.clone());
            let (ib_id, ib) = b.fresh_local(ts_beta.clone());
            let prod_ab = Expr::apps(prod_const(), [alpha.clone(), beta.clone()]);

            let (p_id, p) = b.fresh_local(prod_ab.clone());
            // @Prod.fst.{u,v} α β p  /  @Prod.snd.{u,v} α β p — reducible
            // definitions over `Expr::proj`, which is what the compiler lowers
            // (`l_Prod_fst` / `l_Prod_snd` appear source-lowered in the emitted
            // C and run, measured 2026-09-16 through `clean compile --emit c`).
            let fst = Expr::apps(
                Expr::const_(
                    Name::from_string("Prod.fst"),
                    vec![u_level.clone(), v_level.clone()],
                ),
                [alpha.clone(), beta.clone(), p.clone()],
            );
            let snd = Expr::apps(
                Expr::const_(
                    Name::from_string("Prod.snd"),
                    vec![u_level.clone(), v_level.clone()],
                ),
                [alpha.clone(), beta.clone(), p],
            );
            // Each component through its OWN instance: `@ToString.toString.{u} α ia`
            // for the left and `.{v} β ib` for the right.
            let render_fst = Expr::apps(
                Expr::const_(
                    Name::from_string("ToString.toString"),
                    vec![u_level.clone()],
                ),
                [alpha.clone(), ia, fst],
            );
            let render_snd = Expr::apps(
                Expr::const_(
                    Name::from_string("ToString.toString"),
                    vec![v_level.clone()],
                ),
                [beta.clone(), ib, snd],
            );
            // "(" ++ toString a ++ ", " ++ toString b ++ ")", left-nested
            // exactly as Lean's four `String.Internal.append`s are.
            let body = Expr::apps(
                append.clone(),
                [
                    Expr::apps(
                        append.clone(),
                        [
                            Expr::apps(
                                append.clone(),
                                [
                                    Expr::apps(append.clone(), [Expr::str_lit("("), render_fst]),
                                    Expr::str_lit(", "),
                                ],
                            ),
                            render_snd,
                        ],
                    ),
                    Expr::str_lit(")"),
                ],
            );
            let tostring_fn = b.mk_lam(p_id, BinderInfo::Default, prod_ab.clone(), body);
            let value = Expr::apps(
                Expr::const_(Name::from_string("ToString.mk"), vec![uv_level.clone()]),
                [prod_ab, tostring_fn],
            );
            let r = b.mk_lam(ib_id, BinderInfo::InstImplicit, ts_beta, value);
            let r = b.mk_lam(ia_id, BinderInfo::InstImplicit, ts_alpha, r);
            let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instToStringProd"),
            level_params: vec![u, v],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instToStringProd"),
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
            "instToStringUInt8",
            "instToStringUInt16",
            "instToStringUInt32",
            "instToStringUInt64",
            "instToStringUSize",
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

    /// `instToStringOption` and `instToStringProd` are registered by the
    /// prelude, are `Definition`s that retain their value, type-check at their
    /// own level ARITY, carry an empty axiom closure, and are visible to
    /// instance search as `ToString` candidates.
    ///
    /// Measured before they were registered (`clean check`, 2026-09-16):
    /// `toString (some 3 : Option Nat)` failed with "failed to synthesize
    /// instance `ToString (Option Nat)`" and `toString ((1, 2) : Nat × Nat)`
    /// with "failed to synthesize instance `ToString (Prod Nat Nat)`".
    ///
    /// The arity leg is the discriminating one and is why the two are checked
    /// at different level lists: `instToStringOption` takes ONE level parameter
    /// and `instToStringProd` takes TWO (its carrier is
    /// `ToString.{max u v} (Prod.{u,v} α β)`). A registration that declared the
    /// wrong `level_params` fails `infer_type` here rather than at some later
    /// use site.
    #[test]
    fn test_tostring_option_and_prod_instances_registered() {
        let env = Environment::with_prelude();
        for (name, levels) in [
            ("instToStringOption", vec![Level::zero()]),
            ("instToStringProd", vec![Level::zero(), Level::zero()]),
        ] {
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
                .infer_type(&Expr::const_(Name::from_string(name), levels))
                .unwrap_or_else(|e| panic!("{name} should type-check: {e:?}"));

            let deps = env
                .axiom_deps(&Name::from_string(name))
                .unwrap_or_else(|| panic!("{name} is registered"));
            let axioms: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
            assert!(
                axioms.is_empty(),
                "{name} must have empty axiom closure, got {axioms:?}"
            );

            assert!(
                env.is_instance(&Name::from_string(name)),
                "{name} must be registered as an instance"
            );
            let candidates: Vec<String> = env
                .get_class_instances(&Name::from_string("ToString"))
                .iter()
                .map(|i| i.name.to_string())
                .collect();
            assert!(
                candidates.iter().any(|n| n == name),
                "{name} must be a ToString candidate, got {candidates:?}"
            );
        }
    }
}
