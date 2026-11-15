// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The opaque renderer behind every default-prelude `Repr` stub, and the
//! `Repr` instances for the compound carriers `Option α` and `α × β`.
//!
//! ## Why the renderer is opaque
//!
//! Lean's `Repr` is `Std.Format`-valued; the default prelude models it as
//! `String`-valued (`data_typeclasses_repr`), so no rendering it produces can
//! be Lean's text. What the model CAN keep is Lean's equalities: two renderings
//! that Lean distinguishes must never be definitionally equal here. The earlier
//! stub bodies (`fun _ _ => ""`, and `fun _ _ => "S"` for a derived structure)
//! broke that — `repr (1 : Nat) = repr (2 : Nat) := rfl` and
//! `repr (S.mk 1) = repr (S.mk 2) := rfl` were ACCEPTED by `clean check` and
//! are refused by Lean 4.8 (`type mismatch`, measured 2026-09-30 with the
//! pinned toolchain as oracle).
//!
//! Every stub rendering is therefore `Clean.Repr.render x prec` for an
//! [`Declaration::Opaque`] `Clean.Repr.render` — the `Rat.abs` co-demotion
//! pattern (`algebra_abs.rs`): the constant has a value, so it is not an axiom,
//! but δ-reduction never unfolds it, so two renderings are definitionally equal
//! only when their arguments are. A rendering that depends on instance
//! arguments (`Repr (Option α)` renders through `[Repr α]`) passes those
//! instances INTO the renderer, packed with the value as a `Prod`, so two
//! different element instances never collapse to one rendering either.
//!
//! What this gives up, deliberately: `repr (none : Option Nat) = "none" := rfl`
//! is true in Lean and is refused here. That is the fail-closed direction; the
//! Lean-faithful fix is a `Std.Format`-valued `Repr`, which is open (see
//! `docs/FRONTEND_CLASS_LEDGER.md`, class "Repr model").
//!
//! ## The compound instances
//!
//! - `instReprOption : {α : Type u} → [Repr α] → Repr (Option α)` — Lean's
//!   name and Lean's type (`Init/Data/Repr.lean`).
//! - `Clean.instReprProdOfRepr : {α : Type u} → {β : Type v} → [Repr α] →
//!   [Repr β] → Repr (α × β)`. Lean's instance is `instReprProdOfReprTuple`,
//!   whose second premise is `[ReprTuple β]`; `ReprTuple`'s field is
//!   `α → List Format → List Format`, which this `String` model cannot state
//!   without a new type-differing collision with Lean's class. The two
//!   instance sets resolve exactly the same goals — `ReprTuple β` is
//!   derivable from Lean's three instances iff `Repr β` is, by induction on
//!   the right-nested product — so this instance takes `[Repr β]` and a
//!   name in the `Clean` namespace. Neither Lean name fits: Lean's own
//!   (`instReprProdOfReprTuple`) would be a same-name, different-type
//!   collision, and the bare `instReprProdOfRepr` is the name Lean
//!   auto-generates for a USER's `instance [Repr α] [Repr β] : Repr (α × β)`,
//!   which a Lean-valid file may declare and which must not collide here.
//!
//! Both are wired from `init_repr`, so they inherit its import-mode
//! suppression: under `.olean` import Lean's genuine `Format`-valued instances
//! arrive through the checked import path instead.

use super::decl_builder::EnvDeclBuilder;
use crate::env::{
    Declaration, EnvError, Environment, KernelInstanceInfo, LEAN_DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

/// Name of the opaque renderer every default-prelude `Repr` stub routes
/// through.
pub(crate) const REPR_RENDER: &str = "Clean.Repr.render";

/// `@Clean.Repr.render.{level} carrier : carrier → Nat → String`.
pub(crate) fn repr_render_at(level: Level, carrier: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string(REPR_RENDER), vec![level]),
        carrier,
    )
}

/// `fun (x : carrier) => @Clean.Repr.render (insts_ty × carrier) (insts, x)`,
/// i.e. a `carrier → Nat → String` rendering that depends on the instance
/// arguments `insts : insts_ty` as well as on the value.
///
/// `insts_level` / `carrier_level` are the `u` in `insts_ty : Type u` /
/// `carrier : Type u`; the packed `Prod` lives at `Type (max a b)`.
pub(crate) fn packed_render_fn(
    b: &EnvDeclBuilder,
    insts_ty: &Expr,
    insts_level: &Level,
    insts: &Expr,
    carrier: &Expr,
    carrier_level: &Level,
) -> Expr {
    let mut c = EnvDeclBuilder::child_of(b);
    let (x_id, x) = c.fresh_local(carrier.clone());
    let prod_levels = vec![insts_level.clone(), carrier_level.clone()];
    let packed_ty = Expr::apps(
        Expr::const_(Name::from_string("Prod"), prod_levels.clone()),
        [insts_ty.clone(), carrier.clone()],
    );
    let packed = Expr::apps(
        Expr::const_(Name::from_string("Prod.mk"), prod_levels),
        [insts_ty.clone(), carrier.clone(), insts.clone(), x],
    );
    let render_level = Level::max(insts_level.clone(), carrier_level.clone());
    let body = Expr::app(repr_render_at(render_level, packed_ty), packed);
    let r = c.mk_lam(x_id, BinderInfo::Default, carrier.clone(), body);
    c.finish_child(r)
}

impl Environment {
    /// Register the opaque `Clean.Repr.render.{u} : {α : Type u} → α → Nat →
    /// String`. Its value (`fun _ _ => ""`) is the witness that makes it a
    /// definition rather than an axiom; being `Opaque`, it is never unfolded.
    pub(crate) fn init_repr_render(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string(REPR_RENDER)).is_some() {
            return Ok(());
        }
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level)));
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let string_const = Expr::const_(Name::from_string("String"), vec![]);

        let render_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (x_id, _x) = b.fresh_local(alpha.clone());
            let (n_id, _n) = b.fresh_local(nat_const.clone());
            let r = b.mk_pi(
                n_id,
                BinderInfo::Default,
                nat_const.clone(),
                string_const.clone(),
            );
            let r = b.mk_pi(x_id, BinderInfo::Default, alpha, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        let render_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (x_id, _x) = b.fresh_local(alpha.clone());
            let (n_id, _n) = b.fresh_local(nat_const.clone());
            let r = b.mk_lam(
                n_id,
                BinderInfo::Default,
                nat_const.clone(),
                Expr::str_lit(""),
            );
            let r = b.mk_lam(x_id, BinderInfo::Default, alpha, r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u, r);
            b.finish(r)
        };
        self.add_decl(Declaration::Opaque {
            name: Name::from_string(REPR_RENDER),
            level_params: vec![u],
            type_: render_type,
            value: render_value,
        })
    }

    /// Register `instReprOption` and `Clean.instReprProdOfRepr` (module docs).
    ///
    /// A cut-down environment without `Option` / `Prod` skips the instance it
    /// cannot state, keeping the pre-existing "failed to synthesize" refusal
    /// rather than failing prelude construction (the `add_tostring_*` shape).
    pub(crate) fn init_repr_compound_instances(&mut self) -> Result<(), EnvError> {
        if self.get_const(&Name::from_string("Option")).is_some() {
            self.add_repr_option_instance()?;
        }
        if self.get_const(&Name::from_string("Prod.mk")).is_some() {
            self.add_repr_prod_instance()?;
        }
        Ok(())
    }

    /// `instReprOption.{u} : {α : Type u} → [Repr α] → Repr (Option α)
    ///   := fun {α} [inst] => Repr.mk (Option α) (fun o => render (inst, o))`.
    fn add_repr_option_instance(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let repr_at = |carrier: Expr| {
            Expr::app(
                Expr::const_(Name::from_string("Repr"), vec![u_level.clone()]),
                carrier,
            )
        };
        let option_of = |alpha: &Expr| {
            Expr::app(
                Expr::const_(Name::from_string("Option"), vec![u_level.clone()]),
                alpha.clone(),
            )
        };

        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, _inst) = b.fresh_local(repr_at(alpha.clone()));
            let r = repr_at(option_of(&alpha));
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, repr_at(alpha.clone()), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (inst_id, inst) = b.fresh_local(repr_at(alpha.clone()));
            let option_alpha = option_of(&alpha);
            let render_fn = packed_render_fn(
                &b,
                &repr_at(alpha.clone()),
                &u_level,
                &inst,
                &option_alpha,
                &u_level,
            );
            let body = Expr::apps(
                Expr::const_(Name::from_string("Repr.mk"), vec![u_level.clone()]),
                [option_alpha, render_fn],
            );
            let r = b.mk_lam(
                inst_id,
                BinderInfo::InstImplicit,
                repr_at(alpha.clone()),
                body,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_repr_instance_decl("instReprOption", vec![u], inst_type, inst_value)
    }

    /// `Clean.instReprProdOfRepr.{u,v} : {α : Type u} → {β : Type v} → [Repr α] →
    ///   [Repr β] → Repr (α × β)
    ///   := fun {α β} [ia] [ib] => Repr.mk (α × β) (fun p => render ((ia, ib), p))`.
    fn add_repr_prod_instance(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let uv_level = Level::max(u_level.clone(), v_level.clone());
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(u_level.clone())));
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(v_level.clone())));
        let repr_at = |level: &Level, carrier: Expr| {
            Expr::app(
                Expr::const_(Name::from_string("Repr"), vec![level.clone()]),
                carrier,
            )
        };
        let prod_levels = vec![u_level.clone(), v_level.clone()];
        let prod_of = |a: Expr, b: Expr| {
            Expr::apps(
                Expr::const_(Name::from_string("Prod"), prod_levels.clone()),
                [a, b],
            )
        };

        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let repr_alpha = repr_at(&u_level, alpha.clone());
            let repr_beta = repr_at(&v_level, beta.clone());
            let (ia_id, _ia) = b.fresh_local(repr_alpha.clone());
            let (ib_id, _ib) = b.fresh_local(repr_beta.clone());
            let r = repr_at(&uv_level, prod_of(alpha.clone(), beta.clone()));
            let r = b.mk_pi(ib_id, BinderInfo::InstImplicit, repr_beta, r);
            let r = b.mk_pi(ia_id, BinderInfo::InstImplicit, repr_alpha, r);
            let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let repr_alpha = repr_at(&u_level, alpha.clone());
            let repr_beta = repr_at(&v_level, beta.clone());
            let (ia_id, ia) = b.fresh_local(repr_alpha.clone());
            let (ib_id, ib) = b.fresh_local(repr_beta.clone());
            // The two element instances, packed as `(ia, ib) : Repr α × Repr β`.
            let insts_ty = prod_of(repr_alpha.clone(), repr_beta.clone());
            let insts = Expr::apps(
                Expr::const_(Name::from_string("Prod.mk"), prod_levels.clone()),
                [repr_alpha.clone(), repr_beta.clone(), ia, ib],
            );
            let prod_ab = prod_of(alpha.clone(), beta.clone());
            let render_fn = packed_render_fn(&b, &insts_ty, &uv_level, &insts, &prod_ab, &uv_level);
            let body = Expr::apps(
                Expr::const_(Name::from_string("Repr.mk"), vec![uv_level.clone()]),
                [prod_ab, render_fn],
            );
            let r = b.mk_lam(ib_id, BinderInfo::InstImplicit, repr_beta, body);
            let r = b.mk_lam(ia_id, BinderInfo::InstImplicit, repr_alpha, r);
            let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_repr_instance_decl(
            "Clean.instReprProdOfRepr",
            vec![u, v],
            inst_type,
            inst_value,
        )
    }

    /// Add a reducible instance definition and register it under `Repr` at
    /// Lean's default priority.
    fn add_repr_instance_decl(
        &mut self,
        name: &str,
        level_params: Vec<Name>,
        type_: Expr,
        value: Expr,
    ) -> Result<(), EnvError> {
        self.add_decl(Declaration::Definition {
            name: Name::from_string(name),
            level_params,
            type_,
            value,
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string(name),
            class_name: Name::from_string("Repr"),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }
}

#[cfg(test)]
#[path = "data_typeclasses_repr_compound_tests.rs"]
mod tests;
