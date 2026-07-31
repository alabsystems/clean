// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Option and List operations initialization for Environment
//!
//! This module contains:
//! - Option operations (map, bind, getD)
//! - List operations (append, reverse, map)

use super::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Add Option.map : {α β : Type u} → (α → β) → Option α → Option β
    /// Add Option.bind : {α β : Type u} → Option α → (α → Option β) → Option β
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.option_ops_init == true`
    /// ENSURES: On success, required dependencies (`option`, `unit`, `bool`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_option_ops(&mut self) -> Result<(), EnvError> {
        if self.option_ops_init {
            return Ok(());
        }

        // Ensure Option is initialized
        self.init_option()?;
        // `Option.orElse`'s thunk argument `Unit → Option α` references `Unit`,
        // so guarantee `Unit`/`Unit.unit` exist before we register it.
        self.init_unit()?;
        // `Option.isSome`/`isNone` land in `Bool` and `Option.filter` folds a
        // `Bool.rec` over its predicate, so `Bool`/`Bool.true`/`Bool.false`
        // must exist before those declarations are type-checked. Without this
        // the first `Option.isSome` add fails `UnknownConst(Bool)` in any
        // environment that has not already initialized `Bool` for other
        // reasons — which is exactly what a focused `Environment::new()` test
        // constructs.
        self.init_bool()?;

        let u = Name::from_string("u");
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));

        let option_const = Expr::const_(Name::from_string("Option"), vec![Level::param(u.clone())]);
        let option_none = Expr::const_(
            Name::from_string("Option.none"),
            vec![Level::param(u.clone())],
        );
        let option_some = Expr::const_(
            Name::from_string("Option.some"),
            vec![Level::param(u.clone())],
        );
        // Second universe `v` for the codomain `β`, matching Lean's real
        // `Option.map`/`Option.bind : {α : Type u_1} {β : Type u_2} → …`. Using a
        // single universe for both collapsed the arity and made every reference
        // that instantiates α and β at distinct universes raise LevelCountMismatch.
        let v = Name::from_string("v");
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(v.clone()))));
        let option_const_b =
            Expr::const_(Name::from_string("Option"), vec![Level::param(v.clone())]);
        let option_none_b = Expr::const_(
            Name::from_string("Option.none"),
            vec![Level::param(v.clone())],
        );
        let option_some_b = Expr::const_(
            Name::from_string("Option.some"),
            vec![Level::param(v.clone())],
        );
        // Eliminate `Option α` (Type u) into a motive returning `Option β` (Type v
        // = Sort (v+1)); Option.rec universes are [motive-elim, type] = [succ v, u].
        let option_rec_uv = Expr::const_(
            Name::from_string("Option.rec"),
            vec![
                Level::succ(Level::param(v.clone())),
                Level::param(u.clone()),
            ],
        );

        // Option.map : {α : Type u} {β : Type v} → (α → β) → Option α → Option β
        let map_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let f_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(alpha.clone());
                let r = beta.clone();
                let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            let (opt_id, _opt) = b.fresh_local(Expr::app(option_const.clone(), alpha.clone()));
            let r = Expr::app(option_const_b.clone(), beta.clone());
            let r = b.mk_pi(
                opt_id,
                BinderInfo::Default,
                Expr::app(option_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
            let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // Option.map value: λ {α} {β} (f : α → β) (opt : Option α) => Option.rec α motive none_case some_case opt
        let map_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let f_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(alpha.clone());
                let r = beta.clone();
                let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let (opt_id, opt) = b.fresh_local(Expr::app(option_const.clone(), alpha.clone()));

            // motive: λ (_ : Option α) => Option β
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(Expr::app(option_const.clone(), alpha.clone()));
                let r = Expr::app(option_const_b.clone(), beta.clone());
                let r = c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    Expr::app(option_const.clone(), alpha.clone()),
                    r,
                );
                c.finish_child(r)
            };
            let none_case = Expr::app(option_none_b.clone(), beta.clone());
            // some case: λ (a : α) => Option.some β (f a)
            let some_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(alpha.clone());
                let r = Expr::app(
                    Expr::app(option_some_b.clone(), beta.clone()),
                    Expr::app(f.clone(), a),
                );
                let r = c.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };

            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(option_rec_uv.clone(), alpha.clone()), motive),
                        none_case,
                    ),
                    some_case,
                ),
                opt,
            );
            let r = b.mk_lam(
                opt_id,
                BinderInfo::Default,
                Expr::app(option_const.clone(), alpha.clone()),
                body,
            );
            let r = b.mk_lam(f_id, BinderInfo::Default, f_ty, r);
            let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Option.map"),
            level_params: vec![u.clone(), v.clone()],
            type_: map_type,
            value: map_value,
            is_reducible: true,
        })?;

        // Option.bind : {α β : Type u} → Option α → (α → Option β) → Option β
        let bind_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let (opt_id, _opt) = b.fresh_local(Expr::app(option_const.clone(), alpha.clone()));
            let f_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(alpha.clone());
                let r = Expr::app(option_const_b.clone(), beta.clone());
                let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (f_id, _f) = b.fresh_local(f_ty.clone());
            let r = Expr::app(option_const_b.clone(), beta.clone());
            let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
            let r = b.mk_pi(
                opt_id,
                BinderInfo::Default,
                Expr::app(option_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // Option.bind value: λ {α} {β} (opt) (f) => Option.rec α motive none f opt
        let bind_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let (opt_id, opt) = b.fresh_local(Expr::app(option_const.clone(), alpha.clone()));
            let f_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(alpha.clone());
                let r = Expr::app(option_const_b.clone(), beta.clone());
                let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (f_id, f) = b.fresh_local(f_ty.clone());

            // motive: λ (_ : Option α) => Option β
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(Expr::app(option_const.clone(), alpha.clone()));
                let r = Expr::app(option_const_b.clone(), beta.clone());
                let r = c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    Expr::app(option_const.clone(), alpha.clone()),
                    r,
                );
                c.finish_child(r)
            };
            let none_case = Expr::app(option_none_b.clone(), beta.clone());
            let some_case = f; // f already has type α → Option β

            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(option_rec_uv.clone(), alpha.clone()), motive),
                        none_case,
                    ),
                    some_case,
                ),
                opt,
            );
            let r = b.mk_lam(f_id, BinderInfo::Default, f_ty, body);
            let r = b.mk_lam(
                opt_id,
                BinderInfo::Default,
                Expr::app(option_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Option.bind"),
            level_params: vec![u.clone(), v.clone()],
            type_: bind_type,
            value: bind_value,
            is_reducible: true,
        })?;

        // Option.getD : {α : Type u} → Option α → α → α
        let getd_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (opt_id, _opt) = b.fresh_local(Expr::app(option_const.clone(), alpha.clone()));
            let (def_id, _def) = b.fresh_local(alpha.clone());
            let r = alpha.clone();
            let r = b.mk_pi(def_id, BinderInfo::Default, alpha.clone(), r);
            let r = b.mk_pi(
                opt_id,
                BinderInfo::Default,
                Expr::app(option_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // Option.getD value: λ {α} (opt) (default) => Option.rec α motive default id opt
        let getd_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (opt_id, opt) = b.fresh_local(Expr::app(option_const.clone(), alpha.clone()));
            let (def_id, def_val) = b.fresh_local(alpha.clone());

            let option_rec_u = Expr::const_(
                Name::from_string("Option.rec"),
                vec![
                    Level::succ(Level::param(u.clone())),
                    Level::param(u.clone()),
                ],
            );

            // motive: λ (_ : Option α) => α
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(Expr::app(option_const.clone(), alpha.clone()));
                let r = alpha.clone();
                let r = c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    Expr::app(option_const.clone(), alpha.clone()),
                    r,
                );
                c.finish_child(r)
            };
            // some case: λ (a : α) => a (identity)
            let id_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(alpha.clone());
                let r = a;
                let r = c.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };

            let body = Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::app(option_rec_u, alpha.clone()), motive),
                        def_val,
                    ),
                    id_case,
                ),
                opt,
            );
            let r = b.mk_lam(def_id, BinderInfo::Default, alpha.clone(), body);
            let r = b.mk_lam(
                opt_id,
                BinderInfo::Default,
                Expr::app(option_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("Option.getD"),
            level_params: vec![u.clone()],
            type_: getd_type,
            value: getd_value,
            is_reducible: true,
        })?;

        // Option.isSome / Option.isNone : {α : Type u} → Option α → Bool
        // Both are simple `Option.rec` folds into `Bool` (Sort 1), so the
        // recursor's motive universe is the concrete `1` (= `succ zero`) rather
        // than the `succ u` used by the value-returning `Option.getD` above.
        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_true = Expr::const_(Name::from_string("Bool.true"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        let option_rec_bool = Expr::const_(
            Name::from_string("Option.rec"),
            vec![Level::succ(Level::zero()), Level::param(u.clone())],
        );

        // `{α : Type u} → Option α → Bool` — shared by both predicates.
        let pred_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (opt_id, _opt) = b.fresh_local(Expr::app(option_const.clone(), alpha.clone()));
            let r = bool_const.clone();
            let r = b.mk_pi(
                opt_id,
                BinderInfo::Default,
                Expr::app(option_const.clone(), alpha.clone()),
                r,
            );
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        // λ {α} (o : Option α) => Option.rec (λ _ => Bool) <none> (λ _ => <some>) o
        let build_pred = |none_val: &Expr, some_val: &Expr| {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (opt_id, opt) = b.fresh_local(Expr::app(option_const.clone(), alpha.clone()));
            // motive: λ (_ : Option α) => Bool
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(Expr::app(option_const.clone(), alpha.clone()));
                let r = bool_const.clone();
                let r = c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    Expr::app(option_const.clone(), alpha.clone()),
                    r,
                );
                c.finish_child(r)
            };
            // some case: λ (_ : α) => some_val
            let some_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, _a) = c.fresh_local(alpha.clone());
                let r = some_val.clone();
                let r = c.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let body = Expr::apps(
                option_rec_bool.clone(),
                [alpha.clone(), motive, none_val.clone(), some_case, opt],
            );
            let r = b.mk_lam(
                opt_id,
                BinderInfo::Default,
                Expr::app(option_const.clone(), alpha.clone()),
                body,
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        if self
            .get_const(&Name::from_string("Option.isSome"))
            .is_none()
        {
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Option.isSome"),
                level_params: vec![u.clone()],
                type_: pred_type.clone(),
                value: build_pred(&bool_false, &bool_true),
                is_reducible: true,
            })?;
        }
        if self
            .get_const(&Name::from_string("Option.isNone"))
            .is_none()
        {
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Option.isNone"),
                level_params: vec![u.clone()],
                type_: pred_type,
                value: build_pred(&bool_true, &bool_false),
                is_reducible: true,
            })?;
        }

        // Option.orElse : {α : Type u} → Option α → (Unit → Option α) → Option α
        // Lean `Init/Prelude.lean`:
        //   protected def Option.orElse : Option α → (Unit → Option α) → Option α
        //     | some a, _ => some a
        //     | none,   b => b ()
        // The second argument is a THUNK (`Unit → Option α`) so the fallback is
        // only forced in the `none` case. Registered as a reducible axiom-free
        // `Option.rec` fold whose motive returns `Option α` (`Type u`, elim
        // universe `succ u`), matching `Option.getD`'s `Option.rec.{succ u, u}`.
        if self
            .get_const(&Name::from_string("Option.orElse"))
            .is_none()
        {
            let unit_const = Expr::const_(Name::from_string("Unit"), vec![]);
            let unit_unit = Expr::const_(Name::from_string("Unit.unit"), vec![]);
            let option_rec_u = Expr::const_(
                Name::from_string("Option.rec"),
                vec![
                    Level::succ(Level::param(u.clone())),
                    Level::param(u.clone()),
                ],
            );

            // Build `Unit → Option α` as a child of `parent` so the embedded
            // `alpha` fvar is abstracted later by the parent (a fresh
            // `EnvDeclBuilder::new()` restarts the fvar counter at the same base
            // and would collide with `alpha`). Non-dependent: `Unit` is unused.
            let thunk_ty = |parent: &EnvDeclBuilder, alpha: &Expr| {
                let mut c = EnvDeclBuilder::child_of(parent);
                let (unit_id, _unit) = c.fresh_local(unit_const.clone());
                let r = Expr::app(option_const.clone(), alpha.clone());
                let r = c.mk_pi(unit_id, BinderInfo::Default, unit_const.clone(), r);
                c.finish_child(r)
            };

            // Option.orElse type
            let orelse_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (opt_id, _opt) = b.fresh_local(Expr::app(option_const.clone(), alpha.clone()));
                let thunk_type = thunk_ty(&b, &alpha);
                let (thunk_id, _thunk) = b.fresh_local(thunk_type.clone());
                let r = Expr::app(option_const.clone(), alpha.clone());
                let r = b.mk_pi(thunk_id, BinderInfo::Default, thunk_type, r);
                let r = b.mk_pi(
                    opt_id,
                    BinderInfo::Default,
                    Expr::app(option_const.clone(), alpha.clone()),
                    r,
                );
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            // Option.orElse value:
            //   λ {α} (o : Option α) (thunk : Unit → Option α) =>
            //     @Option.rec α (λ _ => Option α) (thunk ()) (λ a => some a) o
            let orelse_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (opt_id, opt) = b.fresh_local(Expr::app(option_const.clone(), alpha.clone()));
                let thunk_type = thunk_ty(&b, &alpha);
                let (thunk_id, thunk) = b.fresh_local(thunk_type.clone());

                // motive: λ (_ : Option α) => Option α
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(Expr::app(option_const.clone(), alpha.clone()));
                    let r = Expr::app(option_const.clone(), alpha.clone());
                    let r = c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        Expr::app(option_const.clone(), alpha.clone()),
                        r,
                    );
                    c.finish_child(r)
                };
                // none case: thunk () — force the fallback thunk.
                let none_case = Expr::app(thunk.clone(), unit_unit.clone());
                // some case: λ (a : α) => @Option.some α a  (reconstruct `some a`)
                let some_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, a) = c.fresh_local(alpha.clone());
                    let r = Expr::apps(option_some.clone(), [alpha.clone(), a]);
                    let r = c.mk_lam(a_id, BinderInfo::Default, alpha.clone(), r);
                    c.finish_child(r)
                };

                let body = Expr::apps(
                    option_rec_u,
                    [alpha.clone(), motive, none_case, some_case, opt],
                );
                let r = b.mk_lam(thunk_id, BinderInfo::Default, thunk_type, body);
                let r = b.mk_lam(
                    opt_id,
                    BinderInfo::Default,
                    Expr::app(option_const.clone(), alpha.clone()),
                    r,
                );
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("Option.orElse"),
                level_params: vec![u.clone()],
                type_: orelse_type,
                value: orelse_value,
                is_reducible: true,
            })?;
        }

        // Option.filter : {α : Type u} → (α → Bool) → Option α → Option α
        // Lean `Init/Data/Option/Basic.lean`:
        //   def Option.filter (p : α → Bool) : Option α → Option α
        //     | some a => if p a then some a else none
        //     | none   => none
        // Registered as a reducible axiom-free `Option.rec` fold whose some-case
        // NESTS a `Bool.rec` to test `p a` (mirrors `List.find?` above). Both the
        // outer motive and the inner Bool motive land in `Option α` (Type u), so
        // `Option.rec.{succ u, u}` and `Bool.rec.{succ u}`. Bool.rec minor order
        // is [false_case, true_case] (false ↦ none — dropped, true ↦ some a —
        // kept). Without this, `o.filter p` failed with UnknownIdent.
        if self
            .get_const(&Name::from_string("Option.filter"))
            .is_none()
        {
            let option_rec_filter = Expr::const_(
                Name::from_string("Option.rec"),
                vec![
                    Level::succ(Level::param(u.clone())),
                    Level::param(u.clone()),
                ],
            );
            let bool_rec_filter = Expr::const_(
                Name::from_string("Bool.rec"),
                vec![Level::succ(Level::param(u.clone()))],
            );

            // Option.filter type
            let filter_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let option_alpha = Expr::app(option_const.clone(), alpha.clone());
                // p : α → Bool (non-dependent; α is a parent fvar in the domain)
                let p_ty = Expr::pi(BinderInfo::Default, alpha.clone(), bool_const.clone());
                let (p_id, _p) = b.fresh_local(p_ty.clone());
                let (o_id, _o) = b.fresh_local(option_alpha.clone());
                let r = option_alpha.clone();
                let r = b.mk_pi(o_id, BinderInfo::Default, option_alpha.clone(), r);
                let r = b.mk_pi(p_id, BinderInfo::Default, p_ty, r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            // Option.filter value:
            //   λ {α} (p : α → Bool) (o : Option α) =>
            //     @Option.rec α (λ _ => Option α) none
            //       (λ a => @Bool.rec (λ _ => Option α) none (some a) (p a)) o
            let filter_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let option_alpha = Expr::app(option_const.clone(), alpha.clone());
                let p_ty = Expr::pi(BinderInfo::Default, alpha.clone(), bool_const.clone());
                let (p_id, p) = b.fresh_local(p_ty.clone());
                let (o_id, o) = b.fresh_local(option_alpha.clone());

                // outer Option.rec motive: λ (_ : Option α) => Option α
                let option_motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(option_alpha.clone());
                    let r = c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        option_alpha.clone(),
                        option_alpha.clone(),
                    );
                    c.finish_child(r)
                };
                let none_case = Expr::app(option_none.clone(), alpha.clone());

                // some case: λ (a : α) =>
                //   @Bool.rec (λ _ => Option α) none (some a) (p a)
                let some_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, a) = c.fresh_local(alpha.clone());
                    // inner Bool.rec motive: λ (_ : Bool) => Option α
                    let bool_motive = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (bm_id, _bm) = d.fresh_local(bool_const.clone());
                        let r = d.mk_lam(
                            bm_id,
                            BinderInfo::Default,
                            bool_const.clone(),
                            option_alpha.clone(),
                        );
                        d.finish_child(r)
                    };
                    let inner_none = Expr::app(option_none.clone(), alpha.clone());
                    let some_a = Expr::apps(option_some.clone(), [alpha.clone(), a.clone()]);
                    let p_a = Expr::app(p.clone(), a.clone());
                    // Bool.rec motive false_case true_case major
                    let inner = Expr::apps(
                        bool_rec_filter.clone(),
                        [bool_motive, inner_none, some_a, p_a],
                    );
                    let r = c.mk_lam(a_id, BinderInfo::Default, alpha.clone(), inner);
                    c.finish_child(r)
                };

                let body = Expr::apps(
                    option_rec_filter,
                    [
                        alpha.clone(),
                        option_motive,
                        none_case,
                        some_case,
                        o.clone(),
                    ],
                );
                let r = b.mk_lam(o_id, BinderInfo::Default, option_alpha.clone(), body);
                let r = b.mk_lam(p_id, BinderInfo::Default, p_ty, r);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("Option.filter"),
                level_params: vec![u.clone()],
                type_: filter_type,
                value: filter_value,
                is_reducible: true,
            })?;
        }

        self.option_ops_init = true;
        Ok(())
    }

    /// Check if Option operations have been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_option_ops` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_option_ops(&self) -> bool {
        self.option_ops_init
    }

    /// Add List operations: append, reverse, map
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.list_ops_init == true`
    /// ENSURES: On success, required dependencies (`list`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_list_ops(&mut self) -> Result<(), EnvError> {
        if self.list_ops_init {
            return Ok(());
        }

        // Ensure List is initialized
        self.init_list()?;
        // List.zip returns `List (α × β)`, so Prod must be available (it is not
        // implied by init_list; a bare Environment::new() lacks it).
        self.init_prod()?;

        let u = Name::from_string("u");
        let type_u = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone()))));

        let list_const = Expr::const_(Name::from_string("List"), vec![Level::param(u.clone())]);
        let list_nil = Expr::const_(Name::from_string("List.nil"), vec![Level::param(u.clone())]);
        let list_cons = Expr::const_(
            Name::from_string("List.cons"),
            vec![Level::param(u.clone())],
        );
        let list_rec = Expr::const_(
            Name::from_string("List.rec"),
            vec![
                Level::succ(Level::param(u.clone())),
                Level::param(u.clone()),
            ],
        );

        // Second universe `v` for the codomain of `List.map` ({α : Type u}
        // {β : Type v}, matching Lean); the single-universe seed raised
        // LevelCountMismatch on cross-universe instantiations.
        let v = Name::from_string("v");
        let type_v = Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(v.clone()))));
        let list_const_b = Expr::const_(Name::from_string("List"), vec![Level::param(v.clone())]);
        let list_nil_b = Expr::const_(Name::from_string("List.nil"), vec![Level::param(v.clone())]);
        let list_cons_b = Expr::const_(
            Name::from_string("List.cons"),
            vec![Level::param(v.clone())],
        );
        // Eliminate `List α` (Type u) into a motive returning `List β`
        // (Type v = Sort (v+1)): List.rec universes [motive-elim, type] = [succ v, u].
        let list_rec_uv = Expr::const_(
            Name::from_string("List.rec"),
            vec![
                Level::succ(Level::param(v.clone())),
                Level::param(u.clone()),
            ],
        );

        // IMPORT MODE (`suppress_lossy_structure_stubs`, v4.30 census
        // 2026-07-06): `List.append`, `List.reverseAux`, `List.map`,
        // `List.set`, `List.find?`, `List.filter` and `List.replicate` below
        // are direct `List.rec`/`Nat.rec` eliminations — Lean v4.30 stores
        // brecOn towers, so each seeded twin fails the value-defeq dedup
        // ("value not definitionally equal") and every eq_def/lemma
        // elaborated through the genuine body cascades (Init.Prelude /
        // Init.Data.List.Basic). `List.reverse` (`reverseAux · []`) is itself
        // structurally olean-faithful but references the gated `reverseAux`,
        // which no longer exists at seed time, so it rides the same gate. The
        // seeded lemmas `List.append_nil` / `List.length_nil` /
        // `List.length_cons` / `List.length_append` state goals over the
        // gated seeds and are gated with them. Import-suppressed (WS17
        // pattern): the genuine olean definitions import through the checked
        // add_decl path; the default proof-execution lane is unchanged.
        // (`List.get?` and the Option combinators are NOT part of the
        // divergent cluster and stay in both lanes.)

        // List.append : {α : Type u} → List α → List α → List α
        if !self.suppress_lossy_structure_stubs {
            let append_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let (xs_id, _xs) = b.fresh_local(list_alpha.clone());
                let (ys_id, _ys) = b.fresh_local(list_alpha.clone());
                let r = list_alpha.clone();
                let r = b.mk_pi(ys_id, BinderInfo::Default, list_alpha.clone(), r);
                let r = b.mk_pi(xs_id, BinderInfo::Default, list_alpha.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            // append xs ys := List.rec α motive ys cons_case xs
            let append_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let (xs_id, xs) = b.fresh_local(list_alpha.clone());
                let (ys_id, ys) = b.fresh_local(list_alpha.clone());

                // motive: λ (_ : List α) => List α
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_alpha.clone());
                    let r = list_alpha.clone();
                    let r = c.mk_lam(w_id, BinderInfo::Default, list_alpha.clone(), r);
                    c.finish_child(r)
                };

                // cons case: λ (x : α) (_ : List α) (ih : List α) => cons α x ih
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (x_id, x) = c.fresh_local(alpha.clone());
                    let (tail_id, _tail) = c.fresh_local(list_alpha.clone());
                    let (ih_id, ih) = c.fresh_local(list_alpha.clone());
                    let r = Expr::app(
                        Expr::app(Expr::app(list_cons.clone(), alpha.clone()), x),
                        ih,
                    );
                    let r = c.mk_lam(ih_id, BinderInfo::Default, list_alpha.clone(), r);
                    let r = c.mk_lam(tail_id, BinderInfo::Default, list_alpha.clone(), r);
                    let r = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), r);
                    c.finish_child(r)
                };

                let body = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(Expr::app(list_rec.clone(), alpha.clone()), motive),
                            ys,
                        ),
                        cons_case,
                    ),
                    xs,
                );
                let r = b.mk_lam(ys_id, BinderInfo::Default, list_alpha.clone(), body);
                let r = b.mk_lam(xs_id, BinderInfo::Default, list_alpha.clone(), r);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.append"),
                level_params: vec![u.clone()],
                type_: append_type,
                value: append_value,
                is_reducible: true,
            })?;

            // List.reverseAux : {α : Type u} → List α → List α → List α
            // Lean 4 (`Init/Data/List/Basic.lean`):
            //   reverseAux []      r = r
            //   reverseAux (a::l)  r = reverseAux l (a :: r)
            // The accumulator threads forward, so (like `foldl`) it cannot be a direct
            // `List.rec`: recurse to a function `List α → List α` and apply it to `r`.
            //   reverseAux l r =
            //     (@List.rec α (λ _ => List α → List α)
            //        (λ r => r)
            //        (λ a _ ih => λ r => ih (a :: r))
            //        l) r
            // Motive returns `List α → List α : Type u`, so `List.rec.{succ u, u}`.
            let reverse_aux_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let (l_id, _l) = b.fresh_local(list_alpha.clone());
                let (r_id, _r) = b.fresh_local(list_alpha.clone());
                let e = list_alpha.clone();
                let e = b.mk_pi(r_id, BinderInfo::Default, list_alpha.clone(), e);
                let e = b.mk_pi(l_id, BinderInfo::Default, list_alpha.clone(), e);
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            let reverse_aux_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                // `List α → List α : Type u`
                let list_to_list =
                    Expr::pi(BinderInfo::Default, list_alpha.clone(), list_alpha.clone());
                let (l_id, l) = b.fresh_local(list_alpha.clone());
                let (r_id, r) = b.fresh_local(list_alpha.clone());

                // motive: λ (_ : List α) => List α → List α
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_alpha.clone());
                    let m = c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_alpha.clone(),
                        list_to_list.clone(),
                    );
                    c.finish_child(m)
                };

                // nil case: λ (r : List α) => r
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (nr_id, nr) = c.fresh_local(list_alpha.clone());
                    let n = c.mk_lam(nr_id, BinderInfo::Default, list_alpha.clone(), nr);
                    c.finish_child(n)
                };

                // cons case: λ (a : α) (_ : List α) (ih : List α → List α) =>
                //              λ (r : List α) => ih (a :: r)
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, a) = c.fresh_local(alpha.clone());
                    let (tail_id, _tail) = c.fresh_local(list_alpha.clone());
                    let (ih_id, ih) = c.fresh_local(list_to_list.clone());
                    let (cr_id, cr) = c.fresh_local(list_alpha.clone());
                    // a :: r
                    let a_cons_r =
                        Expr::apps(list_cons.clone(), [alpha.clone(), a.clone(), cr.clone()]);
                    let inner = Expr::app(ih.clone(), a_cons_r);
                    let lam = c.mk_lam(cr_id, BinderInfo::Default, list_alpha.clone(), inner);
                    let lam = c.mk_lam(ih_id, BinderInfo::Default, list_to_list.clone(), lam);
                    let lam = c.mk_lam(tail_id, BinderInfo::Default, list_alpha.clone(), lam);
                    let lam = c.mk_lam(a_id, BinderInfo::Default, alpha.clone(), lam);
                    c.finish_child(lam)
                };

                let rec_app = Expr::apps(
                    list_rec.clone(),
                    [alpha.clone(), motive, nil_case, cons_case, l.clone()],
                );
                let body = Expr::app(rec_app, r.clone());
                let e = b.mk_lam(r_id, BinderInfo::Default, list_alpha.clone(), body);
                let e = b.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), e);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.reverseAux"),
                level_params: vec![u.clone()],
                type_: reverse_aux_type,
                value: reverse_aux_value,
                is_reducible: true,
            })?;

            // List.reverse : {α : Type u} → List α → List α
            let reverse_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let (xs_id, _xs) = b.fresh_local(list_alpha.clone());
                let r = list_alpha.clone();
                let r = b.mk_pi(xs_id, BinderInfo::Default, list_alpha.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            // Lean 4 (`Init/Data/List/Basic.lean`):
            //   def reverse (as : List α) : List α := reverseAux as []
            // Matching this EXACT definition (rather than the old direct-`List.rec`
            // append form) lets the imported `List.reverse_*` / `List.get_reverse`
            // lemmas — whose declared types Lean elaborated through
            // `reverse = reverseAux · []` — kernel-verify: the proof's inferred
            // `List.reverse l` and the lemma's `List.reverseAux l []` now δ-reduce to
            // the same head. Prelude DATA correction (`add_decl` re-checks the body;
            // axiom closure stays empty — built purely from `List.reverseAux`/`nil`).
            let reverse_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let (xs_id, xs) = b.fresh_local(list_alpha.clone());
                let reverse_aux_const = Expr::const_(
                    Name::from_string("List.reverseAux"),
                    vec![Level::param(u.clone())],
                );
                // @List.reverseAux α xs (List.nil α)
                let body = Expr::apps(
                    reverse_aux_const,
                    [
                        alpha.clone(),
                        xs.clone(),
                        Expr::app(list_nil.clone(), alpha.clone()),
                    ],
                );
                let r = b.mk_lam(xs_id, BinderInfo::Default, list_alpha.clone(), body);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.reverse"),
                level_params: vec![u.clone()],
                type_: reverse_type,
                value: reverse_value,
                is_reducible: true,
            })?;

            // List.map : {α : Type u} {β : Type v} → (α → β) → List α → List β
            let map_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (beta_id, beta) = b.fresh_local(type_v.clone());
                let f_ty = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, _a) = c.fresh_local(alpha.clone());
                    let r = beta.clone();
                    let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                    c.finish_child(r)
                };
                let (f_id, _f) = b.fresh_local(f_ty.clone());
                let (xs_id, _xs) = b.fresh_local(Expr::app(list_const.clone(), alpha.clone()));
                let r = Expr::app(list_const_b.clone(), beta.clone());
                let r = b.mk_pi(
                    xs_id,
                    BinderInfo::Default,
                    Expr::app(list_const.clone(), alpha.clone()),
                    r,
                );
                let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
                let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            // map f xs := List.rec α motive (nil β) cons_case xs
            let map_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (beta_id, beta) = b.fresh_local(type_v.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let list_beta = Expr::app(list_const_b.clone(), beta.clone());
                let f_ty = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, _a) = c.fresh_local(alpha.clone());
                    let r = beta.clone();
                    let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                    c.finish_child(r)
                };
                let (f_id, f) = b.fresh_local(f_ty.clone());
                let (xs_id, xs) = b.fresh_local(list_alpha.clone());

                // motive: λ (_ : List α) => List β
                let motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_alpha.clone());
                    let r = list_beta.clone();
                    let r = c.mk_lam(w_id, BinderInfo::Default, list_alpha.clone(), r);
                    c.finish_child(r)
                };

                let nil_case = Expr::app(list_nil_b.clone(), beta.clone());

                // cons case: λ (x : α) (_ : List α) (ih : List β) => cons β (f x) ih
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (x_id, x) = c.fresh_local(alpha.clone());
                    let (tail_id, _tail) = c.fresh_local(list_alpha.clone());
                    let (ih_id, ih) = c.fresh_local(list_beta.clone());
                    let fx = Expr::app(f.clone(), x);
                    let r = Expr::app(
                        Expr::app(Expr::app(list_cons_b.clone(), beta.clone()), fx),
                        ih,
                    );
                    let r = c.mk_lam(ih_id, BinderInfo::Default, list_beta.clone(), r);
                    let r = c.mk_lam(tail_id, BinderInfo::Default, list_alpha.clone(), r);
                    let r = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), r);
                    c.finish_child(r)
                };

                let body = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(Expr::app(list_rec_uv.clone(), alpha.clone()), motive),
                            nil_case,
                        ),
                        cons_case,
                    ),
                    xs,
                );
                let r = b.mk_lam(xs_id, BinderInfo::Default, list_alpha.clone(), body);
                let r = b.mk_lam(f_id, BinderInfo::Default, f_ty, r);
                let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), r);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.map"),
                level_params: vec![u.clone(), v.clone()],
                type_: map_type,
                value: map_value,
                is_reducible: true,
            })?;
        } // end import-mode List.append/reverseAux/reverse/map suppression

        // Ensure Option / Bool are available for get?/set/find?.
        self.init_option()?;
        self.init_bool()?;
        // Also pull the Option combinators (Option.map / .bind / .getD) into the
        // prelude. They are real `Option.rec` definitions registered by
        // `init_option_ops`, which is otherwise never reached from `with_prelude`
        // — so `o.map f` failed to resolve `Option.map`. No cycle:
        // `init_option_ops` depends only on `init_option`.
        self.init_option_ops()?;

        let u_lvl = Level::param(u.clone());
        let nat_const = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_const = Expr::const_(Name::from_string("Bool"), vec![]);
        // Option α : Type u, ctors / recursor at level u.
        let option_const = Expr::const_(Name::from_string("Option"), vec![u_lvl.clone()]);
        let option_none = Expr::const_(Name::from_string("Option.none"), vec![u_lvl.clone()]);
        let option_some = Expr::const_(Name::from_string("Option.some"), vec![u_lvl.clone()]);

        // ── List.get? {α : Type u} (l : List α) (i : Nat) : Option α ──────────
        //
        // Recurse on the list with motive `λ _ : List α => Nat → Option α`:
        //   nil  case : λ _ => Option.none α
        //   cons case : λ hd _ ih => λ n =>
        //       Nat.rec (motive := λ _ => Option α)
        //               (Option.some α hd)        -- n = 0
        //               (λ k _ => ih k)            -- n = succ k
        //               n
        //
        // `List.rec` motive is `Nat → Option α : Type u`, so the recursor's
        // major-premise universe is `Level::succ(u)`. The inner `Nat.rec`
        // motive `λ _ => Option α : Type u` likewise uses `Level::succ(u)`.
        let list_rec_get = Expr::const_(
            Name::from_string("List.rec"),
            vec![Level::succ(u_lvl.clone()), u_lvl.clone()],
        );
        let nat_rec_get = Expr::const_(
            Name::from_string("Nat.rec"),
            vec![Level::succ(u_lvl.clone())],
        );
        let get_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let option_alpha = Expr::app(option_const.clone(), alpha.clone());
            let (l_id, _l) = b.fresh_local(list_alpha.clone());
            let (i_id, _i) = b.fresh_local(nat_const.clone());
            let r = option_alpha.clone();
            let r = b.mk_pi(i_id, BinderInfo::Default, nat_const.clone(), r);
            let r = b.mk_pi(l_id, BinderInfo::Default, list_alpha.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        let get_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let option_alpha = Expr::app(option_const.clone(), alpha.clone());
            // nat_to_opt : Nat → Option α (the List.rec motive codomain).
            let nat_to_opt = Expr::pi(BinderInfo::Default, nat_const.clone(), option_alpha.clone());
            let (l_id, l) = b.fresh_local(list_alpha.clone());

            // List.rec motive: λ (_ : List α) => Nat → Option α
            let list_motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(list_alpha.clone());
                let r = c.mk_lam(
                    w_id,
                    BinderInfo::Default,
                    list_alpha.clone(),
                    nat_to_opt.clone(),
                );
                c.finish_child(r)
            };

            // nil case: λ (_ : Nat) => Option.none α
            let none_alpha = Expr::app(option_none.clone(), alpha.clone());
            let nil_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (n_id, _n) = c.fresh_local(nat_const.clone());
                let r = c.mk_lam(
                    n_id,
                    BinderInfo::Default,
                    nat_const.clone(),
                    none_alpha.clone(),
                );
                c.finish_child(r)
            };

            // cons case: λ (hd : α) (_ : List α) (_ih : Nat → Option α) =>
            //              λ (n : Nat) =>
            //                Nat.rec (λ _ => Option α)
            //                        (Option.some α hd)
            //                        (λ (k : Nat) (_ : Option α) => _ih k)
            //                        n
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hd_id, hd) = c.fresh_local(alpha.clone());
                let (tail_id, _tail) = c.fresh_local(list_alpha.clone());
                let (ih_id, ih) = c.fresh_local(nat_to_opt.clone());
                let (n_id, n) = c.fresh_local(nat_const.clone());

                // inner Nat.rec motive: λ (_ : Nat) => Option α
                let nat_motive = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (m_id, _m) = d.fresh_local(nat_const.clone());
                    let r = d.mk_lam(
                        m_id,
                        BinderInfo::Default,
                        nat_const.clone(),
                        option_alpha.clone(),
                    );
                    d.finish_child(r)
                };
                let some_hd = Expr::apps(option_some.clone(), [alpha.clone(), hd.clone()]);
                // succ case: λ (k : Nat) (_ : Option α) => ih k
                let succ_case = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (k_id, k) = d.fresh_local(nat_const.clone());
                    let (prev_id, _prev) = d.fresh_local(option_alpha.clone());
                    let r = Expr::app(ih.clone(), k);
                    let r = d.mk_lam(prev_id, BinderInfo::Default, option_alpha.clone(), r);
                    let r = d.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), r);
                    d.finish_child(r)
                };
                let inner = Expr::apps(nat_rec_get.clone(), [nat_motive, some_hd, succ_case, n]);
                let r = c.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), inner);
                let r = c.mk_lam(ih_id, BinderInfo::Default, nat_to_opt.clone(), r);
                let r = c.mk_lam(tail_id, BinderInfo::Default, list_alpha.clone(), r);
                let r = c.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };

            let body = Expr::apps(
                list_rec_get.clone(),
                [alpha.clone(), list_motive, nil_case, cons_case, l.clone()],
            );
            let r = b.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), body);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("List.get?"),
            level_params: vec![u.clone()],
            type_: get_type,
            value: get_value,
            is_reducible: true,
        })?;

        // ── List.set {α : Type u} (l : List α) (i : Nat) (v : α) : List α ─────
        //
        // Recurse on the list with motive `λ _ : List α => Nat → α → List α`:
        //   nil  case : λ _ _ => List.nil α
        //   cons case : λ hd tl ih => λ n v =>
        //       Nat.rec (motive := λ _ => List α)
        //               (List.cons α v tl)                 -- n = 0
        //               (λ k _ => List.cons α hd (ih k v))  -- n = succ k
        //               n
        //
        // IMPORT MODE: gated with the List.* recursion cluster (see the
        // SOUNDNESS block above List.append).
        if !self.suppress_lossy_structure_stubs {
            let list_rec_set = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(u_lvl.clone()), u_lvl.clone()],
            );
            let nat_rec_set = Expr::const_(
                Name::from_string("Nat.rec"),
                vec![Level::succ(u_lvl.clone())],
            );
            let set_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let (l_id, _l) = b.fresh_local(list_alpha.clone());
                let (i_id, _i) = b.fresh_local(nat_const.clone());
                let (v_id, _v) = b.fresh_local(alpha.clone());
                let r = list_alpha.clone();
                let r = b.mk_pi(v_id, BinderInfo::Default, alpha.clone(), r);
                let r = b.mk_pi(i_id, BinderInfo::Default, nat_const.clone(), r);
                let r = b.mk_pi(l_id, BinderInfo::Default, list_alpha.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            let set_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                // codomain of the List.rec motive: Nat → α → List α
                let nat_a_to_list = Expr::pi(
                    BinderInfo::Default,
                    nat_const.clone(),
                    Expr::pi(BinderInfo::Default, alpha.clone(), list_alpha.clone()),
                );
                let (l_id, l) = b.fresh_local(list_alpha.clone());

                // List.rec motive: λ (_ : List α) => Nat → α → List α
                let list_motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_alpha.clone());
                    let r = c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_alpha.clone(),
                        nat_a_to_list.clone(),
                    );
                    c.finish_child(r)
                };

                // nil case: λ (_ : Nat) (_ : α) => List.nil α
                let nil_alpha = Expr::app(list_nil.clone(), alpha.clone());
                let nil_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (n_id, _n) = c.fresh_local(nat_const.clone());
                    let (v_id, _v) = c.fresh_local(alpha.clone());
                    let r = c.mk_lam(v_id, BinderInfo::Default, alpha.clone(), nil_alpha.clone());
                    let r = c.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), r);
                    c.finish_child(r)
                };

                // cons case: λ (hd : α) (tl : List α) (ih : Nat → α → List α) =>
                //              λ (n : Nat) (v : α) =>
                //                Nat.rec (λ _ => List α)
                //                        (List.cons α v tl)
                //                        (λ (k : Nat) (_ : List α) => List.cons α hd (ih k v))
                //                        n
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hd_id, hd) = c.fresh_local(alpha.clone());
                    let (tl_id, tl) = c.fresh_local(list_alpha.clone());
                    let (ih_id, ih) = c.fresh_local(nat_a_to_list.clone());
                    let (n_id, n) = c.fresh_local(nat_const.clone());
                    let (v_id, v) = c.fresh_local(alpha.clone());

                    let nat_motive = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (m_id, _m) = d.fresh_local(nat_const.clone());
                        let r = d.mk_lam(
                            m_id,
                            BinderInfo::Default,
                            nat_const.clone(),
                            list_alpha.clone(),
                        );
                        d.finish_child(r)
                    };
                    // zero case: List.cons α v tl
                    let cons_v_tl =
                        Expr::apps(list_cons.clone(), [alpha.clone(), v.clone(), tl.clone()]);
                    // succ case: λ (k : Nat) (_ : List α) => List.cons α hd (ih k v)
                    let succ_case = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (k_id, k) = d.fresh_local(nat_const.clone());
                        let (prev_id, _prev) = d.fresh_local(list_alpha.clone());
                        let ih_k_v = Expr::apps(ih.clone(), [k, v.clone()]);
                        let r = Expr::apps(list_cons.clone(), [alpha.clone(), hd.clone(), ih_k_v]);
                        let r = d.mk_lam(prev_id, BinderInfo::Default, list_alpha.clone(), r);
                        let r = d.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), r);
                        d.finish_child(r)
                    };
                    let inner =
                        Expr::apps(nat_rec_set.clone(), [nat_motive, cons_v_tl, succ_case, n]);
                    let r = c.mk_lam(v_id, BinderInfo::Default, alpha.clone(), inner);
                    let r = c.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), r);
                    let r = c.mk_lam(ih_id, BinderInfo::Default, nat_a_to_list.clone(), r);
                    let r = c.mk_lam(tl_id, BinderInfo::Default, list_alpha.clone(), r);
                    let r = c.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), r);
                    c.finish_child(r)
                };

                let body = Expr::apps(
                    list_rec_set.clone(),
                    [alpha.clone(), list_motive, nil_case, cons_case, l.clone()],
                );
                let r = b.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), body);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.set"),
                level_params: vec![u.clone()],
                type_: set_type,
                value: set_value,
                is_reducible: true,
            })?;
        } // end import-mode List.set suppression

        // ── List.find? {α : Type u} (p : α → Bool) (l : List α) : Option α ────
        //
        // Recurse on the list with motive `λ _ : List α => Option α`:
        //   nil  case : Option.none α
        //   cons case : λ hd _ ih =>
        //       Bool.rec (motive := λ _ => Option α)
        //                ih                   -- p hd = false
        //                (Option.some α hd)   -- p hd = true
        //                (p hd)
        //
        // Bool.rec minor order is [false_case, true_case]. The motive lands in
        // `Option α : Type u`, so `Bool.rec.{succ u}` and `List.rec.{succ u, u}`.
        //
        // IMPORT MODE: `List.find?` and `List.filter` (which shares
        // `list_rec_find`/`bool_rec_find`) are gated with the List.*
        // recursion cluster (see the SOUNDNESS block above List.append).
        if !self.suppress_lossy_structure_stubs {
            let list_rec_find = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(u_lvl.clone()), u_lvl.clone()],
            );
            let bool_rec_find = Expr::const_(
                Name::from_string("Bool.rec"),
                vec![Level::succ(u_lvl.clone())],
            );
            let find_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let option_alpha = Expr::app(option_const.clone(), alpha.clone());
                let p_ty = Expr::pi(BinderInfo::Default, alpha.clone(), bool_const.clone());
                let (p_id, _p) = b.fresh_local(p_ty.clone());
                let (l_id, _l) = b.fresh_local(list_alpha.clone());
                let r = option_alpha.clone();
                let r = b.mk_pi(l_id, BinderInfo::Default, list_alpha.clone(), r);
                let r = b.mk_pi(p_id, BinderInfo::Default, p_ty.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            let find_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let option_alpha = Expr::app(option_const.clone(), alpha.clone());
                let p_ty = Expr::pi(BinderInfo::Default, alpha.clone(), bool_const.clone());
                let (p_id, p) = b.fresh_local(p_ty.clone());
                let (l_id, l) = b.fresh_local(list_alpha.clone());

                // List.rec motive: λ (_ : List α) => Option α
                let list_motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_alpha.clone());
                    let r = c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_alpha.clone(),
                        option_alpha.clone(),
                    );
                    c.finish_child(r)
                };

                let nil_case = Expr::app(option_none.clone(), alpha.clone());

                // cons case: λ (hd : α) (_ : List α) (ih : Option α) =>
                //              Bool.rec (λ _ => Option α) ih (Option.some α hd) (p hd)
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hd_id, hd) = c.fresh_local(alpha.clone());
                    let (tail_id, _tail) = c.fresh_local(list_alpha.clone());
                    let (ih_id, ih) = c.fresh_local(option_alpha.clone());

                    // inner Bool.rec motive: λ (_ : Bool) => Option α
                    let bool_motive = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (bm_id, _bm) = d.fresh_local(bool_const.clone());
                        let r = d.mk_lam(
                            bm_id,
                            BinderInfo::Default,
                            bool_const.clone(),
                            option_alpha.clone(),
                        );
                        d.finish_child(r)
                    };
                    let some_hd = Expr::apps(option_some.clone(), [alpha.clone(), hd.clone()]);
                    let p_hd = Expr::app(p.clone(), hd.clone());
                    // Bool.rec motive false_case true_case major
                    let inner = Expr::apps(
                        bool_rec_find.clone(),
                        [bool_motive, ih.clone(), some_hd, p_hd],
                    );
                    let r = c.mk_lam(ih_id, BinderInfo::Default, option_alpha.clone(), inner);
                    let r = c.mk_lam(tail_id, BinderInfo::Default, list_alpha.clone(), r);
                    let r = c.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), r);
                    c.finish_child(r)
                };

                let body = Expr::apps(
                    list_rec_find.clone(),
                    [alpha.clone(), list_motive, nil_case, cons_case, l.clone()],
                );
                let r = b.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), body);
                let r = b.mk_lam(p_id, BinderInfo::Default, p_ty.clone(), r);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.find?"),
                level_params: vec![u.clone()],
                type_: find_type,
                value: find_value,
                is_reducible: true,
            })?;

            // ── List.filter {α : Type u} (p : α → Bool) (l : List α) : List α ──────
            //
            // Keeps the elements satisfying `p`. Genuine, axiom-free `List.rec`
            // recursion (same shape as `List.find?` above, but the motive lands in
            // `List α` instead of `Option α`):
            //   motive    : λ _ : List α => List α
            //   nil  case : List.nil α
            //   cons case : λ hd _ ih =>
            //       Bool.rec (motive := λ _ => List α)
            //                ih                       -- p hd = false: drop hd
            //                (List.cons α hd ih)       -- p hd = true:  keep hd
            //                (p hd)
            //
            // `List.rec.{succ u, u}` / `Bool.rec.{succ u}` (the motive codomain
            // `List α : Type u` matches the `List.find?` setup, so we reuse
            // `list_rec_find` / `bool_rec_find`). Backs trust-ir
            // `Semantics/Aggregate.lean` `setUnion`/`setIntersection`
            // (`l.filter (fun ...)`), and the nested-aux `Value._List.filter`
            // resolves through the same constant via the toContainer machinery.
            let filter_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let p_ty = Expr::pi(BinderInfo::Default, alpha.clone(), bool_const.clone());
                let (p_id, _p) = b.fresh_local(p_ty.clone());
                let (l_id, _l) = b.fresh_local(list_alpha.clone());
                let r = list_alpha.clone();
                let r = b.mk_pi(l_id, BinderInfo::Default, list_alpha.clone(), r);
                let r = b.mk_pi(p_id, BinderInfo::Default, p_ty.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            let filter_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let p_ty = Expr::pi(BinderInfo::Default, alpha.clone(), bool_const.clone());
                let (p_id, p) = b.fresh_local(p_ty.clone());
                let (l_id, l) = b.fresh_local(list_alpha.clone());

                // List.rec motive: λ (_ : List α) => List α
                let list_motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_alpha.clone());
                    let r = c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_alpha.clone(),
                        list_alpha.clone(),
                    );
                    c.finish_child(r)
                };

                let nil_case = Expr::app(list_nil.clone(), alpha.clone());

                // cons case: λ (hd : α) (_ : List α) (ih : List α) =>
                //              Bool.rec (λ _ => List α) ih (List.cons α hd ih) (p hd)
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hd_id, hd) = c.fresh_local(alpha.clone());
                    let (tail_id, _tail) = c.fresh_local(list_alpha.clone());
                    let (ih_id, ih) = c.fresh_local(list_alpha.clone());

                    // inner Bool.rec motive: λ (_ : Bool) => List α
                    let bool_motive = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (bm_id, _bm) = d.fresh_local(bool_const.clone());
                        let r = d.mk_lam(
                            bm_id,
                            BinderInfo::Default,
                            bool_const.clone(),
                            list_alpha.clone(),
                        );
                        d.finish_child(r)
                    };
                    let keep =
                        Expr::apps(list_cons.clone(), [alpha.clone(), hd.clone(), ih.clone()]);
                    let p_hd = Expr::app(p.clone(), hd.clone());
                    // Bool.rec motive false_case true_case major
                    let inner =
                        Expr::apps(bool_rec_find.clone(), [bool_motive, ih.clone(), keep, p_hd]);
                    let r = c.mk_lam(ih_id, BinderInfo::Default, list_alpha.clone(), inner);
                    let r = c.mk_lam(tail_id, BinderInfo::Default, list_alpha.clone(), r);
                    let r = c.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), r);
                    c.finish_child(r)
                };

                let body = Expr::apps(
                    list_rec_find.clone(),
                    [alpha.clone(), list_motive, nil_case, cons_case, l.clone()],
                );
                let r = b.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), body);
                let r = b.mk_lam(p_id, BinderInfo::Default, p_ty.clone(), r);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.filter"),
                level_params: vec![u.clone()],
                type_: filter_type,
                value: filter_value,
                is_reducible: true,
            })?;

            // ── List.filterMap {α : Type u} {β : Type v}
            //        (f : α → Option β) (l : List α) : List β ────────────────────
            //
            // Maps then drops the `none`s. Genuine, axiom-free `List.rec` fold
            // over `List α` (Type u) into the motive `λ _ => List β` (Type v):
            //   nil  case : List.nil β
            //   cons case : λ hd _ ih =>
            //       Option.rec (motive := λ _ : Option β => List β)
            //                  ih                       -- f hd = none: drop
            //                  (λ b => List.cons β b ih) -- f hd = some b: keep b
            //                  (f hd)
            //
            // Same skeleton as `List.find?` above (List.rec + a nested dependent
            // rec on a per-element scrutinee) but the fold lands in a SECOND type
            // `List β : Type v`, so the outer eliminator is `List.rec.{succ v, u}`
            // (`list_rec_uv`) and the inner one `Option.rec.{succ v, v}`. `β`, its
            // `List`/`List.nil`/`List.cons` (`list_const_b`/`list_nil_b`/
            // `list_cons_b`) and the level `v` come from the `List.map` seed above.
            let option_v = Expr::const_(Name::from_string("Option"), vec![Level::param(v.clone())]);
            let option_rec_v = Expr::const_(
                Name::from_string("Option.rec"),
                vec![
                    Level::succ(Level::param(v.clone())),
                    Level::param(v.clone()),
                ],
            );
            let filtermap_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (beta_id, beta) = b.fresh_local(type_v.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let list_beta = Expr::app(list_const_b.clone(), beta.clone());
                let option_beta = Expr::app(option_v.clone(), beta.clone());
                let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), option_beta.clone());
                let (f_id, _f) = b.fresh_local(f_ty.clone());
                let (l_id, _l) = b.fresh_local(list_alpha.clone());
                let r = list_beta.clone();
                let r = b.mk_pi(l_id, BinderInfo::Default, list_alpha.clone(), r);
                let r = b.mk_pi(f_id, BinderInfo::Default, f_ty.clone(), r);
                let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            let filtermap_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (beta_id, beta) = b.fresh_local(type_v.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let list_beta = Expr::app(list_const_b.clone(), beta.clone());
                let option_beta = Expr::app(option_v.clone(), beta.clone());
                let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), option_beta.clone());
                let (f_id, f) = b.fresh_local(f_ty.clone());
                let (l_id, l) = b.fresh_local(list_alpha.clone());

                // outer List.rec motive: λ (_ : List α) => List β
                let list_motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_alpha.clone());
                    let r = c.mk_lam(
                        w_id,
                        BinderInfo::Default,
                        list_alpha.clone(),
                        list_beta.clone(),
                    );
                    c.finish_child(r)
                };

                let nil_case = Expr::app(list_nil_b.clone(), beta.clone());

                // cons case: λ (hd : α) (_ : List α) (ih : List β) =>
                //   Option.rec (λ _ : Option β => List β) ih
                //              (λ (b : β) => List.cons β b ih) (f hd)
                let cons_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (hd_id, hd) = c.fresh_local(alpha.clone());
                    let (tail_id, _tail) = c.fresh_local(list_alpha.clone());
                    let (ih_id, ih) = c.fresh_local(list_beta.clone());

                    // inner Option.rec motive: λ (_ : Option β) => List β
                    let opt_motive = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (om_id, _om) = d.fresh_local(option_beta.clone());
                        let r = d.mk_lam(
                            om_id,
                            BinderInfo::Default,
                            option_beta.clone(),
                            list_beta.clone(),
                        );
                        d.finish_child(r)
                    };
                    // some case: λ (bb : β) => List.cons β bb ih
                    let some_case = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (bb_id, bb) = d.fresh_local(beta.clone());
                        let consed =
                            Expr::apps(list_cons_b.clone(), [beta.clone(), bb.clone(), ih.clone()]);
                        let r = d.mk_lam(bb_id, BinderInfo::Default, beta.clone(), consed);
                        d.finish_child(r)
                    };
                    let f_hd = Expr::app(f.clone(), hd.clone());
                    // Option.rec β motive none_case some_case major
                    let inner = Expr::apps(
                        option_rec_v.clone(),
                        [beta.clone(), opt_motive, ih.clone(), some_case, f_hd],
                    );
                    let r = c.mk_lam(ih_id, BinderInfo::Default, list_beta.clone(), inner);
                    let r = c.mk_lam(tail_id, BinderInfo::Default, list_alpha.clone(), r);
                    let r = c.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), r);
                    c.finish_child(r)
                };

                let body = Expr::apps(
                    list_rec_uv.clone(),
                    [alpha.clone(), list_motive, nil_case, cons_case, l.clone()],
                );
                let r = b.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), body);
                let r = b.mk_lam(f_id, BinderInfo::Default, f_ty.clone(), r);
                let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), r);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.filterMap"),
                level_params: vec![u.clone(), v.clone()],
                type_: filtermap_type,
                value: filtermap_value,
                is_reducible: true,
            })?;
        } // end import-mode List.find?/List.filter suppression

        // ── List.zip {α β : Type u} (xs : List α) (ys : List β)
        //          : List (α × β) ──────────────────────────────────────────────
        //
        // Truncating pairwise zip. Genuine, axiom-free double `List.rec`: recurse
        // on `xs` producing a function `List β → List (α × β)`, then recurse on
        // `ys` to peel its head/tail:
        //   outer motive : λ _ : List α => List β → List (α × β)
        //   nil  case    : λ _ : List β => List.nil (α × β)
        //   cons case    : λ (x : α) (_ : List α) (ih : List β → List (α × β)) =>
        //                    λ (ys : List β) =>
        //                      List.rec (motive := λ _ : List β => List (α × β))
        //                        (List.nil (α × β))                       -- ys = []
        //                        (λ (y : β) (ytl : List β) (_ih2) =>
        //                           List.cons (α × β) (Prod.mk α β x y) (ih ytl))
        //                        ys
        // The inner cons case uses `ytl` (the real tail of `ys`) with the OUTER
        // ih, not the inner `_ih2`, so the recursion is well-founded on both
        // arguments. `Prod`/`Prod.mk` at `[u, u]`; the result `List (α × β)`
        // and the function `List β → List (α × β)` both live in `Type u`, so the
        // recursors are `List.rec.{succ u, u}`. Backs trust-ir
        // `Semantics/Eval.lean` `bindBlockParams`/`bindResultDests`
        // (`(params.zip args).foldl ...`).
        // WS-LEVEL: this hand-rolled `List.zip` is SINGLE-universe
        // (`{α β : Type u}`, `level_params = [u]`), but Lean 4 core's genuine
        // `List.zip.{u, v}` is TWO-universe (`{α : Type u} {β : Type v}`). On
        // `.olean` import the loader dedups by name and this stub — registered by
        // the prelude first — SHADOWS the real two-universe definition, so every
        // Mathlib proof that references `@List.zip.{u, v}` (2 level args) hits
        // `LevelCountMismatch { expected: 1, got: 2 }` and fails to kernel-verify
        // (56 such rows in the mathverse-full-v2 corpus). Same lossy-stub
        // shadowing class as WS17/18/19: in import-verification mode suppress the
        // stub so the genuine `List.zip` registers through the checked import path
        // with its full two-universe signature. SOUNDNESS: suppression only ever
        // lets the genuine, fully kernel-checked Lean `List.zip` import in the
        // stub's place; nothing here touches `is_def_eq`/`whnf` or relaxes
        // acceptance. Nothing else in the prelude references `List.zip`, so no
        // dangling reference remains. The proof-execution lane (stub NOT
        // suppressed) keeps the single-universe `List.zip` exactly as before.
        if !self.suppress_lossy_structure_stubs {
            let prod_const = Expr::const_(
                Name::from_string("Prod"),
                vec![u_lvl.clone(), u_lvl.clone()],
            );
            let prod_mk = Expr::const_(
                Name::from_string("Prod.mk"),
                vec![u_lvl.clone(), u_lvl.clone()],
            );
            let list_rec_zip = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(u_lvl.clone()), u_lvl.clone()],
            );
            let zip_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (beta_id, beta) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let list_beta = Expr::app(list_const.clone(), beta.clone());
                let prod_ab = Expr::apps(prod_const.clone(), [alpha.clone(), beta.clone()]);
                let list_prod = Expr::app(list_const.clone(), prod_ab);
                let (xs_id, _xs) = b.fresh_local(list_alpha.clone());
                let (ys_id, _ys) = b.fresh_local(list_beta.clone());
                let r = list_prod;
                let r = b.mk_pi(ys_id, BinderInfo::Default, list_beta.clone(), r);
                let r = b.mk_pi(xs_id, BinderInfo::Default, list_alpha.clone(), r);
                let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            let zip_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (beta_id, beta) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let list_beta = Expr::app(list_const.clone(), beta.clone());
                let prod_ab = Expr::apps(prod_const.clone(), [alpha.clone(), beta.clone()]);
                let list_prod = Expr::app(list_const.clone(), prod_ab.clone());
                // `List β → List (α × β)` — the outer-recursion motive codomain.
                let fn_ty = Expr::pi(BinderInfo::Default, list_beta.clone(), list_prod.clone());
                let nil_prod = Expr::app(list_nil.clone(), prod_ab.clone());

                let (xs_id, xs) = b.fresh_local(list_alpha.clone());
                let (ys_id, ys) = b.fresh_local(list_beta.clone());

                // outer List.rec motive: λ (_ : List α) => List β → List (α × β)
                let outer_motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (w_id, _w) = c.fresh_local(list_alpha.clone());
                    let r = c.mk_lam(w_id, BinderInfo::Default, list_alpha.clone(), fn_ty.clone());
                    c.finish_child(r)
                };

                // outer nil case: λ (_ : List β) => List.nil (α × β)
                let outer_nil = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (ig_id, _ig) = c.fresh_local(list_beta.clone());
                    let r = c.mk_lam(
                        ig_id,
                        BinderInfo::Default,
                        list_beta.clone(),
                        nil_prod.clone(),
                    );
                    c.finish_child(r)
                };

                // outer cons case:
                //   λ (x : α) (_ : List α) (ih : List β → List (α × β)) =>
                //     λ (ys2 : List β) => List.rec ... ys2
                let outer_cons = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (x_id, x) = c.fresh_local(alpha.clone());
                    let (xtail_id, _xtail) = c.fresh_local(list_alpha.clone());
                    let (ih_id, ih) = c.fresh_local(fn_ty.clone());
                    let (ys2_id, ys2) = c.fresh_local(list_beta.clone());

                    // inner List.rec motive: λ (_ : List β) => List (α × β)
                    let inner_motive = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (w_id, _w) = d.fresh_local(list_beta.clone());
                        let r = d.mk_lam(
                            w_id,
                            BinderInfo::Default,
                            list_beta.clone(),
                            list_prod.clone(),
                        );
                        d.finish_child(r)
                    };

                    // inner cons case: λ (y : β) (ytl : List β) (_ih2 : List (α×β)) =>
                    //   List.cons (α×β) (Prod.mk α β x y) (ih ytl)
                    let inner_cons = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (y_id, y) = d.fresh_local(beta.clone());
                        let (ytl_id, ytl) = d.fresh_local(list_beta.clone());
                        let (ih2_id, _ih2) = d.fresh_local(list_prod.clone());
                        let pair = Expr::apps(
                            prod_mk.clone(),
                            [alpha.clone(), beta.clone(), x.clone(), y.clone()],
                        );
                        let rest = Expr::app(ih.clone(), ytl.clone());
                        let consed = Expr::apps(list_cons.clone(), [prod_ab.clone(), pair, rest]);
                        let r = d.mk_lam(ih2_id, BinderInfo::Default, list_prod.clone(), consed);
                        let r = d.mk_lam(ytl_id, BinderInfo::Default, list_beta.clone(), r);
                        let r = d.mk_lam(y_id, BinderInfo::Default, beta.clone(), r);
                        d.finish_child(r)
                    };

                    let inner = Expr::apps(
                        list_rec_zip.clone(),
                        [
                            beta.clone(),
                            inner_motive,
                            nil_prod.clone(),
                            inner_cons,
                            ys2.clone(),
                        ],
                    );
                    let r = c.mk_lam(ys2_id, BinderInfo::Default, list_beta.clone(), inner);
                    let r = c.mk_lam(ih_id, BinderInfo::Default, fn_ty.clone(), r);
                    let r = c.mk_lam(xtail_id, BinderInfo::Default, list_alpha.clone(), r);
                    let r = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), r);
                    c.finish_child(r)
                };

                // (List.rec α outer_motive outer_nil outer_cons xs) ys
                let recurse = Expr::apps(
                    list_rec_zip.clone(),
                    [
                        alpha.clone(),
                        outer_motive,
                        outer_nil,
                        outer_cons,
                        xs.clone(),
                    ],
                );
                let body = Expr::app(recurse, ys.clone());
                let r = b.mk_lam(ys_id, BinderInfo::Default, list_beta.clone(), body);
                let r = b.mk_lam(xs_id, BinderInfo::Default, list_alpha.clone(), r);
                let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_u.clone(), r);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.zip"),
                level_params: vec![u.clone()],
                type_: zip_type,
                value: zip_value,
                is_reducible: true,
            })?;
        } // end import-mode `List.zip` stub suppression

        // ── List.replicate {α : Type u} (n : Nat) (a : α) : List α ───────────
        //
        // Builds the list `[a, a, …, a]` of length `n`. Recurse on the Nat with
        // motive `λ _ : Nat => List α`:
        //   zero case : List.nil α
        //   succ case : λ (k : Nat) (ih : List α) => List.cons α a ih
        //
        // Without `List.replicate` registered, `List.replicate 8 0` (trust-ir
        // `Semantics/Memory.lean` `encodeValue`'s axiomatized Float/nullPtr
        // placeholders, `some (List.replicate 8 0)`) was parsed as a projection
        // `.replicate` on the receiver `List`, whose type is the Pi
        // `Type u → Type u`; the dot resolver / `get_type_name` cannot extract a
        // namespace from a Pi, failing with "cannot extract type name from
        // Pi(...)". Registering the real `List.rec`/`Nat.rec` definition makes
        // `List.replicate` resolve as an ordinary const. Axiom-free: built
        // entirely from `Nat.rec` + `List.nil`/`List.cons` (Definition).
        //
        // IMPORT MODE: gated with the List.* recursion cluster (see the
        // SOUNDNESS block above List.append).
        if !self.suppress_lossy_structure_stubs {
            let nat_rec_repl = Expr::const_(
                Name::from_string("Nat.rec"),
                vec![Level::succ(u_lvl.clone())],
            );
            let replicate_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let (n_id, _n) = b.fresh_local(nat_const.clone());
                let (a_id, _a) = b.fresh_local(alpha.clone());
                let r = list_alpha.clone();
                let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                let r = b.mk_pi(n_id, BinderInfo::Default, nat_const.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            let replicate_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let list_alpha = Expr::app(list_const.clone(), alpha.clone());
                let (n_id, n) = b.fresh_local(nat_const.clone());
                let (a_id, a) = b.fresh_local(alpha.clone());

                // Nat.rec motive: λ (_ : Nat) => List α
                let nat_motive = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (m_id, _m) = c.fresh_local(nat_const.clone());
                    let r = c.mk_lam(
                        m_id,
                        BinderInfo::Default,
                        nat_const.clone(),
                        list_alpha.clone(),
                    );
                    c.finish_child(r)
                };
                // zero case: List.nil α
                let zero_case = Expr::app(list_nil.clone(), alpha.clone());
                // succ case: λ (k : Nat) (ih : List α) => List.cons α a ih
                let succ_case = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (k_id, _k) = c.fresh_local(nat_const.clone());
                    let (ih_id, ih) = c.fresh_local(list_alpha.clone());
                    let r = Expr::apps(list_cons.clone(), [alpha.clone(), a.clone(), ih]);
                    let r = c.mk_lam(ih_id, BinderInfo::Default, list_alpha.clone(), r);
                    let r = c.mk_lam(k_id, BinderInfo::Default, nat_const.clone(), r);
                    c.finish_child(r)
                };
                let body = Expr::apps(
                    nat_rec_repl.clone(),
                    [nat_motive, zero_case, succ_case, n.clone()],
                );
                let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
                let r = b.mk_lam(n_id, BinderInfo::Default, nat_const.clone(), r);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("List.replicate"),
                level_params: vec![u.clone()],
                type_: replicate_type,
                value: replicate_value,
                is_reducible: true,
            })?;
        } // end import-mode List.replicate suppression

        // ── List.append_nil : {α : Type u} → (xs : List α) → xs ++ [] = xs ───
        //
        // The ι-reducing direction `[] ++ xs = xs` closes by `rfl` because
        // `List.append` recurses on its FIRST argument. The symbolic-tail
        // direction `xs ++ [] = xs` is STUCK on the recursion target and needs
        // a genuine induction. We discharge it with `List.rec`, exactly the
        // template used by `List.Perm.refl` (data_types_list_perm.rs):
        //
        //   motive    := λ (l : List α) => @List.append α l (@List.nil α) = l
        //   nil case  := @Eq.refl (List α) (@List.nil α)
        //               (since `[] ++ [] ↦ []` by ι, the motive at `[]` is
        //                `[] = []`, closed by refl)
        //   cons case := λ (x : α) (xs : List α)
        //                  (ih : @List.append α xs (@List.nil α) = xs) =>
        //                    @congrArg (List α) (List α)
        //                      (@List.append α xs (@List.nil α)) xs
        //                      (λ l => @List.cons α x l) ih
        //               (this has type `(x :: (xs ++ [])) = (x :: xs)`; since
        //                `(x :: xs) ++ [] ↦ x :: (xs ++ [])` by ι, it is def-eq
        //                to the motive at `x :: xs`, which the kernel accepts as
        //                `List.append` is reducible)
        //
        // Transitive axiom closure: `List.rec` + `congrArg` + `Eq.refl`, all
        // FOUNDATIONAL — a genuine 0-axiom proof. `Eq`/`Eq.refl`/`congrArg`
        // come from `init_eq` (idempotent).
        self.init_eq()?;
        // IMPORT MODE: `List.append_nil` states a goal over the gated
        // `List.append` seed — gated with the cluster (see the SOUNDNESS
        // block above List.append); the genuine olean theorem imports.
        if !self.suppress_lossy_structure_stubs {
            let u_lvl = Level::param(u.clone());
            let list_alpha_of = |a: &Expr| Expr::app(list_const.clone(), a.clone());
            let nil_of = |a: &Expr| Expr::app(list_nil.clone(), a.clone());
            // @List.append α xs []
            let list_append_const =
                Expr::const_(Name::from_string("List.append"), vec![u_lvl.clone()]);
            let append_nil_of = |a: &Expr, xs: Expr| {
                Expr::apps(list_append_const.clone(), [a.clone(), xs, nil_of(a)])
            };
            // `Eq` and `Eq.refl` for the carrier `List α : Type u = Sort (u+1)`.
            let eq_const = Expr::const_(Name::from_string("Eq"), vec![Level::succ(u_lvl.clone())]);
            let eq_refl_const = Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(u_lvl.clone())],
            );
            // `@Eq (List α) a b`
            let eq_of = |a: &Expr, lhs: Expr, rhs: Expr| {
                Expr::apps(eq_const.clone(), [list_alpha_of(a), lhs, rhs])
            };
            // congrArg.{u+1, u+1} : {α β : Sort (u+1)} {a₁ a₂ : α}
            //   (f : α → β) → a₁ = a₂ → f a₁ = f a₂   (here α = β = List α').
            let congr_arg_const = Expr::const_(
                Name::from_string("congrArg"),
                vec![Level::succ(u_lvl.clone()), Level::succ(u_lvl.clone())],
            );

            // Type: {α : Type u} → (xs : List α) → @List.append α xs [] = xs
            let append_nil_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (xs_id, xs) = b.fresh_local(list_alpha_of(&alpha));
                let concl = eq_of(&alpha, append_nil_of(&alpha, xs.clone()), xs.clone());
                let e = b.mk_pi(xs_id, BinderInfo::Default, list_alpha_of(&alpha), concl);
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };

            let append_nil_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());

                // motive : λ (l : List α) => @List.append α l [] = l   (→ Prop)
                let (m_id, m_l) = b.fresh_local(list_alpha_of(&alpha));
                let motive = b.mk_lam(
                    m_id,
                    BinderInfo::Default,
                    list_alpha_of(&alpha),
                    eq_of(&alpha, append_nil_of(&alpha, m_l.clone()), m_l.clone()),
                );

                // nil case : @Eq.refl (List α) (@List.nil α)
                let nil_case = Expr::apps(
                    eq_refl_const.clone(),
                    [list_alpha_of(&alpha), nil_of(&alpha)],
                );

                // cons case : λ (x : α) (xs : List α)
                //               (ih : @List.append α xs [] = xs) =>
                //   @congrArg (List α) (List α)
                //     (@List.append α xs []) xs (λ l => @List.cons α x l) ih
                let (x_id, x) = b.fresh_local(alpha.clone());
                let (xs_id, xs) = b.fresh_local(list_alpha_of(&alpha));
                let ih_ty = eq_of(&alpha, append_nil_of(&alpha, xs.clone()), xs.clone());
                let (ih_id, ih) = b.fresh_local(ih_ty.clone());
                // f := λ (l : List α) => @List.cons α x l
                let cons_fn = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (l_id, l) = c.fresh_local(list_alpha_of(&alpha));
                    let body = Expr::apps(list_cons.clone(), [alpha.clone(), x.clone(), l]);
                    let r = c.mk_lam(l_id, BinderInfo::Default, list_alpha_of(&alpha), body);
                    c.finish_child(r)
                };
                let cons_body = Expr::apps(
                    congr_arg_const.clone(),
                    [
                        list_alpha_of(&alpha),
                        list_alpha_of(&alpha),
                        append_nil_of(&alpha, xs.clone()),
                        xs.clone(),
                        cons_fn,
                        ih.clone(),
                    ],
                );
                let cons_case = b.mk_lam(ih_id, BinderInfo::Default, ih_ty, cons_body);
                let cons_case =
                    b.mk_lam(xs_id, BinderInfo::Default, list_alpha_of(&alpha), cons_case);
                let cons_case = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), cons_case);

                // List.rec.{0, u} α motive nil_case cons_case l
                let list_rec_prop = Expr::const_(
                    Name::from_string("List.rec"),
                    vec![Level::zero(), u_lvl.clone()],
                );
                let (l_id, l) = b.fresh_local(list_alpha_of(&alpha));
                let body = Expr::apps(
                    list_rec_prop,
                    [alpha.clone(), motive, nil_case, cons_case, l.clone()],
                );
                let e = b.mk_lam(l_id, BinderInfo::Default, list_alpha_of(&alpha), body);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                b.finish(e)
            };

            self.add_decl(Declaration::Theorem {
                name: Name::from_string("List.append_nil"),
                level_params: vec![u.clone()],
                type_: append_nil_type,
                value: append_nil_value,
            })?;
        }

        // ── List.length simp lemmas: length_nil / length_cons / length_append ──
        //
        // These three rules let `simp` evaluate `List.length` over the three
        // shapes that appear in `(xs ++ ys).length = xs.length + ys.length`.
        // All proofs are genuine — `List.length_append` inducts via `List.rec`;
        // the two base lemmas close by `rfl` (ι-reduction of `List.length`).
        // `List.length` (data_types_collections.rs) recurses on the list:
        //   `nil.length ↦ Nat.zero` and `(x::xs).length ↦ Nat.succ xs.length`.
        //
        // `Nat.zero_add` and `Nat.succ_add` are needed because `Nat.add`
        // recurses on its SECOND argument, so `0 + n` and `succ a + b` are
        // STUCK and not def-eq to `n` / `succ (a + b)`. Both are constructive
        // (#3604) theorems with empty domain-axiom closure, registered by the
        // idempotent `init_nat_arith_lemmas` (called defensively here since
        // `init_list_ops`'s ordering does not guarantee they ran yet).
        //
        // Transitive axiom closure for all three: `List.rec`/`Nat.rec`
        // (recursors), `congrArg`, `Eq.refl`/`Eq.symm`/`Eq.trans` (Eq
        // built-ins), `Nat.zero_add`/`Nat.succ_add` (constructive #3604) — all
        // FOUNDATIONAL, a genuine 0-domain-axiom proof. `length_nil` and
        // `length_cons` close by `Eq.refl` alone.
        self.init_nat_arith_lemmas()?;
        // IMPORT MODE: the three `List.length_*` lemmas state goals over the
        // gated `List.length`/`List.append` seeds — gated with the cluster
        // (see the SOUNDNESS block above List.append); the genuine olean
        // theorems import.
        if !self.suppress_lossy_structure_stubs {
            let u_lvl = Level::param(u.clone());
            let list_alpha_of = |a: &Expr| Expr::app(list_const.clone(), a.clone());
            let nil_of = |a: &Expr| Expr::app(list_nil.clone(), a.clone());
            // @List.length.{u} α l : Nat   (recurses on the list)
            let list_length_const =
                Expr::const_(Name::from_string("List.length"), vec![u_lvl.clone()]);
            let length_of =
                |a: &Expr, l: Expr| Expr::apps(list_length_const.clone(), [a.clone(), l]);
            // @List.append.{u} α xs ys
            let list_append_const =
                Expr::const_(Name::from_string("List.append"), vec![u_lvl.clone()]);
            let append_of = |a: &Expr, xs: Expr, ys: Expr| {
                Expr::apps(list_append_const.clone(), [a.clone(), xs, ys])
            };
            // Nat building blocks.
            let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
            let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
            let nat_add = Expr::const_(Name::from_string("Nat.add"), vec![]);
            let succ_of = |x: Expr| Expr::app(nat_succ.clone(), x);
            let add_of = |x: Expr, y: Expr| Expr::apps(nat_add.clone(), [x, y]);
            // `Eq` / `Eq.refl` / `Eq.symm` / `Eq.trans` for the carrier
            // `Nat : Type 0 = Sort 1`, so the universe argument is `1`.
            let nat_lvl = Level::succ(Level::zero());
            let eq_nat = Expr::const_(Name::from_string("Eq"), vec![nat_lvl.clone()]);
            let eq_nat_of =
                |lhs: Expr, rhs: Expr| Expr::apps(eq_nat.clone(), [nat_const.clone(), lhs, rhs]);
            let eq_refl_nat = Expr::const_(Name::from_string("Eq.refl"), vec![nat_lvl.clone()]);
            let eq_refl_nat_of = |x: Expr| Expr::apps(eq_refl_nat.clone(), [nat_const.clone(), x]);
            let eq_symm_nat = Expr::const_(Name::from_string("Eq.symm"), vec![nat_lvl.clone()]);
            let eq_trans_nat = Expr::const_(Name::from_string("Eq.trans"), vec![nat_lvl.clone()]);
            // congrArg.{1,1} : {α β : Sort 1} {a₁ a₂ : α} (f : α → β)
            //   → a₁ = a₂ → f a₁ = f a₂   (here α = β = Nat).
            let congr_arg_nat = Expr::const_(
                Name::from_string("congrArg"),
                vec![nat_lvl.clone(), nat_lvl.clone()],
            );
            let nat_zero_add = Expr::const_(Name::from_string("Nat.zero_add"), vec![]);
            let nat_succ_add = Expr::const_(Name::from_string("Nat.succ_add"), vec![]);

            // ── List.length_nil : {α : Type u} → (@List.nil α).length = 0 ──────
            // Motive at `nil` ι-reduces to `0`, so the goal is `0 = 0`: rfl.
            {
                let length_nil_type = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let concl = eq_nat_of(length_of(&alpha, nil_of(&alpha)), nat_zero.clone());
                    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), concl);
                    b.finish(e)
                };
                let length_nil_value = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, _alpha) = b.fresh_local(type_u.clone());
                    let body = eq_refl_nat_of(nat_zero.clone());
                    let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
                    b.finish(e)
                };
                self.add_decl(Declaration::Theorem {
                    name: Name::from_string("List.length_nil"),
                    level_params: vec![u.clone()],
                    type_: length_nil_type,
                    value: length_nil_value,
                })?;
            }

            // ── List.length_cons : {α} → (x : α) → (xs : List α) →
            //      (@List.cons α x xs).length = (xs.length).succ ────────────────
            // Motive at `cons x xs` ι-reduces to `Nat.succ xs.length`: rfl.
            {
                let length_cons_type = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let (x_id, x) = b.fresh_local(alpha.clone());
                    let (xs_id, xs) = b.fresh_local(list_alpha_of(&alpha));
                    let cons_xs =
                        Expr::apps(list_cons.clone(), [alpha.clone(), x.clone(), xs.clone()]);
                    let concl = eq_nat_of(
                        length_of(&alpha, cons_xs),
                        succ_of(length_of(&alpha, xs.clone())),
                    );
                    let e = b.mk_pi(xs_id, BinderInfo::Default, list_alpha_of(&alpha), concl);
                    let e = b.mk_pi(x_id, BinderInfo::Default, alpha.clone(), e);
                    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                let length_cons_value = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let (x_id, _x) = b.fresh_local(alpha.clone());
                    let (xs_id, xs) = b.fresh_local(list_alpha_of(&alpha));
                    let body = eq_refl_nat_of(succ_of(length_of(&alpha, xs.clone())));
                    let e = b.mk_lam(xs_id, BinderInfo::Default, list_alpha_of(&alpha), body);
                    let e = b.mk_lam(x_id, BinderInfo::Default, alpha.clone(), e);
                    let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };
                self.add_decl(Declaration::Theorem {
                    name: Name::from_string("List.length_cons"),
                    level_params: vec![u.clone()],
                    type_: length_cons_type,
                    value: length_cons_value,
                })?;
            }

            // ── List.length_append : {α} → (xs ys : List α) →
            //      (xs ++ ys).length = xs.length + ys.length ────────────────────
            //
            // Induct on `xs` via `List.rec.{0, u}` (motive lands in Prop):
            //   motive l := length (l ++ ys) = length l + length ys
            //   nil  : length (nil ++ ys) = length nil + length ys
            //          ι-reduces (append/length nil cases) to
            //          `length ys = 0 + length ys`. `0 + length ys` is STUCK,
            //          so close with `Eq.symm (Nat.zero_add (length ys))`.
            //   cons : λ x cxs (ih : length (cxs ++ ys) = length cxs + length ys)
            //          motive at `x :: cxs` ι-reduces to
            //          `succ (length (cxs ++ ys)) = succ (length cxs) + length ys`.
            //          C1 := congrArg succ ih
            //                : succ (length (cxs++ys)) = succ (length cxs + length ys)
            //          C2 := Eq.symm (Nat.succ_add (length cxs) (length ys))
            //                : succ (length cxs) + length ys = succ (length cxs + length ys)
            //                (symm of succ_add's `succ a + b = succ (a+b)`)
            //          proof := Eq.trans C1 (Eq.symm C2-as-needed) — assembled as
            //          Eq.trans over the three points below.
            {
                let length_append_type = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let (xs_id, xs) = b.fresh_local(list_alpha_of(&alpha));
                    let (ys_id, ys) = b.fresh_local(list_alpha_of(&alpha));
                    let concl = eq_nat_of(
                        length_of(&alpha, append_of(&alpha, xs.clone(), ys.clone())),
                        add_of(length_of(&alpha, xs.clone()), length_of(&alpha, ys.clone())),
                    );
                    let e = b.mk_pi(ys_id, BinderInfo::Default, list_alpha_of(&alpha), concl);
                    let e = b.mk_pi(xs_id, BinderInfo::Default, list_alpha_of(&alpha), e);
                    let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };

                let length_append_value = {
                    let mut b = EnvDeclBuilder::new();
                    let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                    let (ys_id, ys) = b.fresh_local(list_alpha_of(&alpha));

                    // motive : λ (l : List α) =>
                    //   length (l ++ ys) = length l + length ys   (→ Prop)
                    let motive = {
                        let mut c = EnvDeclBuilder::child_of(&b);
                        let (l_id, l) = c.fresh_local(list_alpha_of(&alpha));
                        let body = eq_nat_of(
                            length_of(&alpha, append_of(&alpha, l.clone(), ys.clone())),
                            add_of(length_of(&alpha, l.clone()), length_of(&alpha, ys.clone())),
                        );
                        let r = c.mk_lam(l_id, BinderInfo::Default, list_alpha_of(&alpha), body);
                        c.finish_child(r)
                    };

                    // nil case : Eq.symm (Nat.zero_add (length ys))
                    //   Nat.zero_add (length ys) : 0 + length ys = length ys
                    //   Eq.symm                   : length ys = 0 + length ys
                    let len_ys = length_of(&alpha, ys.clone());
                    let nil_case = {
                        let za = Expr::app(nat_zero_add.clone(), len_ys.clone());
                        Expr::apps(
                            eq_symm_nat.clone(),
                            [
                                nat_const.clone(),
                                add_of(nat_zero.clone(), len_ys.clone()),
                                len_ys.clone(),
                                za,
                            ],
                        )
                    };

                    // cons case : λ (x : α) (cxs : List α)
                    //   (ih : length (cxs ++ ys) = length cxs + length ys) => …
                    let cons_case = {
                        let mut c = EnvDeclBuilder::child_of(&b);
                        let (x_id, _x) = c.fresh_local(alpha.clone());
                        let (cxs_id, cxs) = c.fresh_local(list_alpha_of(&alpha));
                        let len_cxs_ys =
                            length_of(&alpha, append_of(&alpha, cxs.clone(), ys.clone()));
                        let len_cxs = length_of(&alpha, cxs.clone());
                        let rhs_inner = add_of(len_cxs.clone(), len_ys.clone());
                        let ih_ty = eq_nat_of(len_cxs_ys.clone(), rhs_inner.clone());
                        let (ih_id, ih) = c.fresh_local(ih_ty.clone());

                        // C1 := congrArg.{1,1} Nat Nat
                        //         len_cxs_ys rhs_inner Nat.succ ih
                        //   : succ len_cxs_ys = succ rhs_inner
                        let c1 = Expr::apps(
                            congr_arg_nat.clone(),
                            [
                                nat_const.clone(),
                                nat_const.clone(),
                                len_cxs_ys.clone(),
                                rhs_inner.clone(),
                                nat_succ.clone(),
                                ih.clone(),
                            ],
                        );

                        // C2 := Eq.symm (Nat.succ_add len_cxs len_ys)
                        //   Nat.succ_add a b : succ a + b = succ (a + b)
                        //   here a = len_cxs, b = len_ys, so
                        //     succ_add : (succ len_cxs) + len_ys = succ (len_cxs + len_ys)
                        //   Eq.symm  : succ (len_cxs + len_ys) = (succ len_cxs) + len_ys
                        let succ_add_app =
                            Expr::apps(nat_succ_add.clone(), [len_cxs.clone(), len_ys.clone()]);
                        let succ_lhs = add_of(succ_of(len_cxs.clone()), len_ys.clone());
                        let succ_rhs = succ_of(rhs_inner.clone());
                        let c2 = Expr::apps(
                            eq_symm_nat.clone(),
                            [
                                nat_const.clone(),
                                succ_lhs.clone(),
                                succ_rhs.clone(),
                                succ_add_app,
                            ],
                        );

                        // proof := Eq.trans.{1} Nat
                        //   (succ len_cxs_ys) (succ rhs_inner) (succ_lhs)
                        //   C1 C2
                        //   : succ len_cxs_ys = (succ len_cxs) + len_ys
                        //   which is the motive at `cons x cxs`.
                        let body = Expr::apps(
                            eq_trans_nat.clone(),
                            [
                                nat_const.clone(),
                                succ_of(len_cxs_ys.clone()),
                                succ_rhs.clone(),
                                succ_lhs.clone(),
                                c1,
                                c2,
                            ],
                        );
                        let r = c.mk_lam(ih_id, BinderInfo::Default, ih_ty, body);
                        let r = c.mk_lam(cxs_id, BinderInfo::Default, list_alpha_of(&alpha), r);
                        let r = c.mk_lam(x_id, BinderInfo::Default, alpha.clone(), r);
                        c.finish_child(r)
                    };

                    // List.rec.{0, u} α motive nil_case cons_case xs
                    let list_rec_prop = Expr::const_(
                        Name::from_string("List.rec"),
                        vec![Level::zero(), u_lvl.clone()],
                    );
                    let (xs_id, xs) = b.fresh_local(list_alpha_of(&alpha));
                    let body = Expr::apps(
                        list_rec_prop,
                        [alpha.clone(), motive, nil_case, cons_case, xs.clone()],
                    );
                    // Close `ys` (inner) then `xs` (outer) so the value's binder
                    // order is `{α} → (xs) → (ys) → …`, matching the declared
                    // type. (`ys` is captured free inside both the motive and
                    // the recursion target `xs`, so it must wrap the inside.)
                    let e = b.mk_lam(ys_id, BinderInfo::Default, list_alpha_of(&alpha), body);
                    let e = b.mk_lam(xs_id, BinderInfo::Default, list_alpha_of(&alpha), e);
                    let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
                    b.finish(e)
                };

                self.add_decl(Declaration::Theorem {
                    name: Name::from_string("List.length_append"),
                    level_params: vec![u.clone()],
                    type_: length_append_type,
                    value: length_append_value,
                })?;
            }
        }

        self.list_ops_init = true;
        Ok(())
    }

    /// Check if List operations have been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_list_ops` has completed successfully
    /// ENSURES: Pure - no side effects
    #[cfg(test)]
    pub(crate) fn has_list_ops(&self) -> bool {
        self.list_ops_init
    }
}
