// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! For-loop infrastructure: `ForInStep`, the `ForIn` type class, the
//! `ForIn.forIn` method, and the `List` instance the do-notation desugarer
//! emits for `for x in xs do ...`.
//!
//! The do-notation elaborator (`clean-elab` `elab_do_for_core`) lowers a
//! `for`-loop into the fully-applied
//!
//! ```text
//! @ForIn.forIn.{u1,u2,uρ,uα} m ρ α inst β collection init
//!   (fun (x : α) (acc : β) => body >>= fun _ => pure (ForInStep.yield acc'))
//! ```
//!
//! For that term to type-check, the environment must contain:
//!  * `ForInStep` — a real (axiom-free) inductive with `done`/`yield`,
//!  * `ForIn` — the type class (single-constructor structure),
//!  * `ForIn.forIn` — the projection/method,
//!  * an instance for the `ρ = List α` case so the `inst` metavariable can be
//!    synthesised.
//!
//! Everything registered here is a genuine kernel-checked term: the `List`
//! instance is `List.forIn`, built from `List.rec` + `ForInStep.rec` +
//! the already-registered `Bind.bind`/`Pure.pure` constants. No axioms, no
//! `sorry`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize the `ForInStep` inductive type.
    ///
    /// ```text
    /// inductive ForInStep (α : Type u) : Type u where
    ///   | done  (a : α) : ForInStep α
    ///   | yield (a : α) : ForInStep α
    /// ```
    ///
    /// Mirrors the `Option` registration (`init_option`): a single type
    /// parameter, two single-field constructors. Auto-generates
    /// `ForInStep.rec` / `ForInStep.casesOn`, which `List.forIn` uses to
    /// branch on `done` (stop) vs `yield` (continue).
    pub fn init_for_in_step(&mut self) -> Result<(), EnvError> {
        if self.for_in_step_init {
            return Ok(());
        }

        let u = Name::from_string("u");
        let u_lvl = Level::param(u.clone());
        // Type u = Sort (u+1)
        let type_u = Expr::sort(Level::succ(u_lvl.clone()));

        // ForInStep : Type u → Type u
        let for_in_step_type = Expr::pi(BinderInfo::Implicit, type_u.clone(), type_u.clone());

        let for_in_step_const = Expr::const_(Name::from_string("ForInStep"), vec![u_lvl.clone()]);

        // ForInStep.done : {α : Type u} → α → ForInStep α
        let done_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let body = Expr::app(for_in_step_const.clone(), alpha.clone());
            let e = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        // ForInStep.yield : {α : Type u} → α → ForInStep α
        let yield_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (val_id, _val) = b.fresh_local(alpha.clone());
            let body = Expr::app(for_in_step_const.clone(), alpha.clone());
            let e = b.mk_pi(val_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), e);
            b.finish(e)
        };

        let for_in_step_decl = InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("ForInStep"),
                type_: for_in_step_type,
                constructors: vec![
                    Constructor {
                        name: Name::from_string("ForInStep.done"),
                        type_: done_type,
                    },
                    Constructor {
                        name: Name::from_string("ForInStep.yield"),
                        type_: yield_type,
                    },
                ],
            }],
        };

        self.add_inductive(for_in_step_decl)?;
        self.for_in_step_init = true;
        Ok(())
    }

    /// Check if `ForInStep` has been initialized.
    #[cfg(test)]
    pub(crate) fn has_for_in_step(&self) -> bool {
        self.for_in_step_init
    }

    /// Initialize the `ForIn` type class and its `ForIn.forIn` method.
    ///
    /// ```text
    /// class ForIn (m : Type u₁ → Type u₂) (ρ : Type uρ) (α : outParam (Type uα)) where
    ///   forIn : {β : Type u₁} → ρ → β → (α → β → m (ForInStep β)) → m β
    /// ```
    ///
    /// Registered as a single-constructor structure plus the projection
    /// `ForIn.forIn`. The level order `[u₁, u₂, uρ, uα]` matches the
    /// elaborator's `ForIn.forIn.{do_u, do_v, u_rho, u_alpha}` call.
    pub fn init_for_in(&mut self) -> Result<(), EnvError> {
        if self.for_in_init {
            return Ok(());
        }
        self.init_for_in_step()?;
        // The `forIn` field telescope carries a `[Monad m]` instance binder (A4,
        // matching Lean's `ForIn.forIn`), so the `Monad` carrier must exist first.
        self.init_monad_classes()?;

        let u1 = Name::from_string("u_1");
        let u2 = Name::from_string("u_2");
        let urho = Name::from_string("u_rho");
        let ualpha = Name::from_string("u_alpha");
        let u1l = Level::param(u1.clone());
        let u2l = Level::param(u2.clone());
        let url = Level::param(urho.clone());
        let ual = Level::param(ualpha.clone());

        // Type u1 / Type u2 / Type uρ / Type uα
        let type_u1 = Expr::sort(Level::succ(u1l.clone()));
        let type_u2 = Expr::sort(Level::succ(u2l.clone()));
        let type_urho = Expr::sort(Level::succ(url.clone()));
        let type_ualpha = Expr::sort(Level::succ(ual.clone()));

        // m : Type u1 → Type u2
        let m_ty = Expr::pi(BinderInfo::Default, type_u1.clone(), type_u2.clone());

        let levels = vec![u1l.clone(), u2l.clone(), url.clone(), ual.clone()];
        let class_const = Expr::const_(Name::from_string("ForIn"), levels.clone());

        // The single field `forIn`'s type, as a function of (m, ρ, α). FAITHFUL
        // to Lean (src/Init/Core.lean): the `[Monad m]` instance binder sits after
        // `{β}` and before `(x : ρ)` (A4):
        //   {β : Type u1} → [Monad m] → ρ → β → (α → β → m (ForInStep β)) → m β
        //
        // Built as a `child_of` the *calling* builder so its fresh FVar ids are
        // disjoint from the parent's `m`/`ρ`/`α` (a sibling `new()` builder
        // would re-use ids 0,1,2 and the leak-checker would mistake the
        // parent's `α` for an un-closed local).
        let mk_for_in_field_ty =
            |parent: &EnvDeclBuilder, m: &Expr, rho: &Expr, alpha: &Expr| -> Expr {
                let mut b = EnvDeclBuilder::child_of(parent);
                let (beta_id, beta) = b.fresh_local(type_u1.clone());
                // step fn: α → β → m (ForInStep β)
                let for_in_step_beta = Expr::app(
                    Expr::const_(Name::from_string("ForInStep"), vec![u1l.clone()]),
                    beta.clone(),
                );
                let m_step = Expr::app(m.clone(), for_in_step_beta);
                let step_ty = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, _a) = c.fresh_local(alpha.clone());
                    let (acc_id, _acc) = c.fresh_local(beta.clone());
                    let r = m_step.clone();
                    let r = c.mk_pi(acc_id, BinderInfo::Default, beta.clone(), r);
                    let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                    c.finish_child(r)
                };
                let (step_id, _step) = b.fresh_local(step_ty.clone());
                let m_beta = Expr::app(m.clone(), beta.clone());
                // ρ → β → step_ty → m β
                let r = m_beta;
                let r = b.mk_pi(step_id, BinderInfo::Default, step_ty, r);
                let (init_id, _init) = b.fresh_local(beta.clone());
                let r = b.mk_pi(init_id, BinderInfo::Default, beta.clone(), r);
                let (coll_id, _coll) = b.fresh_local(rho.clone());
                let r = b.mk_pi(coll_id, BinderInfo::Default, rho.clone(), r);
                // [Monad m] : @Monad.{u1,u2} m  (instance-implicit; ignored by the body)
                let monad_m = Expr::app(
                    Expr::const_(Name::from_string("Monad"), vec![u1l.clone(), u2l.clone()]),
                    m.clone(),
                );
                let (monad_id, _monad) = b.fresh_local(monad_m.clone());
                let r = b.mk_pi(monad_id, BinderInfo::InstImplicit, monad_m, r);
                let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_u1.clone(), r);
                // `r` still references the parent's m/ρ/α; close only this builder's locals.
                b.finish_child(r)
            };

        // ForIn.mk : {m} → {ρ} → {α} → (forIn : <field ty>) → ForIn m ρ α
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(m_ty.clone());
            let (rho_id, rho) = b.fresh_local(type_urho.clone());
            let (alpha_id, alpha) = b.fresh_local(type_ualpha.clone());
            let field_ty = mk_for_in_field_ty(&b, &m, &rho, &alpha);
            let (field_id, _field) = b.fresh_local(field_ty.clone());
            let class_applied =
                Expr::apps(class_const.clone(), [m.clone(), rho.clone(), alpha.clone()]);
            let r = b.mk_pi(field_id, BinderInfo::Default, field_ty, class_applied);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_ualpha.clone(), r);
            let r = b.mk_pi(rho_id, BinderInfo::Implicit, type_urho.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, m_ty.clone(), r);
            b.finish(r)
        };

        // ForIn : (m : Type u1 → Type u2) → (ρ : Type uρ) → (α : Type uα) → Sort _
        //
        // The carrier must contain the single field's type. That field is
        //   {β : Type u1} → [Monad m] → ρ → β → (α → β → m (ForInStep β)) → m β
        // The `{β : Type u1}` binder contributes `Type (u1+1) = Sort (u1+2)`, and
        // the `[Monad m]` binder's domain `Monad m : Type (max (u1+1) u2)` has type
        // `Sort (max (u1+1) u2 + 1)`, so `infer_sort` of the field yields
        // `max (u1+2) (max (u1+1) u2 + 1) (u2+1) (uρ+1) (uα+1)`. The carrier must
        // be at least that (kernel per-field universe check, F2). The Monad term
        // `succ (max (succ u1) u2)` is the new contribution A4 adds.
        let monad_field_sort = Level::succ(Level::max(Level::succ(u1l.clone()), u2l.clone()));
        let class_result_sort = Expr::sort(Level::max(
            Level::max(
                Level::max(
                    Level::succ(Level::succ(u1l.clone())),
                    Level::succ(u2l.clone()),
                ),
                monad_field_sort,
            ),
            Level::max(Level::succ(url.clone()), Level::succ(ual.clone())),
        ));
        let class_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, _m) = b.fresh_local(m_ty.clone());
            let (rho_id, _rho) = b.fresh_local(type_urho.clone());
            let (alpha_id, _alpha) = b.fresh_local(type_ualpha.clone());
            let r = class_result_sort.clone();
            let r = b.mk_pi(alpha_id, BinderInfo::Default, type_ualpha.clone(), r);
            let r = b.mk_pi(rho_id, BinderInfo::Default, type_urho.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Default, m_ty.clone(), r);
            b.finish(r)
        };

        let for_in_ind = InductiveDecl {
            level_params: vec![u1.clone(), u2.clone(), urho.clone(), ualpha.clone()],
            num_params: 3,
            types: vec![InductiveType {
                name: Name::from_string("ForIn"),
                type_: class_type,
                constructors: vec![Constructor {
                    name: Name::from_string("ForIn.mk"),
                    type_: ctor_type,
                }],
            }],
        };
        self.add_inductive(for_in_ind)?;

        self.register_structure_fields(
            Name::from_string("ForIn"),
            vec![Name::from_string("forIn")],
        )?;

        self.register_class(KernelClassInfo {
            name: Name::from_string("ForIn"),
            num_params: 3,
            // α (index 2) is an outParam: synthesis determines it from the
            // collection type ρ (List α ⇒ α). m and ρ drive resolution.
            out_params: vec![2],
            semi_out_params: vec![],
        });

        // ForIn.forIn : {m} → {ρ} → {α} → [self : ForIn m ρ α] → {β} → ρ → β →
        //               (α → β → m (ForInStep β)) → m β
        //   := fun {m} {ρ} {α} (self : ForIn m ρ α) => self.forIn   (proj field 0)
        let proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(m_ty.clone());
            let (rho_id, rho) = b.fresh_local(type_urho.clone());
            let (alpha_id, alpha) = b.fresh_local(type_ualpha.clone());
            let class_applied =
                Expr::apps(class_const.clone(), [m.clone(), rho.clone(), alpha.clone()]);
            let (self_id, _self) = b.fresh_local(class_applied.clone());
            let field_ty = mk_for_in_field_ty(&b, &m, &rho, &alpha);
            let r = field_ty;
            let r = b.mk_pi(self_id, BinderInfo::InstImplicit, class_applied, r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_ualpha.clone(), r);
            let r = b.mk_pi(rho_id, BinderInfo::Implicit, type_urho.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, m_ty.clone(), r);
            b.finish(r)
        };
        let proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(m_ty.clone());
            let (rho_id, rho) = b.fresh_local(type_urho.clone());
            let (alpha_id, alpha) = b.fresh_local(type_ualpha.clone());
            let class_applied =
                Expr::apps(class_const.clone(), [m.clone(), rho.clone(), alpha.clone()]);
            let (self_id, self_e) = b.fresh_local(class_applied.clone());
            // self.forIn  (structure projection, field index 0)
            let body = Expr::proj(Name::from_string("ForIn"), 0, self_e);
            let r = b.mk_lam(self_id, BinderInfo::InstImplicit, class_applied, body);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_ualpha.clone(), r);
            let r = b.mk_lam(rho_id, BinderInfo::Implicit, type_urho.clone(), r);
            let r = b.mk_lam(m_id, BinderInfo::Implicit, m_ty.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: Name::from_string("ForIn.forIn"),
            level_params: vec![u1.clone(), u2.clone(), urho.clone(), ualpha.clone()],
            type_: proj_type,
            value: proj_value,
            is_reducible: true,
        })?;

        self.for_in_init = true;
        Ok(())
    }

    /// Check if the `ForIn` class has been initialized.
    #[cfg(test)]
    pub(crate) fn has_for_in(&self) -> bool {
        self.for_in_init
    }

    /// Initialize `List.forIn` and the `instForInList` instance.
    ///
    /// ```text
    /// def List.forIn {m : Type u1 → Type u2} {α : Type u1} {β : Type u1}
    ///     (as : List α) (init : β) (f : α → β → m (ForInStep β)) : m β :=
    ///   List.rec
    ///     (motive := fun _ => β → m β)
    ///     (fun acc => Pure.pure acc)
    ///     (fun hd _ ih acc =>
    ///        Bind.bind (f hd acc) (fun s =>
    ///          ForInStep.rec (fun b => Pure.pure b) (fun b => ih b) s))
    ///     as
    ///     init
    /// ```
    ///
    /// `α` and `β` share the monad-domain level `u1` (so `List α` and the
    /// `ForInStep β` flowing through the monad live in `Type u1`). Built purely
    /// from `List.rec`, `ForInStep.rec`, `Bind.bind`, `Pure.pure` — no axioms,
    /// no `[Monad m]` premise (clean's `Bind`/`Pure` are metavariable-resolved,
    /// not synthesised).
    pub fn init_list_for_in_inst(&mut self) -> Result<(), EnvError> {
        if self.list_for_in_inst_init {
            return Ok(());
        }
        self.init_for_in()?;
        self.init_list()?;
        self.init_monad_classes()?;

        let u1 = Name::from_string("u_1");
        let u2 = Name::from_string("u_2");
        let u1l = Level::param(u1.clone());
        let u2l = Level::param(u2.clone());
        let type_u1 = Expr::sort(Level::succ(u1l.clone()));
        let m_ty = Expr::pi(
            BinderInfo::Default,
            type_u1.clone(),
            Expr::sort(Level::succ(u2l.clone())),
        );
        let list_const = Expr::const_(Name::from_string("List"), vec![u1l.clone()]);

        let bind_const = Expr::const_(
            Name::from_string("Bind.bind"),
            vec![u1l.clone(), u2l.clone()],
        );
        let pure_const = Expr::const_(
            Name::from_string("Pure.pure"),
            vec![u1l.clone(), u2l.clone()],
        );

        // ── List.forIn type ──────────────────────────────────────────────
        // {m} → {α} → {β} → List α → β → (α → β → m (ForInStep β)) → m β
        //
        // `child_of` the caller so fresh ids stay disjoint from the parent's
        // m/α/β (see the analogous note in `init_for_in`).
        let mk_step_fn_ty =
            |parent: &EnvDeclBuilder, alpha: &Expr, beta: &Expr, m: &Expr| -> Expr {
                let mut c = EnvDeclBuilder::child_of(parent);
                let (a_id, _a) = c.fresh_local(alpha.clone());
                let (acc_id, _acc) = c.fresh_local(beta.clone());
                let for_in_step_beta = Expr::app(
                    Expr::const_(Name::from_string("ForInStep"), vec![u1l.clone()]),
                    beta.clone(),
                );
                let m_step = Expr::app(m.clone(), for_in_step_beta);
                let r = m_step;
                let r = c.mk_pi(acc_id, BinderInfo::Default, beta.clone(), r);
                let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };

        // [Monad m] : @Monad.{u1,u2} m — the (ignored) instance binder that aligns
        // `List.forIn`'s telescope with the corrected `ForIn` field type (A4).
        let monad_m_ty = |m: &Expr| -> Expr {
            Expr::app(
                Expr::const_(Name::from_string("Monad"), vec![u1l.clone(), u2l.clone()]),
                m.clone(),
            )
        };

        let list_for_in_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(m_ty.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u1.clone());
            let (beta_id, beta) = b.fresh_local(type_u1.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let step_ty = mk_step_fn_ty(&b, &alpha, &beta, &m);
            let m_beta = Expr::app(m.clone(), beta.clone());
            let (f_id, _f) = b.fresh_local(step_ty.clone());
            let (init_id, _init) = b.fresh_local(beta.clone());
            let (as_id, _as) = b.fresh_local(list_alpha.clone());
            let monad_m = monad_m_ty(&m);
            let (monad_id, _monad) = b.fresh_local(monad_m.clone());
            let r = m_beta;
            let r = b.mk_pi(f_id, BinderInfo::Default, step_ty, r);
            let r = b.mk_pi(init_id, BinderInfo::Default, beta.clone(), r);
            let r = b.mk_pi(as_id, BinderInfo::Default, list_alpha.clone(), r);
            // [Monad m] sits after {β} and before (as : List α), mirroring the
            // ForIn field telescope `{β} → [Monad m] → ρ → …`.
            let r = b.mk_pi(monad_id, BinderInfo::InstImplicit, monad_m, r);
            let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_u1.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u1.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, m_ty.clone(), r);
            b.finish(r)
        };

        // ── List.forIn value ─────────────────────────────────────────────
        let list_for_in_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(m_ty.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u1.clone());
            let (beta_id, beta) = b.fresh_local(type_u1.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let step_ty = mk_step_fn_ty(&b, &alpha, &beta, &m);
            let m_beta = Expr::app(m.clone(), beta.clone());
            let (f_id, f) = b.fresh_local(step_ty.clone());
            let (init_id, init) = b.fresh_local(beta.clone());
            let (as_id, as_e) = b.fresh_local(list_alpha.clone());
            // [Monad m] — bound but ignored by the body (clean's Bind/Pure are
            // metavariable-resolved, not synthesised from the Monad instance).
            let monad_m = monad_m_ty(&m);
            let (monad_id, _monad) = b.fresh_local(monad_m.clone());

            // motive : List α → Sort _ := fun _ => β → m β
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (l_id, _l) = c.fresh_local(list_alpha.clone());
                let arrow = Expr::pi(BinderInfo::Default, beta.clone(), m_beta.clone());
                let lam = c.mk_lam(l_id, BinderInfo::Default, list_alpha.clone(), arrow);
                c.finish_child(lam)
            };

            // nil case : β → m β := fun acc => @Pure.pure m β acc
            let nil_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (acc_id, acc) = c.fresh_local(beta.clone());
                let pure_acc =
                    Expr::apps(pure_const.clone(), [m.clone(), beta.clone(), acc.clone()]);
                let lam = c.mk_lam(acc_id, BinderInfo::Default, beta.clone(), pure_acc);
                c.finish_child(lam)
            };

            // cons case : α → List α → (β → m β) → (β → m β)
            //   := fun hd _ ih acc =>
            //        @Bind.bind m (ForInStep β) β (f hd acc)
            //          (fun (s : ForInStep β) =>
            //             @ForInStep.rec β (fun _ => m β)
            //               (fun b => @Pure.pure m β b)   -- done
            //               (fun b => ih b)               -- yield
            //               s)
            let for_in_step_beta = Expr::app(
                Expr::const_(Name::from_string("ForInStep"), vec![u1l.clone()]),
                beta.clone(),
            );
            let m_for_in_step_beta = Expr::app(m.clone(), for_in_step_beta.clone());
            let ih_ty = Expr::pi(BinderInfo::Default, beta.clone(), m_beta.clone());
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hd_id, hd) = c.fresh_local(alpha.clone());
                let (tl_id, _tl) = c.fresh_local(list_alpha.clone());
                let (ih_id, ih) = c.fresh_local(ih_ty.clone());
                let (acc_id, acc) = c.fresh_local(beta.clone());

                // f hd acc : m (ForInStep β)
                let f_hd_acc = Expr::apps(f.clone(), [hd.clone(), acc.clone()]);

                // ForInStep.rec motive: fun (_ : ForInStep β) => m β
                let step_motive = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (s_id, _s) = d.fresh_local(for_in_step_beta.clone());
                    d.finish_child(d.mk_lam(
                        s_id,
                        BinderInfo::Default,
                        for_in_step_beta.clone(),
                        m_beta.clone(),
                    ))
                };
                // done minor: fun (b : β) => @Pure.pure m β b
                let done_minor = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (b_id, bv) = d.fresh_local(beta.clone());
                    let pure_b =
                        Expr::apps(pure_const.clone(), [m.clone(), beta.clone(), bv.clone()]);
                    d.finish_child(d.mk_lam(b_id, BinderInfo::Default, beta.clone(), pure_b))
                };
                // yield minor: fun (b : β) => ih b
                let yield_minor = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (b_id, bv) = d.fresh_local(beta.clone());
                    let ih_b = Expr::app(ih.clone(), bv.clone());
                    d.finish_child(d.mk_lam(b_id, BinderInfo::Default, beta.clone(), ih_b))
                };

                // continuation: fun (s : ForInStep β) =>
                //   @ForInStep.rec.{u2,u1} β step_motive done_minor yield_minor s
                let cont = {
                    let mut d = EnvDeclBuilder::child_of(&c);
                    let (s_id, s_e) = d.fresh_local(for_in_step_beta.clone());
                    let for_in_step_rec = Expr::const_(
                        Name::from_string("ForInStep.rec"),
                        vec![Level::succ(u2l.clone()), u1l.clone()],
                    );
                    let rec_app = Expr::apps(
                        for_in_step_rec,
                        [
                            beta.clone(),
                            step_motive.clone(),
                            done_minor.clone(),
                            yield_minor.clone(),
                            s_e.clone(),
                        ],
                    );
                    d.finish_child(d.mk_lam(
                        s_id,
                        BinderInfo::Default,
                        for_in_step_beta.clone(),
                        rec_app,
                    ))
                };

                // @Bind.bind m (ForInStep β) β (f hd acc) cont
                let bind_app = Expr::apps(
                    bind_const.clone(),
                    [
                        m.clone(),
                        for_in_step_beta.clone(),
                        beta.clone(),
                        f_hd_acc,
                        cont,
                    ],
                );
                let _ = m_for_in_step_beta; // (documentary)

                let lam = c.mk_lam(acc_id, BinderInfo::Default, beta.clone(), bind_app);
                let lam = c.mk_lam(ih_id, BinderInfo::Default, ih_ty.clone(), lam);
                let lam = c.mk_lam(tl_id, BinderInfo::Default, list_alpha.clone(), lam);
                let lam = c.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), lam);
                c.finish_child(lam)
            };

            // @List.rec.{u2, u1} α motive nil_case cons_case as : β → m β
            // List.rec level params: [motive-universe, element-universe].
            // motive lands in Type u2 (β → m β : Sort (max (u1+1) (u2+1)));
            // use succ u2 as the motive level (m β : Type u2 dominates).
            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![
                    Level::succ(Level::max(u1l.clone(), u2l.clone())),
                    u1l.clone(),
                ],
            );
            let rec_app = Expr::apps(
                list_rec,
                [alpha.clone(), motive, nil_case, cons_case, as_e.clone()],
            );
            // apply to init : (β → m β) init = m β
            let body = Expr::app(rec_app, init.clone());

            let e = b.mk_lam(f_id, BinderInfo::Default, step_ty, body);
            let e = b.mk_lam(init_id, BinderInfo::Default, beta.clone(), e);
            let e = b.mk_lam(as_id, BinderInfo::Default, list_alpha.clone(), e);
            // [Monad m] lambda — mirrors the type's instance binder (ignored body).
            let e = b.mk_lam(monad_id, BinderInfo::InstImplicit, monad_m, e);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, type_u1.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u1.clone(), e);
            let e = b.mk_lam(m_id, BinderInfo::Implicit, m_ty.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("List.forIn"),
            level_params: vec![u1.clone(), u2.clone()],
            type_: list_for_in_type,
            value: list_for_in_value,
            is_reducible: true,
        })?;

        // instForInList : {m} → {α} → ForIn m (List α) α := ForIn.mk List.forIn
        let for_in_mk = Expr::const_(
            Name::from_string("ForIn.mk"),
            // ForIn.{u1,u2,uρ,uα}: here ρ = List α : Type u1, α : Type u1.
            vec![u1l.clone(), u2l.clone(), u1l.clone(), u1l.clone()],
        );

        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(m_ty.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u1.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            // ForIn m (List α) α
            let for_in_applied = Expr::apps(
                Expr::const_(
                    Name::from_string("ForIn"),
                    vec![u1l.clone(), u2l.clone(), u1l.clone(), u1l.clone()],
                ),
                [m.clone(), list_alpha.clone(), alpha.clone()],
            );
            let r = for_in_applied;
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u1.clone(), r);
            let r = b.mk_pi(m_id, BinderInfo::Implicit, m_ty.clone(), r);
            b.finish(r)
        };

        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (m_id, m) = b.fresh_local(m_ty.clone());
            let (alpha_id, alpha) = b.fresh_local(type_u1.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            // List.forIn instantiated at this m and α (β stays implicit/general):
            //   @List.forIn.{u1,u2} m α   -- a {β} → List α → β → … function,
            // which is exactly the field type {β} → ρ → β → (…) → m β with ρ = List α.
            let list_for_in_inst = Expr::apps(
                Expr::const_(
                    Name::from_string("List.forIn"),
                    vec![u1l.clone(), u2l.clone()],
                ),
                [m.clone(), alpha.clone()],
            );
            // ForIn.mk m (List α) α List.forIn
            let body = Expr::apps(
                for_in_mk.clone(),
                [
                    m.clone(),
                    list_alpha.clone(),
                    alpha.clone(),
                    list_for_in_inst,
                ],
            );
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u1.clone(), body);
            let r = b.mk_lam(m_id, BinderInfo::Implicit, m_ty.clone(), r);
            b.finish(r)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instForInList"),
            level_params: vec![u1.clone(), u2.clone()],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string("instForInList"),
            class_name: Name::from_string("ForIn"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        self.list_for_in_inst_init = true;
        Ok(())
    }

    /// Check if the `List` `ForIn` instance has been initialized.
    #[cfg(test)]
    pub(crate) fn has_list_for_in_inst(&self) -> bool {
        self.list_for_in_inst_init
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;

    /// `ForInStep` and `ForIn` are registered by the prelude: `ForInStep` as a
    /// real inductive (with auto-generated `done`/`yield` constructors), `ForIn`
    /// as a single-constructor structure recognised as a class.
    #[test]
    fn test_for_in_inductives_registered() {
        let env = Environment::with_prelude();
        assert!(env.has_for_in_step(), "ForInStep must be in the prelude");
        assert!(env.has_for_in(), "ForIn must be in the prelude");
        assert!(
            env.has_list_for_in_inst(),
            "the List ForIn instance must be in the prelude"
        );

        assert!(
            env.get_inductive(&Name::from_string("ForInStep")).is_some(),
            "ForInStep inductive must exist"
        );
        for ctor in ["ForInStep.done", "ForInStep.yield"] {
            assert!(
                env.get_const(&Name::from_string(ctor)).is_some(),
                "{ctor} constructor must exist"
            );
        }
        assert!(
            env.get_inductive(&Name::from_string("ForIn")).is_some(),
            "ForIn structure must exist"
        );
        assert!(
            env.is_class(&Name::from_string("ForIn")),
            "ForIn must be a registered class"
        );
    }

    /// `ForIn.forIn`, `List.forIn`, and `instForInList` are axiom-free
    /// `Definition`s whose declared types type-check (so the closed terms are
    /// well-formed and contain no `sorry`).
    #[test]
    fn test_for_in_members_are_axiom_free_definitions() {
        let env = Environment::with_prelude();

        // (name, level-arg count for a representative monomorphic instantiation)
        let checks: [(&str, Vec<Level>); 3] = [
            (
                "ForIn.forIn",
                vec![Level::zero(), Level::zero(), Level::zero(), Level::zero()],
            ),
            ("List.forIn", vec![Level::zero(), Level::zero()]),
            ("instForInList", vec![Level::zero(), Level::zero()]),
        ];

        for (name, levels) in checks {
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
        }
    }

    /// The whole prelude is initialised without any new trust-boundary axioms
    /// introduced by the for-in registrations (idempotent, kernel-checked).
    #[test]
    fn test_for_in_init_is_idempotent() {
        let mut env = Environment::with_prelude();
        // Re-running the initializers must be a no-op (no duplicate-decl error).
        env.init_for_in_step().expect("init_for_in_step idempotent");
        env.init_for_in().expect("init_for_in idempotent");
        env.init_list_for_in_inst()
            .expect("init_list_for_in_inst idempotent");
    }
}
