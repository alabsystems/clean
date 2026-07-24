// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real `Pure` / `Bind` class structures and `Option` / `List` monad
//! instances (Brick B07 — instance-projection defeq reduction,
//! `docs/plans/GAP_SWEEP_2026-07-09.md`).
//!
//! # Diagnosis (B07)
//!
//! The gap-sweep symptom was "`Pure.pure`/`Bind.bind` applied through the
//! prelude `Monad Option` instance never reduce in def-eq, so no do-block
//! value is rfl-certifiable". The presumed mechanism (a stuck
//! instance-projection chain in the kernel's whnf/def-eq path) turned out to
//! be WRONG: the prelude had **no monad instances at all**. `init_monad_classes`
//! (`data_monad.rs`) models `Pure.pure` / `Bind.bind` as value-less,
//! instance-less **axioms** (`Pure.pure : {m} → {α} → α → m α`), and the
//! do-notation elaborator applies them with no `[inst]` argument. An axiom has
//! no body, so kernel delta-unfolding is impossible **by design** — there was
//! never anything for proj-of-ctor iota to act on. The kernel's actual
//! instance machinery (delta on instance definitions + primitive-`Proj`-of-mk
//! iota, `tc/whnf.rs` / `tc/whnf_proj.rs`) is fine and already proven by the
//! `Seq*` classes (`data_seq_classes.rs`) and the structures probe family
//! (GAP_SWEEP §4.2: `p01`/`p11`/`p12`/`p20` all `MATCH_ACCEPT`).
//!
//! # Fix (registration + elaboration; ZERO kernel tc/ changes)
//!
//! This module registers what Lean actually has (v4.30.0-rc2
//! `Init/Prelude.lean:3698` (`Bind`) / `:3714` (`Pure`); the upstream
//! `Monad Option` instance is core too -- `Init/Data/Option/Basic.lean:575`):
//!
//! ```text
//! class Pure (f : Type u → Type v) : Type (max (u+1) v) where
//!   pure {α : Type u} : α → f α
//! class Bind (m : Type u → Type v) : Type (max (u+1) v) where
//!   bind : {α β : Type u} → m α → (α → m β) → m β
//! ```
//!
//! as fully kernel-checked single-constructor structures (no axioms), plus
//! `Option` (and, builtin-prelude-only, `List`) instances with real
//! `Option.some`/`Option.bind`/`List.rec` bodies. The elaborator's
//! materialization pass (`clean-elab::infer::elab_monad_materialize`) then
//! rewrites stub applications `Pure.pure m α v` / `Bind.bind m α β ma f` over
//! a concrete monad `m` with a registered instance into the instance-projected
//! form `(Proj Pure 0 inst) α v` / `(Proj Bind 0 inst) α β ma f`. The kernel
//! reduces those with its ORDINARY machinery — delta on the instance
//! definition, proj-of-mk iota, beta, then recursor iota on
//! `Option.bind`/`List.rec` — exactly the reduction sequence Lean's kernel
//! performs on its own elaboration output (`src/kernel/type_checker.cpp`:
//! instances are plain definitions unfolded by delta; projections reduce via
//! proj-of-constructor; no monad special-casing exists). No new definitional
//! equalities are introduced anywhere: every step is derivable from the
//! registered environment.
//!
//! # Why the projection CONSTANTS are not registered here
//!
//! The natural projection names `Pure.pure` / `Bind.bind` are owned by the
//! legacy instance-less axiom stubs, which the generic prelude lanes
//! (`List.forIn`, `List.mapM`, `Bind.kleisli*`, the StateT/ExceptT do-control
//! stack) still spell their telescopes against. Replacing the stubs with
//! `[inst]`-carrying projections is the (larger) follow-up migration; until
//! then the materialization pass emits primitive `Proj` nodes directly, which
//! the kernel treats identically to Lean's compiled projections.
//!
//! # Lean-core fidelity of the `List` gating
//!
//! Lean 4 v4.30.0-rc2 **core has no `Monad`/`Bind`/`Pure` instance for
//! `List`** (verified by grep of `Init/` — GAP_SWEEP §5 OVER_ACCEPT-01; the
//! instance lives in downstream libraries such as Mathlib). Therefore
//! [`Environment::init_monad_list_insts`] is NOT part of the prelude init
//! chain: the `clean check --prelude lean4-core` lane omits it (and enables
//! the strict monad-instance gate), so `do`-blocks over `List` are rejected
//! with a failed-to-synthesize error exactly like real Lean core, while the
//! default builtin prelude keeps them (a documented Clean-native extension,
//! same policy as the Clean-native `instSeq*Option` names in
//! `data_seq_classes.rs`).
//!
//! IMPORT MODE (`suppress_lossy_structure_stubs`): the instance definitions
//! are withheld (the genuine olean closure carries Lean's own
//! `instMonadOption`-derived chain); the class structures follow the same
//! ungated policy as `init_seq_classes` (identical registration pattern, same
//! olean-dedup path).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Which of the two monad-operation classes is being built.
#[derive(Clone, Copy)]
enum MonadOpShape {
    /// `pure : {α : Type u} → α → f α`
    Pure,
    /// `bind : {α β : Type u} → m α → (α → m β) → m β`
    Bind,
}

impl MonadOpShape {
    fn class_name(self) -> &'static str {
        match self {
            MonadOpShape::Pure => "Pure",
            MonadOpShape::Bind => "Bind",
        }
    }

    fn field_name(self) -> &'static str {
        match self {
            MonadOpShape::Pure => "pure",
            MonadOpShape::Bind => "bind",
        }
    }
}

/// The field type of the class over carrier `f`:
/// - `Pure`: `{α : Type u} → α → f α`
/// - `Bind`: `{α β : Type u} → f α → (α → f β) → f β`
fn monad_op_field_ty(
    parent: &EnvDeclBuilder,
    type_u: &Expr,
    f: &Expr,
    shape: MonadOpShape,
) -> Expr {
    let mut c = EnvDeclBuilder::child_of(parent);
    match shape {
        MonadOpShape::Pure => {
            let (alpha_id, alpha) = c.fresh_local(type_u.clone());
            let f_alpha = Expr::app(f.clone(), alpha.clone());
            let (a_id, _a) = c.fresh_local(alpha.clone());
            let r = f_alpha;
            let r = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
            let r = c.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            c.finish_child(r)
        }
        MonadOpShape::Bind => {
            let (alpha_id, alpha) = c.fresh_local(type_u.clone());
            let (beta_id, beta) = c.fresh_local(type_u.clone());
            let f_alpha = Expr::app(f.clone(), alpha.clone());
            let f_beta = Expr::app(f.clone(), beta.clone());
            let (ma_id, _ma) = c.fresh_local(f_alpha.clone());
            let k_ty = {
                let mut d = EnvDeclBuilder::child_of(&c);
                let (x_id, _x) = d.fresh_local(alpha.clone());
                let r = f_beta.clone();
                let r = d.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                d.finish_child(r)
            };
            let (k_id, _k) = c.fresh_local(k_ty.clone());
            let r = f_beta;
            let r = c.mk_pi(k_id, BinderInfo::Default, k_ty, r);
            let r = c.mk_pi(ma_id, BinderInfo::Default, f_alpha, r);
            let r = c.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = c.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            c.finish_child(r)
        }
    }
}

impl Environment {
    /// Register the `Pure` and `Bind` classes as real single-constructor
    /// structures (Lean `Init/Prelude.lean` shapes), fully kernel-checked.
    ///
    /// Registration pattern is byte-for-byte the `init_seq_classes` template
    /// (`data_seq_classes.rs`) minus the named projection definitions — see
    /// the module doc for why those names stay with the legacy stubs.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.pure_bind_classes_init == true`
    /// ENSURES: Idempotent
    pub(crate) fn init_pure_bind_classes(&mut self) -> Result<(), EnvError> {
        if self.pure_bind_classes_init {
            return Ok(());
        }

        for shape in [MonadOpShape::Pure, MonadOpShape::Bind] {
            self.init_monad_op_class(shape)?;
        }

        self.pure_bind_classes_init = true;
        Ok(())
    }

    fn init_monad_op_class(&mut self, shape: MonadOpShape) -> Result<(), EnvError> {
        let class_name = Name::from_string(shape.class_name());
        let ctor_name = Name::from_string(&format!("{}.mk", shape.class_name()));

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let type_v = Expr::sort(Level::succ(v_level.clone()));
        let m_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone());
        // Type (max (u+1) v) — Lean: `class Pure (f : Type u → Type v) : Type (max (u+1) v)`
        let result_sort = Expr::sort(Level::succ(Level::max(
            Level::succ(u_level.clone()),
            v_level.clone(),
        )));
        let class_const = Expr::const_(class_name.clone(), vec![u_level, v_level]);

        // <Class>.mk : {f : Type u → Type v} → (field : …) → <Class> f
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(m_type.clone());
            let field_ty = monad_op_field_ty(&b, &type_u, &f, shape);
            let (field_id, _) = b.fresh_local(field_ty.clone());
            let class_ty = Expr::app(class_const.clone(), f.clone());
            let r = b.mk_pi(field_id, BinderInfo::Default, field_ty, class_ty);
            let r = b.mk_pi(f_id, BinderInfo::Implicit, m_type.clone(), r);
            b.finish(r)
        };

        self.add_inductive(InductiveDecl {
            level_params: vec![u, v],
            num_params: 1,
            types: vec![InductiveType {
                name: class_name.clone(),
                type_: Expr::pi(BinderInfo::Default, m_type.clone(), result_sort),
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
            name: class_name,
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        Ok(())
    }

    /// Register `instPureOption : Pure Option` / `instBindOption : Bind Option`
    /// with real `Option.some` / `Option.bind` bodies (no axioms, no sorry):
    ///
    /// ```text
    /// instPureOption : Pure Option := ⟨fun a => Option.some a⟩
    /// instBindOption : Bind Option := ⟨fun ma f => Option.bind ma f⟩
    /// ```
    ///
    /// Lean fidelity note: upstream Lean derives these through the single
    /// `instMonadOption : Monad Option` (`Init/Prelude.lean`; `pure := some`,
    /// `bind := Option.bind`); Clean's prelude has no real `Monad`/`Applicative`
    /// hierarchy yet (`Monad` is still an opaque carrier axiom), so the two
    /// leaf-class instances (definitionally equal to Lean's derived
    /// `Monad.toPure`/`Monad.toBind` chain on `Option`) are registered directly
    /// under Clean-native names — the same policy as `instSeq*Option` in
    /// `data_seq_classes.rs`.
    ///
    /// IMPORT MODE (`suppress_lossy_structure_stubs`): withheld — the genuine
    /// olean closure carries Lean's own `Monad Option` instance chain.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.monad_option_insts_init == true`
    /// ENSURES: Idempotent
    pub(crate) fn init_monad_option_insts(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.monad_option_insts_init {
            return Ok(());
        }

        self.init_pure_bind_classes()?;
        self.init_option()?;
        self.init_option_ops()?; // Option.bind (real List.rec-style body)

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let uu = vec![u_level.clone(), u_level.clone()];
        let option_const = Expr::const_(Name::from_string("Option"), vec![u_level.clone()]);

        // instPureOption : Pure Option := Pure.mk Option (fun {α} (a : α) => Option.some α a)
        let pure_field = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let some_const = Expr::const_(Name::from_string("Option.some"), vec![u_level.clone()]);
            let body = Expr::apps(some_const, [alpha.clone(), a]);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_monad_op_instance("instPureOption", "Pure", &u, &uu, &option_const, pure_field)?;

        // instBindOption : Bind Option
        //   := Bind.mk Option (fun {α β} (ma : Option α) (f : α → Option β) => Option.bind α β ma f)
        let bind_field = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let opt_alpha = Expr::app(option_const.clone(), alpha.clone());
            let opt_beta = Expr::app(option_const.clone(), beta.clone());
            let (ma_id, ma) = b.fresh_local(opt_alpha.clone());
            let f_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(alpha.clone());
                let r = opt_beta.clone();
                let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (f_id, f) = b.fresh_local(f_ty.clone());
            // Option.bind.{u,u} α β ma f
            let option_bind = Expr::const_(Name::from_string("Option.bind"), uu.clone());
            let body = Expr::apps(option_bind, [alpha.clone(), beta.clone(), ma, f]);
            let r = b.mk_lam(f_id, BinderInfo::Default, f_ty, body);
            let r = b.mk_lam(ma_id, BinderInfo::Default, opt_alpha, r);
            let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_monad_op_instance("instBindOption", "Bind", &u, &uu, &option_const, bind_field)?;

        self.monad_option_insts_init = true;
        Ok(())
    }

    /// Register `instPureId : Pure Id` / `instBindId : Bind Id` with the real
    /// identity-monad bodies (no axioms, no sorry) — Brick B22 (Id-monad
    /// reduction, `docs/plans/GAP_SWEEP_2026-07-09.md`):
    ///
    /// ```text
    /// instPureId : Pure Id := ⟨fun a => a⟩
    /// instBindId : Bind Id := ⟨fun ma f => f ma⟩
    /// ```
    ///
    /// These are the leaf-class projections of Lean's single core
    /// `instance : Monad Id := { pure := fun x => x, bind := fun x f => f x }`
    /// (`Init/Prelude.lean`). With `Id` now a reducible def (`Id α ≡ α`,
    /// `data_monad.rs::init_id`), the elaborator's materialization pass
    /// (`clean-elab::infer::elab_monad_materialize`) rewrites `Pure.pure Id α v`
    /// / `Bind.bind Id α β ma f` into instance-projected form and the kernel
    /// reduces it through ORDINARY delta + proj-of-mk iota + beta:
    /// `pure v ↦ v`, `bind ma f ↦ f ma`. Composed with the identity `Id.run`,
    /// `Id.run (pure 5)` reduces to `5` — the do p13/p14 value pin. Lean's
    /// kernel performs the identical sequence on its own elaboration output;
    /// no new definitional equality is introduced. Registered directly under
    /// Clean-native leaf names because Clean's `Monad` is still an opaque
    /// carrier axiom — the same policy as `instPureOption`/`instBindOption`.
    ///
    /// IMPORT MODE (`suppress_lossy_structure_stubs`): withheld — the genuine
    /// olean closure carries Lean's own `instMonadId`-derived chain.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.monad_id_insts_init == true`
    /// ENSURES: Idempotent
    pub(crate) fn init_monad_id_insts(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.monad_id_insts_init {
            return Ok(());
        }

        self.init_pure_bind_classes()?;
        self.init_id()?; // Id/Id.mk/Id.run reducible defs (identity monad)

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let uu = vec![u_level.clone(), u_level.clone()];
        let id_const = Expr::const_(Name::from_string("Id"), vec![u_level.clone()]);

        // instPureId : Pure Id := Pure.mk Id (fun {α} (a : α) => a)
        // `pure a = a` — the body `a : α` checks against `Id α ≡ α`.
        let pure_field = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), a);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_monad_op_instance("instPureId", "Pure", &u, &uu, &id_const, pure_field)?;

        // instBindId : Bind Id
        //   := Bind.mk Id (fun {α β} (ma : Id α) (f : α → Id β) => f ma)
        // `bind ma f = f ma` — `ma : Id α ≡ α` is exactly `f`'s domain.
        let bind_field = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let id_alpha = Expr::app(id_const.clone(), alpha.clone());
            let id_beta = Expr::app(id_const.clone(), beta.clone());
            let (ma_id, ma) = b.fresh_local(id_alpha.clone());
            let f_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(alpha.clone());
                let r = id_beta.clone();
                let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let body = Expr::app(f, ma);
            let r = b.mk_lam(f_id, BinderInfo::Default, f_ty, body);
            let r = b.mk_lam(ma_id, BinderInfo::Default, id_alpha, r);
            let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_monad_op_instance("instBindId", "Bind", &u, &uu, &id_const, bind_field)?;

        self.monad_id_insts_init = true;
        Ok(())
    }

    /// Register `instPureList : Pure List` / `instBindList : Bind List` with
    /// real `List.cons`/`List.rec`+`List.append` bodies:
    ///
    /// ```text
    /// instPureList : Pure List := ⟨fun a => [a]⟩
    /// instBindList : Bind List := ⟨fun ma f => List.rec [] (fun hd _ ih => f hd ++ ih) ma⟩
    /// ```
    ///
    /// NOT part of the prelude init chain. Lean 4 v4.30.0-rc2 core has NO
    /// `Monad`/`Bind`/`Pure` instance for `List` (GAP_SWEEP_2026-07-09 §5
    /// OVER_ACCEPT-01, verified against `Init/`), so the `--prelude lean4-core`
    /// check lane must reject `do`-blocks over `List`. The `clean check`
    /// builtin-prelude lane calls this explicitly (documented Clean-native
    /// extension).
    ///
    /// IMPORT MODE (`suppress_lossy_structure_stubs`): withheld — `List.append`
    /// (referenced by the bind body) is itself import-gated, and a genuine
    /// olean environment supplies its own List monad chain if any.
    ///
    /// # Errors
    ///
    /// Propagates any `EnvError` from the underlying `add_decl` registrations.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.monad_list_insts_init == true`
    /// ENSURES: Idempotent
    pub fn init_monad_list_insts(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.monad_list_insts_init {
            return Ok(());
        }

        self.init_pure_bind_classes()?;
        self.init_list()?;
        self.init_list_ops()?; // List.append (real List.rec body)

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let uu = vec![u_level.clone(), u_level.clone()];
        let list_const = Expr::const_(Name::from_string("List"), vec![u_level.clone()]);
        let list_nil = Expr::const_(Name::from_string("List.nil"), vec![u_level.clone()]);
        let list_cons = Expr::const_(Name::from_string("List.cons"), vec![u_level.clone()]);

        // instPureList : Pure List := Pure.mk List (fun {α} (a : α) => List.cons α a (List.nil α))
        let pure_field = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let nil = Expr::app(list_nil.clone(), alpha.clone());
            let body = Expr::apps(list_cons.clone(), [alpha.clone(), a, nil]);
            let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_monad_op_instance("instPureList", "Pure", &u, &uu, &list_const, pure_field)?;

        // instBindList : Bind List := Bind.mk List
        //   (fun {α β} (ma : List α) (f : α → List β) =>
        //      List.rec (motive := fun _ => List β)
        //        (List.nil β) (fun hd _tl ih => List.append β (f hd) ih) ma)
        let bind_field = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let list_alpha = Expr::app(list_const.clone(), alpha.clone());
            let list_beta = Expr::app(list_const.clone(), beta.clone());
            let (ma_id, ma) = b.fresh_local(list_alpha.clone());
            let f_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, _x) = c.fresh_local(alpha.clone());
                let r = list_beta.clone();
                let r = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            let (f_id, f) = b.fresh_local(f_ty.clone());

            // motive : fun (_ : List α) => List β
            let motive = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (w_id, _w) = c.fresh_local(list_alpha.clone());
                let r = list_beta.clone();
                let r = c.mk_lam(w_id, BinderInfo::Default, list_alpha.clone(), r);
                c.finish_child(r)
            };
            // cons case : fun (hd : α) (_tl : List α) (ih : List β) => List.append β (f hd) ih
            let cons_case = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (hd_id, hd) = c.fresh_local(alpha.clone());
                let (tl_id, _tl) = c.fresh_local(list_alpha.clone());
                let (ih_id, ih) = c.fresh_local(list_beta.clone());
                let append = Expr::const_(Name::from_string("List.append"), vec![u_level.clone()]);
                let fhd = Expr::app(f.clone(), hd.clone());
                let body = Expr::apps(append, [beta.clone(), fhd, ih]);
                let r = c.mk_lam(ih_id, BinderInfo::Default, list_beta.clone(), body);
                let r = c.mk_lam(tl_id, BinderInfo::Default, list_alpha.clone(), r);
                let r = c.mk_lam(hd_id, BinderInfo::Default, alpha.clone(), r);
                c.finish_child(r)
            };
            // List.rec universes [motive-elim, type] = [succ u, u] (List β : Type u = Sort (u+1)).
            let list_rec = Expr::const_(
                Name::from_string("List.rec"),
                vec![Level::succ(u_level.clone()), u_level.clone()],
            );
            let nil_case = Expr::app(list_nil.clone(), beta.clone());
            let body = Expr::apps(list_rec, [alpha.clone(), motive, nil_case, cons_case, ma]);
            let r = b.mk_lam(f_id, BinderInfo::Default, f_ty, body);
            let r = b.mk_lam(ma_id, BinderInfo::Default, list_alpha, r);
            let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_monad_op_instance("instBindList", "Bind", &u, &uu, &list_const, bind_field)?;

        self.monad_list_insts_init = true;
        Ok(())
    }

    /// Shared tail for the monad-op instances: build
    /// `<inst> : <Class> <carrier> := <Class>.mk <carrier> <field_value>`,
    /// `add_decl` it (fully kernel-checked, `is_reducible`), and register the
    /// instance for elaborator synthesis.
    fn add_monad_op_instance(
        &mut self,
        inst_name: &str,
        class_name: &str,
        u: &Name,
        class_levels: &[Level],
        carrier: &Expr,
        field_value: Expr,
    ) -> Result<(), EnvError> {
        let class_const = Expr::const_(Name::from_string(class_name), class_levels.to_vec());
        let class_mk = Expr::const_(
            Name::from_string(&format!("{class_name}.mk")),
            class_levels.to_vec(),
        );
        let inst_type = Expr::app(class_const, carrier.clone());
        let inst_value = Expr::apps(class_mk, [carrier.clone(), field_value]);

        self.add_decl(Declaration::Definition {
            name: Name::from_string(inst_name),
            level_params: vec![u.clone()],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.register_instance(KernelInstanceInfo {
            name: Name::from_string(inst_name),
            class_name: Name::from_string(class_name),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::tc::TypeChecker;
    use crate::{Environment, Expr, Level, Name};

    fn env_with_option_insts() -> Environment {
        let mut env = Environment::new();
        env.init_eq().expect("init_eq");
        env.init_nat().expect("init_nat");
        env.init_monad_option_insts()
            .expect("Pure/Bind classes + Option instances must register (fully kernel-checked)");
        env
    }

    fn nat() -> Expr {
        Expr::const_(Name::from_string("Nat"), vec![])
    }

    fn some_nat(n: u64) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Option.some"), vec![Level::zero()]),
            [nat(), Expr::nat_lit(n)],
        )
    }

    /// `(Proj Bind 0 instBindOption) α β ma f` — the exact shape the
    /// elaborator's materialization pass emits for a do-block bind.
    fn bind_app(ma: Expr, f: Expr) -> Expr {
        let inst = Expr::const_(Name::from_string("instBindOption"), vec![Level::zero()]);
        let head = Expr::proj(Name::from_string("Bind"), 0, inst);
        Expr::apps(head, [nat(), nat(), ma, f])
    }

    /// `(Proj Pure 0 instPureOption) α v`.
    fn pure_app(v: Expr) -> Expr {
        let inst = Expr::const_(Name::from_string("instPureOption"), vec![Level::zero()]);
        let head = Expr::proj(Name::from_string("Pure"), 0, inst);
        Expr::apps(head, [nat(), v])
    }

    /// B07 kernel-level pin: the instance-projected bind/pure chain reduces to
    /// a ground `Option.some` through ORDINARY kernel machinery only (delta on
    /// the instance definition, proj-of-mk iota, beta, `Option.rec` iota) —
    /// the reduction sequence Lean's kernel performs (type_checker.cpp).
    #[test]
    fn test_materialized_bind_pure_chain_is_defeq_to_ground_some() {
        let env = env_with_option_insts();
        let tc = TypeChecker::new(&env);

        // bind (some 3) (fun (x : Nat) => pure x)  ≡  some 3
        let k = Expr::lam(crate::BinderInfo::Default, nat(), pure_app(Expr::bvar(0)));
        let chain = bind_app(some_nat(3), k);
        assert!(
            tc.is_def_eq(&chain, &some_nat(3)),
            "instance-projected bind/pure over Option must reduce to ground some"
        );
    }

    /// none short-circuit: `bind none f ≡ none` (Option.bind's none branch).
    #[test]
    fn test_materialized_bind_none_short_circuits() {
        let env = env_with_option_insts();
        let tc = TypeChecker::new(&env);

        let none = Expr::apps(
            Expr::const_(Name::from_string("Option.none"), vec![Level::zero()]),
            [nat()],
        );
        let k = Expr::lam(crate::BinderInfo::Default, nat(), pure_app(Expr::bvar(0)));
        let chain = bind_app(none.clone(), k);
        assert!(
            tc.is_def_eq(&chain, &none),
            "bind none f must short-circuit to none"
        );
    }

    /// ADVERSARIAL: the new reductions must not over-equate — a chain
    /// producing `some 3` must NOT be def-eq to `some 4`.
    #[test]
    fn test_materialized_chain_rejects_wrong_value() {
        let env = env_with_option_insts();
        let tc = TypeChecker::new(&env);

        let k = Expr::lam(crate::BinderInfo::Default, nat(), pure_app(Expr::bvar(0)));
        let chain = bind_app(some_nat(3), k);
        assert!(
            !tc.is_def_eq(&chain, &some_nat(4)),
            "wrong ground value must stay non-def-eq"
        );
    }

    /// The List instances register (fully kernel-checked) and `pure a ≡ [a]`.
    #[test]
    fn test_list_insts_register_and_pure_reduces() {
        let mut env = Environment::new();
        env.init_eq().expect("init_eq");
        env.init_nat().expect("init_nat");
        env.init_monad_list_insts()
            .expect("Pure/Bind List instances must register (fully kernel-checked)");
        let tc = TypeChecker::new(&env);

        let inst = Expr::const_(Name::from_string("instPureList"), vec![Level::zero()]);
        let head = Expr::proj(Name::from_string("Pure"), 0, inst);
        let pure_3 = Expr::apps(head, [nat(), Expr::nat_lit(3)]);
        let singleton = Expr::apps(
            Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
            [
                nat(),
                Expr::nat_lit(3),
                Expr::apps(
                    Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
                    [nat()],
                ),
            ],
        );
        assert!(
            tc.is_def_eq(&pure_3, &singleton),
            "Pure List instance must reduce pure a to [a]"
        );
    }

    // ── B22: Id identity-monad instances ──────────────────────────────────

    fn env_with_id_insts() -> Environment {
        let mut env = Environment::new();
        env.init_eq().expect("init_eq");
        env.init_nat().expect("init_nat");
        env.init_monad_id_insts()
            .expect("Pure/Bind classes + Id instances must register (fully kernel-checked)");
        env
    }

    /// `(Proj Pure 0 instPureId) Nat v` — the shape the materialization pass
    /// emits for `pure v` over `Id`.
    fn id_pure_app(v: Expr) -> Expr {
        let inst = Expr::const_(Name::from_string("instPureId"), vec![Level::zero()]);
        let head = Expr::proj(Name::from_string("Pure"), 0, inst);
        Expr::apps(head, [nat(), v])
    }

    /// `(Proj Bind 0 instBindId) Nat Nat ma f`.
    fn id_bind_app(ma: Expr, f: Expr) -> Expr {
        let inst = Expr::const_(Name::from_string("instBindId"), vec![Level::zero()]);
        let head = Expr::proj(Name::from_string("Bind"), 0, inst);
        Expr::apps(head, [nat(), nat(), ma, f])
    }

    /// `Id.run.{0} Nat x`.
    fn id_run(x: Expr) -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Id.run"), vec![Level::zero()]),
            [nat(), x],
        )
    }

    /// B22 kernel-level pin: `Id.run (pure 5) ≡ 5`. `pure 5` is the
    /// instance-projected `(Proj Pure 0 instPureId) Nat 5` (identity body →
    /// `5`); `Id.run` is a reducible identity def — the whole term reduces to
    /// the ground literal through ORDINARY delta + proj-of-mk iota + beta.
    #[test]
    fn test_id_run_of_pure_reduces_to_ground_value() {
        let env = env_with_id_insts();
        let tc = TypeChecker::new(&env);

        let term = id_run(id_pure_app(Expr::nat_lit(5)));
        assert!(
            tc.is_def_eq(&term, &Expr::nat_lit(5)),
            "Id.run (pure 5) must reduce to 5"
        );
    }

    /// `Id.run (bind (pure 3) (fun x => pure (x))) ≡ 3` — the identity monad's
    /// left-identity through the instance-projected bind (`bind ma f ≡ f ma`).
    #[test]
    fn test_id_bind_pure_chain_reduces() {
        let env = env_with_id_insts();
        let tc = TypeChecker::new(&env);

        let k = Expr::lam(
            crate::BinderInfo::Default,
            nat(),
            id_pure_app(Expr::bvar(0)),
        );
        let chain = id_run(id_bind_app(id_pure_app(Expr::nat_lit(3)), k));
        assert!(
            tc.is_def_eq(&chain, &Expr::nat_lit(3)),
            "Id.run (bind (pure 3) pure) must reduce to 3"
        );
    }

    /// `Id α ≡ α`: the reducible `Id` alias unfolds so `Id Nat` and `Nat` are
    /// def-eq (the reduction every Id value pin depends on).
    #[test]
    fn test_id_alias_reduces_to_type_arg() {
        let env = env_with_id_insts();
        let tc = TypeChecker::new(&env);

        let id_nat = Expr::app(
            Expr::const_(Name::from_string("Id"), vec![Level::zero()]),
            nat(),
        );
        assert!(
            tc.is_def_eq(&id_nat, &nat()),
            "Id Nat must be def-eq to Nat (reducible identity alias)"
        );
    }

    /// ADVERSARIAL: the Id reductions must not over-equate — `Id.run (pure 5)`
    /// must NOT be def-eq to `6`. (The wrong pin `Id.run (pure 5) = 6 := rfl`
    /// stays rejected; B22 adds reduction, not unsoundness.)
    #[test]
    fn test_id_run_of_pure_rejects_wrong_value() {
        let env = env_with_id_insts();
        let tc = TypeChecker::new(&env);

        let term = id_run(id_pure_app(Expr::nat_lit(5)));
        assert!(
            !tc.is_def_eq(&term, &Expr::nat_lit(6)),
            "Id.run (pure 5) must stay non-def-eq to 6"
        );
    }
}
