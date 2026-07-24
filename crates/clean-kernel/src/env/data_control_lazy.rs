// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lazy heterogeneous control classes and `Bind` combinators (Brick P1 —
//! unregistered prelude heads).
//!
//! Registers the Lean 4 core classes behind `>>` / `<|>` as fully
//! kernel-checked single-constructor structures (no axioms) plus their
//! projections, and the plain `Bind` combinator defs behind `=<<` / `>=>` /
//! `<=<`:
//!
//! ```text
//! class HAndThen (α : Type u) (β : Type v) (γ : outParam (Type w)) where
//!   hAndThen : α → (Unit → β) → γ
//! class HOrElse (α : Type u) (β : Type v) (γ : outParam (Type w)) where
//!   hOrElse : α → (Unit → β) → γ
//! ```
//!
//! Lean sources (toolchain `v4.30.0-rc2`): `Init/Prelude.lean:1449`
//! (`HOrElse`), `:1461` (`HAndThen`) — note the `Unit → β` thunk on the
//! second explicit parameter; `Init/Control/Basic.lean:416/421/426`
//! (`Bind.kleisliRight` / `Bind.kleisliLeft` / `Bind.bindLeft`).
//!
//! Without these heads, `>>`/`<|>`/`=<<`/`>=>`/`<=<` (audit rows
//! a01/a07/a09–a11 in `docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md`) resolved
//! via auto-implicit and failed `TooManyArguments { Sort(u) }`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// `α → (Unit → β) → γ` — the thunked hetero field type shared by
/// `HAndThen.hAndThen` and `HOrElse.hOrElse`.
fn thunked_hetero_field_ty(
    parent: &EnvDeclBuilder,
    alpha: &Expr,
    beta: &Expr,
    gamma: &Expr,
) -> Expr {
    let unit_ty = Expr::const_(Name::from_string("Unit"), vec![]);
    let mut c = EnvDeclBuilder::child_of(parent);
    let (lhs_id, _lhs) = c.fresh_local(alpha.clone());
    let thunk_ty = Expr::pi(BinderInfo::Default, unit_ty, beta.clone());
    let (rhs_id, _rhs) = c.fresh_local(thunk_ty.clone());
    let r = gamma.clone();
    let r = c.mk_pi(rhs_id, BinderInfo::Default, thunk_ty, r);
    let r = c.mk_pi(lhs_id, BinderInfo::Default, alpha.clone(), r);
    c.finish_child(r)
}

impl Environment {
    /// Register the `HAndThen` / `HOrElse` classes and their
    /// `hAndThen` / `hOrElse` projections, all as fully-checked declarations.
    ///
    /// Lean fidelity: `Init/Prelude.lean:1461` / `:1449` — three-parameter
    /// heterogeneous classes with `γ` an `outParam` and the second explicit
    /// argument thunked as `Unit → β` (the laziness Lean routes through
    /// `binop_lazy%`; the parser-side thunk insertion is Brick 3).
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.handthen_horelse_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_handthen_horelse(&mut self) -> Result<(), EnvError> {
        if self.handthen_horelse_init {
            return Ok(());
        }

        // The thunk parameter references `Unit` (Lean's `Unit → β`).
        self.init_unit()?;

        for (class_name, field_name) in [("HAndThen", "hAndThen"), ("HOrElse", "hOrElse")] {
            self.init_thunked_hetero_class(class_name, field_name)?;
        }

        self.handthen_horelse_init = true;
        Ok(())
    }

    fn init_thunked_hetero_class(
        &mut self,
        class_name: &str,
        field_name: &str,
    ) -> Result<(), EnvError> {
        let class = Name::from_string(class_name);
        let ctor_name = Name::from_string(&format!("{class_name}.mk"));
        let proj_name = Name::from_string(&format!("{class_name}.{field_name}"));

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let w = Name::from_string("w");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let w_level = Level::param(w.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let type_v = Expr::sort(Level::succ(v_level.clone()));
        let type_w = Expr::sort(Level::succ(w_level.clone()));
        // Type (max u v w) — the class-former result universe (the single
        // field `α → (Unit → β) → γ` lives at `max (u+1) (v+1) (w+1)`).
        let result_sort = Expr::sort(Level::succ(Level::max(
            u_level.clone(),
            Level::max(v_level.clone(), w_level.clone()),
        )));
        let class_const = Expr::const_(class.clone(), vec![u_level, v_level, w_level]);

        // <Class>.mk : {α β γ} → (field : α → (Unit → β) → γ) → <Class> α β γ
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let (gamma_id, gamma) = b.fresh_local(type_w.clone());
            let field_ty = thunked_hetero_field_ty(&b, &alpha, &beta, &gamma);
            let (field_id, _) = b.fresh_local(field_ty.clone());
            let class_ty = Expr::apps(
                class_const.clone(),
                [alpha.clone(), beta.clone(), gamma.clone()],
            );
            let r = b.mk_pi(field_id, BinderInfo::Default, field_ty, class_ty);
            let r = b.mk_pi(gamma_id, BinderInfo::Implicit, type_w.clone(), r);
            let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        self.add_inductive(InductiveDecl {
            level_params: vec![u.clone(), v.clone(), w.clone()],
            num_params: 3,
            types: vec![InductiveType {
                name: class.clone(),
                type_: Expr::pi(
                    BinderInfo::Default,
                    type_u.clone(),
                    Expr::pi(
                        BinderInfo::Default,
                        type_v.clone(),
                        Expr::pi(BinderInfo::Default, type_w.clone(), result_sort),
                    ),
                ),
                constructors: vec![Constructor {
                    name: ctor_name,
                    type_: ctor_type,
                }],
            }],
        })?;

        self.register_structure_fields(class.clone(), vec![Name::from_string(field_name)])?;

        self.register_class(KernelClassInfo {
            name: class.clone(),
            num_params: 3,
            // γ is the outParam (Init/Prelude.lean:1449/1461), like HAdd.
            out_params: vec![2],
            semi_out_params: vec![],
        });

        // Projection: <Class>.<field> : {α β γ} → [self] → α → (Unit → β) → γ
        let proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let (gamma_id, gamma) = b.fresh_local(type_w.clone());
            let class_ty = Expr::apps(
                class_const.clone(),
                [alpha.clone(), beta.clone(), gamma.clone()],
            );
            let (inst_id, _) = b.fresh_local(class_ty.clone());
            let field_ty = thunked_hetero_field_ty(&b, &alpha, &beta, &gamma);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, class_ty, field_ty);
            let r = b.mk_pi(gamma_id, BinderInfo::Implicit, type_w.clone(), r);
            let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        let proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_v.clone());
            let (gamma_id, gamma) = b.fresh_local(type_w.clone());
            let class_ty = Expr::apps(
                class_const.clone(),
                [alpha.clone(), beta.clone(), gamma.clone()],
            );
            let (inst_id, inst) = b.fresh_local(class_ty.clone());
            let body = Expr::proj(class.clone(), 0, inst);
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, class_ty, body);
            let r = b.mk_lam(gamma_id, BinderInfo::Implicit, type_w.clone(), r);
            let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_v.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };
        self.add_decl(Declaration::Definition {
            name: proj_name,
            level_params: vec![u, v, w],
            type_: proj_type,
            value: proj_value,
            is_reducible: true,
        })?;

        Ok(())
    }

    /// Register the `Option` instances behind `>>` / `<|>`, with real
    /// `Option.bind` / `Option.rec` bodies (fully kernel-checked Definitions —
    /// no axioms, no sorry, no Opaque):
    ///
    /// ```text
    /// instHAndThenOption : {α β : Type u} → HAndThen (Option α) (Option β) (Option β)
    ///   hAndThen a b := Option.bind a (fun _ => b ())
    /// instHOrElseOption  : {α : Type u} → HOrElse (Option α) (Option α) (Option α)
    ///   hOrElse a b := Option.rec (b ()) (fun x => some x) a
    /// ```
    ///
    /// Lean fidelity note: upstream reaches these through instance chains —
    /// `[Bind m] : HAndThen (m α) (m β) (m β) := ⟨fun a b => a >>= fun _ =>
    /// b ()⟩` (`Init/Control/Basic.lean`) and `instHOrElse [OrElse α] :
    /// HOrElse α α α` over `instOrElseOption := ⟨Option.orElse⟩`
    /// (`Init/Prelude.lean`; `Option.orElse` is `some a, _ => some a` /
    /// `none, b => b ()`). Clean's prelude has no `AndThen`/`OrElse`
    /// hierarchy and its `Bind.bind` is a stub AXIOM (data_monad.rs), so the
    /// derived behaviors — definitionally equal on `Option`, and spelled
    /// against the real `Option.bind`/`Option.rec` so the axiom closure stays
    /// EMPTY — are registered directly under Clean-native names, the same
    /// policy as `instSeqOption` (data_seq_classes.rs).
    ///
    /// IMPORT MODE (`suppress_lossy_structure_stubs`): withheld — the genuine
    /// olean closure carries Lean's own `AndThen`/`OrElse`/`Bind`-derived
    /// instance chain, and these Clean-native names would only pollute the
    /// import prelude (same policy as `instSeq*Option`). The default
    /// proof-execution lane is unchanged.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.handthen_horelse_option_insts_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_handthen_horelse_option_insts(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.handthen_horelse_option_insts_init {
            return Ok(());
        }

        self.init_handthen_horelse()?;
        self.init_option()?;
        self.init_option_ops()?; // Option.bind

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let uuu = vec![u_level.clone(), u_level.clone(), u_level.clone()];
        let option_const = Expr::const_(Name::from_string("Option"), vec![u_level.clone()]);
        // Option.bind.{u, v} instantiated at [u, u] (data_seq_classes policy).
        let option_bind = Expr::const_(
            Name::from_string("Option.bind"),
            vec![u_level.clone(), u_level.clone()],
        );
        let option_some = Expr::const_(Name::from_string("Option.some"), vec![u_level.clone()]);
        // Eliminate `Option α` (Type u) into `Option α` (Type u = Sort (u+1)):
        // Option.rec universes are [motive-elim, type] = [succ u, u].
        let option_rec = Expr::const_(
            Name::from_string("Option.rec"),
            vec![Level::succ(u_level.clone()), u_level.clone()],
        );
        let unit_ty = Expr::const_(Name::from_string("Unit"), vec![]);
        let unit_unit = Expr::const_(Name::from_string("Unit.unit"), vec![]);

        // instHAndThenOption : {α β : Type u} → HAndThen (Option α) (Option β) (Option β)
        //   := fun {α β} => HAndThen.mk _ _ _
        //        (fun (a : Option α) (b : Unit → Option β) =>
        //           Option.bind α β a (fun _ : α => b ()))
        {
            let class_const = Expr::const_(Name::from_string("HAndThen"), uuu.clone());
            let class_mk = Expr::const_(Name::from_string("HAndThen.mk"), uuu.clone());

            let inst_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (beta_id, beta) = b.fresh_local(type_u.clone());
                let opt_alpha = Expr::app(option_const.clone(), alpha);
                let opt_beta = Expr::app(option_const.clone(), beta);
                let r = Expr::apps(class_const, [opt_alpha, opt_beta.clone(), opt_beta]);
                let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), r);
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            let inst_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (beta_id, beta) = b.fresh_local(type_u.clone());
                let opt_alpha = Expr::app(option_const.clone(), alpha.clone());
                let opt_beta = Expr::app(option_const.clone(), beta.clone());
                let thunk_ty = Expr::pi(BinderInfo::Default, unit_ty.clone(), opt_beta.clone());
                let field = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, a) = c.fresh_local(opt_alpha.clone());
                    let (bthunk_id, bthunk) = c.fresh_local(thunk_ty.clone());
                    // fun _ : α => b ()
                    let k = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (v_id, _v) = d.fresh_local(alpha.clone());
                        let forced = Expr::app(bthunk, unit_unit.clone());
                        let r = d.mk_lam(v_id, BinderInfo::Default, alpha.clone(), forced);
                        d.finish_child(r)
                    };
                    let body = Expr::apps(option_bind.clone(), [alpha.clone(), beta.clone(), a, k]);
                    let r = c.mk_lam(bthunk_id, BinderInfo::Default, thunk_ty, body);
                    let r = c.mk_lam(a_id, BinderInfo::Default, opt_alpha.clone(), r);
                    c.finish_child(r)
                };
                let body = Expr::apps(class_mk, [opt_alpha, opt_beta.clone(), opt_beta, field]);
                let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_u.clone(), body);
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("instHAndThenOption"),
                level_params: vec![u.clone()],
                type_: inst_type,
                value: inst_value,
                is_reducible: true,
            })?;
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instHAndThenOption"),
                class_name: Name::from_string("HAndThen"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        // instHOrElseOption : {α : Type u} → HOrElse (Option α) (Option α) (Option α)
        //   := fun {α} => HOrElse.mk _ _ _
        //        (fun (a : Option α) (b : Unit → Option α) =>
        //           Option.rec (motive := fun _ => Option α)
        //             (b ()) (fun x => Option.some α x) a)
        {
            let class_const = Expr::const_(Name::from_string("HOrElse"), uuu.clone());
            let class_mk = Expr::const_(Name::from_string("HOrElse.mk"), uuu);

            let inst_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let opt_alpha = Expr::app(option_const.clone(), alpha);
                let r = Expr::apps(
                    class_const,
                    [opt_alpha.clone(), opt_alpha.clone(), opt_alpha],
                );
                let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                b.finish(r)
            };

            let inst_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let opt_alpha = Expr::app(option_const.clone(), alpha.clone());
                let thunk_ty = Expr::pi(BinderInfo::Default, unit_ty.clone(), opt_alpha.clone());
                let field = {
                    let mut c = EnvDeclBuilder::child_of(&b);
                    let (a_id, a) = c.fresh_local(opt_alpha.clone());
                    let (bthunk_id, bthunk) = c.fresh_local(thunk_ty.clone());
                    // motive: fun _ : Option α => Option α
                    let motive = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (w_id, _w) = d.fresh_local(opt_alpha.clone());
                        let r = d.mk_lam(
                            w_id,
                            BinderInfo::Default,
                            opt_alpha.clone(),
                            opt_alpha.clone(),
                        );
                        d.finish_child(r)
                    };
                    let none_case = Expr::app(bthunk, unit_unit.clone()); // b ()
                                                                          // some case: fun x : α => Option.some α x
                    let some_case = {
                        let mut d = EnvDeclBuilder::child_of(&c);
                        let (x_id, x) = d.fresh_local(alpha.clone());
                        let r = Expr::apps(option_some.clone(), [alpha.clone(), x]);
                        let r = d.mk_lam(x_id, BinderInfo::Default, alpha.clone(), r);
                        d.finish_child(r)
                    };
                    let body = Expr::apps(
                        option_rec.clone(),
                        [alpha.clone(), motive, none_case, some_case, a],
                    );
                    let r = c.mk_lam(bthunk_id, BinderInfo::Default, thunk_ty, body);
                    let r = c.mk_lam(a_id, BinderInfo::Default, opt_alpha.clone(), r);
                    c.finish_child(r)
                };
                let body = Expr::apps(
                    class_mk,
                    [opt_alpha.clone(), opt_alpha.clone(), opt_alpha, field],
                );
                let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), body);
                b.finish(r)
            };

            self.add_decl(Declaration::Definition {
                name: Name::from_string("instHOrElseOption"),
                level_params: vec![u],
                type_: inst_type,
                value: inst_value,
                is_reducible: true,
            })?;
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string("instHOrElseOption"),
                class_name: Name::from_string("HOrElse"),
                priority: DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }

        self.handthen_horelse_option_insts_init = true;
        Ok(())
    }

    /// Register the plain `Bind` combinator defs behind `=<<` / `>=>` / `<=<`
    /// as fully-checked Definitions over the EXISTING `Bind.bind` constant:
    ///
    /// ```text
    /// Bind.bindLeft     : {m} → {α β : Type u}   → (α → m β) → m α → m β
    /// Bind.kleisliRight : {m} → {α β γ : Type u} → (α → m β) → (β → m γ) → α → m γ
    /// Bind.kleisliLeft  : {m} → {α β γ : Type u} → (β → m γ) → (α → m β) → α → m γ
    /// ```
    ///
    /// Lean fidelity: `Init/Control/Basic.lean:426/416/421` — same names,
    /// explicit-argument arity/order, and bodies (`ma >>= f` / `f₁ a >>= f₂`).
    /// KNOWN DEVIATIONS (both stub-shaped, both to be re-derived when `Bind`
    /// becomes a real structure — tracked with the `Bind.bind` stub note in
    /// data_monad.rs):
    /// 1. upstream carries a `[Bind m]` instance binder; Clean's prelude
    ///    `Bind.bind` stub (`init_monad_classes`) has no `Bind` class and no
    ///    such binder, so these defs mirror the stub's implicit telescope
    ///    (`{m} {α β [γ]}`);
    /// 2. upstream's kleisli source type `α` lives in its OWN universe
    ///    (toolchain oracle: `Bind.kleisliLeft : {α : Type u_1} → {m : Type
    ///    u_2 → Type u_3} → {β γ : Type u_2} → …`); the stub-shaped versions
    ///    pin `α : Type u` alongside `β γ` (the `Bind.bind` stub's single
    ///    value universe).
    ///
    /// IMPORT MODE (`suppress_lossy_structure_stubs`): withheld with the whole
    /// Monad/Bind/Pure cluster (see `init_monad_classes` gating in
    /// `init_prelude_extended`) — the stub-shaped telescopes would shadow the
    /// genuine `[Bind m]`-carrying olean twins, and their `Bind.bind`
    /// dependency is itself suppressed. The default lane is unchanged.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.bind_combinators_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_bind_combinators(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.bind_combinators_init {
            return Ok(());
        }

        // Bind.bind (the stub these are spelled against).
        self.init_monad_classes()?;

        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let type_v = Expr::sort(Level::succ(v_level.clone()));
        let m_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone());
        let bind_const = Expr::const_(
            Name::from_string("Bind.bind"),
            vec![u_level.clone(), v_level.clone()],
        );

        // Bind.bindLeft : {m} → {α β} → (α → m β) → m α → m β := fun f ma => Bind.bind ma f
        {
            let build = |as_value: bool| {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(m_type.clone());
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (beta_id, beta) = b.fresh_local(type_u.clone());
                let m_alpha = Expr::app(m.clone(), alpha.clone());
                let m_beta = Expr::app(m.clone(), beta.clone());
                let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), m_beta.clone());
                let (f_id, f) = b.fresh_local(f_ty.clone());
                let (ma_id, ma) = b.fresh_local(m_alpha.clone());
                if as_value {
                    // Bind.bind m α β ma f
                    let body = Expr::apps(
                        bind_const.clone(),
                        [m.clone(), alpha.clone(), beta.clone(), ma, f],
                    );
                    let r = b.mk_lam(ma_id, BinderInfo::Default, m_alpha, body);
                    let r = b.mk_lam(f_id, BinderInfo::Default, f_ty, r);
                    let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_u.clone(), r);
                    let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                    let r = b.mk_lam(m_id, BinderInfo::Implicit, m_type.clone(), r);
                    b.finish(r)
                } else {
                    let r = m_beta.clone();
                    let r = b.mk_pi(ma_id, BinderInfo::Default, m_alpha, r);
                    let r = b.mk_pi(f_id, BinderInfo::Default, f_ty, r);
                    let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), r);
                    let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                    let r = b.mk_pi(m_id, BinderInfo::Implicit, m_type.clone(), r);
                    b.finish(r)
                }
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string("Bind.bindLeft"),
                level_params: vec![u.clone(), v.clone()],
                type_: build(false),
                value: build(true),
                is_reducible: true,
            })?;
        }

        // Bind.kleisliRight : (f₁ : α → m β) → (f₂ : β → m γ) → α → m γ
        // Bind.kleisliLeft  : (f₂ : β → m γ) → (f₁ : α → m β) → α → m γ
        // both := Bind.bind (f₁ a) f₂
        for (name, f1_first) in [("Bind.kleisliRight", true), ("Bind.kleisliLeft", false)] {
            let build = |as_value: bool| {
                let mut b = EnvDeclBuilder::new();
                let (m_id, m) = b.fresh_local(m_type.clone());
                let (alpha_id, alpha) = b.fresh_local(type_u.clone());
                let (beta_id, beta) = b.fresh_local(type_u.clone());
                let (gamma_id, gamma) = b.fresh_local(type_u.clone());
                let m_beta = Expr::app(m.clone(), beta.clone());
                let m_gamma = Expr::app(m.clone(), gamma.clone());
                let f1_ty = Expr::pi(BinderInfo::Default, alpha.clone(), m_beta.clone());
                let f2_ty = Expr::pi(BinderInfo::Default, beta.clone(), m_gamma.clone());
                // Bind the two function locals in the declared explicit order.
                let ((f1_id, f1), (f2_id, f2)) = if f1_first {
                    let f1 = b.fresh_local(f1_ty.clone());
                    let f2 = b.fresh_local(f2_ty.clone());
                    (f1, f2)
                } else {
                    let f2 = b.fresh_local(f2_ty.clone());
                    let f1 = b.fresh_local(f1_ty.clone());
                    (f1, f2)
                };
                let (a_id, a) = b.fresh_local(alpha.clone());
                if as_value {
                    // Bind.bind m β γ (f₁ a) f₂
                    let body = Expr::apps(
                        bind_const.clone(),
                        [m.clone(), beta.clone(), gamma.clone(), Expr::app(f1, a), f2],
                    );
                    let r = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
                    let r = if f1_first {
                        let r = b.mk_lam(f2_id, BinderInfo::Default, f2_ty, r);
                        b.mk_lam(f1_id, BinderInfo::Default, f1_ty, r)
                    } else {
                        let r = b.mk_lam(f1_id, BinderInfo::Default, f1_ty, r);
                        b.mk_lam(f2_id, BinderInfo::Default, f2_ty, r)
                    };
                    let r = b.mk_lam(gamma_id, BinderInfo::Implicit, type_u.clone(), r);
                    let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_u.clone(), r);
                    let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                    let r = b.mk_lam(m_id, BinderInfo::Implicit, m_type.clone(), r);
                    b.finish(r)
                } else {
                    let r = m_gamma.clone();
                    let r = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), r);
                    let r = if f1_first {
                        let r = b.mk_pi(f2_id, BinderInfo::Default, f2_ty, r);
                        b.mk_pi(f1_id, BinderInfo::Default, f1_ty, r)
                    } else {
                        let r = b.mk_pi(f1_id, BinderInfo::Default, f1_ty, r);
                        b.mk_pi(f2_id, BinderInfo::Default, f2_ty, r)
                    };
                    let r = b.mk_pi(gamma_id, BinderInfo::Implicit, type_u.clone(), r);
                    let r = b.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), r);
                    let r = b.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
                    let r = b.mk_pi(m_id, BinderInfo::Implicit, m_type.clone(), r);
                    b.finish(r)
                }
            };
            self.add_decl(Declaration::Definition {
                name: Name::from_string(name),
                level_params: vec![u.clone(), v.clone()],
                type_: build(false),
                value: build(true),
                is_reducible: true,
            })?;
        }

        self.bind_combinators_init = true;
        Ok(())
    }
}
