// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The `Seq` / `SeqLeft` / `SeqRight` type classes (Brick P1 — unregistered
//! prelude heads).
//!
//! Registers the Lean 4 core applicative-sequencing classes as fully
//! kernel-checked single-constructor structures (no axioms), their
//! projections, and `Option` instances with real bodies:
//!
//! ```text
//! class Seq (f : Type u → Type v) : Type (max (u+1) v) where
//!   seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
//! class SeqLeft (f : Type u → Type v) : Type (max (u+1) v) where
//!   seqLeft : {α β : Type u} → f α → (Unit → f β) → f α
//! class SeqRight (f : Type u → Type v) : Type (max (u+1) v) where
//!   seqRight : {α β : Type u} → f α → (Unit → f β) → f β
//! ```
//!
//! Lean sources (toolchain `v4.30.0-rc2`): `Init/Prelude.lean:3773` (`Seq`),
//! `:3793` (`SeqLeft`), `:3815` (`SeqRight`). Note the `Unit → f _` thunk on
//! the second explicit parameter — exactly Lean's laziness shape (the parser
//! thunk-insertion itself is Brick 3, out of scope here).
//!
//! Without these heads, `<*>`/`<*`/`*>` (audit rows a04–a06 in
//! `docs/plans/ELAB_ARMS_AUDIT_2026-07-08.md`) resolved their `Seq*.seq*`
//! heads via auto-implicit and failed `TooManyArguments { Sort(u) }`.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Which of the three sequencing classes is being built.
#[derive(Clone, Copy)]
enum SeqShape {
    /// `seq : f (α → β) → (Unit → f α) → f β`
    Seq,
    /// `seqLeft : f α → (Unit → f β) → f α`
    SeqLeft,
    /// `seqRight : f α → (Unit → f β) → f β`
    SeqRight,
}

impl SeqShape {
    fn class_name(self) -> &'static str {
        match self {
            SeqShape::Seq => "Seq",
            SeqShape::SeqLeft => "SeqLeft",
            SeqShape::SeqRight => "SeqRight",
        }
    }

    fn field_name(self) -> &'static str {
        match self {
            SeqShape::Seq => "seq",
            SeqShape::SeqLeft => "seqLeft",
            SeqShape::SeqRight => "seqRight",
        }
    }

    /// `(first explicit arg type, thunked inner type, result type)` given the
    /// class carrier `f` and the two type binders `α`, `β`.
    fn arg_types(self, f: &Expr, alpha: &Expr, beta: &Expr) -> (Expr, Expr, Expr) {
        let f_alpha = Expr::app(f.clone(), alpha.clone());
        let f_beta = Expr::app(f.clone(), beta.clone());
        match self {
            SeqShape::Seq => {
                let alpha_to_beta = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
                let f_fun = Expr::app(f.clone(), alpha_to_beta);
                (f_fun, f_alpha, f_beta)
            }
            SeqShape::SeqLeft => (f_alpha.clone(), f_beta, f_alpha),
            SeqShape::SeqRight => (f_alpha, f_beta.clone(), f_beta),
        }
    }
}

/// The field type `{α β : Type u} → <first> → (Unit → <inner>) → <result>`.
fn seq_field_ty(parent: &EnvDeclBuilder, type_u: &Expr, f: &Expr, shape: SeqShape) -> Expr {
    let unit_ty = Expr::const_(Name::from_string("Unit"), vec![]);
    let mut c = EnvDeclBuilder::child_of(parent);
    let (alpha_id, alpha) = c.fresh_local(type_u.clone());
    let (beta_id, beta) = c.fresh_local(type_u.clone());
    let (first_ty, inner_ty, result_ty) = shape.arg_types(f, &alpha, &beta);
    let (x_id, _x) = c.fresh_local(first_ty.clone());
    let thunk_ty = Expr::pi(BinderInfo::Default, unit_ty, inner_ty);
    let (y_id, _y) = c.fresh_local(thunk_ty.clone());
    let r = result_ty;
    let r = c.mk_pi(y_id, BinderInfo::Default, thunk_ty, r);
    let r = c.mk_pi(x_id, BinderInfo::Default, first_ty, r);
    let r = c.mk_pi(beta_id, BinderInfo::Implicit, type_u.clone(), r);
    let r = c.mk_pi(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
    c.finish_child(r)
}

impl Environment {
    /// Register the `Seq`, `SeqLeft`, `SeqRight` classes and their
    /// projections, all as fully-checked declarations.
    ///
    /// Lean fidelity: `Init/Prelude.lean:3773/3793/3815` — one-field classes
    /// over `(f : Type u → Type v)` at `Type (max (u+1) v)` with the
    /// `Unit → f _` thunk on the second explicit parameter.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.seq_classes_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_seq_classes(&mut self) -> Result<(), EnvError> {
        if self.seq_classes_init {
            return Ok(());
        }

        // The thunk parameter references `Unit` (Lean's `Unit → f α`).
        self.init_unit()?;

        for shape in [SeqShape::Seq, SeqShape::SeqLeft, SeqShape::SeqRight] {
            self.init_seq_class_with_shape(shape)?;
        }

        self.seq_classes_init = true;
        Ok(())
    }

    fn init_seq_class_with_shape(&mut self, shape: SeqShape) -> Result<(), EnvError> {
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
        let m_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_v.clone());
        // Type (max (u+1) v)
        let result_sort = Expr::sort(Level::succ(Level::max(
            Level::succ(u_level.clone()),
            v_level.clone(),
        )));
        let class_const = Expr::const_(class_name.clone(), vec![u_level, v_level]);

        // <Class>.mk : {f : Type u → Type v} → (field : …) → <Class> f
        let ctor_type = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(m_type.clone());
            let field_ty = seq_field_ty(&b, &type_u, &f, shape);
            let (field_id, _) = b.fresh_local(field_ty.clone());
            let class_ty = Expr::app(class_const.clone(), f.clone());
            let r = b.mk_pi(field_id, BinderInfo::Default, field_ty, class_ty);
            let r = b.mk_pi(f_id, BinderInfo::Implicit, m_type.clone(), r);
            b.finish(r)
        };

        self.add_inductive(InductiveDecl {
            level_params: vec![u.clone(), v.clone()],
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
            name: class_name.clone(),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // Projection: <Class>.<field> : {f} → [self : <Class> f] → <field type>
        let proj_type = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(m_type.clone());
            let class_ty = Expr::app(class_const.clone(), f.clone());
            let (inst_id, _) = b.fresh_local(class_ty.clone());
            let field_ty = seq_field_ty(&b, &type_u, &f, shape);
            let r = b.mk_pi(inst_id, BinderInfo::InstImplicit, class_ty, field_ty);
            let r = b.mk_pi(f_id, BinderInfo::Implicit, m_type.clone(), r);
            b.finish(r)
        };
        let proj_value = {
            let mut b = EnvDeclBuilder::new();
            let (f_id, f) = b.fresh_local(m_type.clone());
            let class_ty = Expr::app(class_const.clone(), f.clone());
            let (inst_id, inst) = b.fresh_local(class_ty.clone());
            let body = Expr::proj(class_name.clone(), 0, inst);
            let r = b.mk_lam(inst_id, BinderInfo::InstImplicit, class_ty, body);
            let r = b.mk_lam(f_id, BinderInfo::Implicit, m_type.clone(), r);
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

    /// Register `Seq Option` / `SeqLeft Option` / `SeqRight Option` instances
    /// with real `Option.bind`/`Option.map` bodies (no axioms, no sorry):
    ///
    /// ```text
    /// instSeqOption      : seq g x      := g.bind fun h => (x ()).map h
    /// instSeqLeftOption  : seqLeft a b  := a.bind fun x => (b ()).map fun _ => x
    /// instSeqRightOption : seqRight a b := a.bind fun _ => b ()
    /// ```
    ///
    /// Lean fidelity note: upstream Lean derives these through
    /// `Monad Option → Applicative → Seq/SeqLeft/SeqRight` (there is no direct
    /// upstream `instSeqOption`); Clean's prelude has no `Applicative`
    /// hierarchy, so the derived behaviors (definitionally equal on `Option`)
    /// are registered directly under Clean-native names.
    ///
    /// IMPORT MODE (`suppress_lossy_structure_stubs`): withheld — the genuine
    /// olean closure carries Lean's own `Monad Option`-derived instance chain,
    /// and these Clean-native names would only pollute the import prelude.
    /// The default proof-execution lane is unchanged.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.seq_option_insts_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub(crate) fn init_seq_option_insts(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs {
            return Ok(());
        }
        if self.seq_option_insts_init {
            return Ok(());
        }

        self.init_seq_classes()?;
        self.init_option()?;
        self.init_option_ops()?; // Option.map / Option.bind

        for shape in [SeqShape::Seq, SeqShape::SeqLeft, SeqShape::SeqRight] {
            self.add_seq_option_instance(shape)?;
        }

        self.seq_option_insts_init = true;
        Ok(())
    }

    fn add_seq_option_instance(&mut self, shape: SeqShape) -> Result<(), EnvError> {
        let inst_name = format!("inst{}Option", shape.class_name());
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let uu = vec![u_level.clone(), u_level.clone()];
        let option_const = Expr::const_(Name::from_string("Option"), vec![u_level.clone()]);
        let option_map = Expr::const_(Name::from_string("Option.map"), uu.clone());
        let option_bind = Expr::const_(Name::from_string("Option.bind"), uu.clone());
        let class_const = Expr::const_(Name::from_string(shape.class_name()), uu.clone());
        let class_mk = Expr::const_(Name::from_string(&format!("{}.mk", shape.class_name())), uu);
        let unit_ty = Expr::const_(Name::from_string("Unit"), vec![]);
        let unit_unit = Expr::const_(Name::from_string("Unit.unit"), vec![]);

        let inst_type = Expr::app(class_const, option_const.clone());

        // field value: fun {α β : Type u} (x : <first>) (y : Unit → <inner>) => <body>
        let field_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(type_u.clone());
            let (beta_id, beta) = b.fresh_local(type_u.clone());
            let (first_ty, inner_ty, _result_ty) = shape.arg_types(&option_const, &alpha, &beta);
            let (x_id, x) = b.fresh_local(first_ty.clone());
            let thunk_ty = Expr::pi(BinderInfo::Default, unit_ty.clone(), inner_ty.clone());
            let (y_id, y) = b.fresh_local(thunk_ty.clone());
            let forced = Expr::app(y, unit_unit.clone()); // y () : <inner>

            let body = match shape {
                // Option.bind (α→β) β x (fun h => Option.map α β h (y ()))
                SeqShape::Seq => {
                    let alpha_to_beta = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
                    let k = {
                        let mut c = EnvDeclBuilder::child_of(&b);
                        let (h_id, h) = c.fresh_local(alpha_to_beta.clone());
                        let mapped = Expr::apps(
                            option_map.clone(),
                            [alpha.clone(), beta.clone(), h, forced.clone()],
                        );
                        let r = c.mk_lam(h_id, BinderInfo::Default, alpha_to_beta.clone(), mapped);
                        c.finish_child(r)
                    };
                    Expr::apps(option_bind.clone(), [alpha_to_beta, beta.clone(), x, k])
                }
                // Option.bind α α a (fun v => Option.map β α (fun _ => v) (y ()))
                SeqShape::SeqLeft => {
                    let k = {
                        let mut c = EnvDeclBuilder::child_of(&b);
                        let (v_id, v) = c.fresh_local(alpha.clone());
                        let const_fun = {
                            let mut d = EnvDeclBuilder::child_of(&c);
                            let (w_id, _w) = d.fresh_local(beta.clone());
                            let r = d.mk_lam(w_id, BinderInfo::Default, beta.clone(), v.clone());
                            d.finish_child(r)
                        };
                        let mapped = Expr::apps(
                            option_map.clone(),
                            [beta.clone(), alpha.clone(), const_fun, forced.clone()],
                        );
                        let r = c.mk_lam(v_id, BinderInfo::Default, alpha.clone(), mapped);
                        c.finish_child(r)
                    };
                    Expr::apps(option_bind.clone(), [alpha.clone(), alpha.clone(), x, k])
                }
                // Option.bind α β a (fun _ => y ())
                SeqShape::SeqRight => {
                    let k = {
                        let mut c = EnvDeclBuilder::child_of(&b);
                        let (v_id, _v) = c.fresh_local(alpha.clone());
                        let r = c.mk_lam(v_id, BinderInfo::Default, alpha.clone(), forced.clone());
                        c.finish_child(r)
                    };
                    Expr::apps(option_bind.clone(), [alpha.clone(), beta.clone(), x, k])
                }
            };

            let r = b.mk_lam(y_id, BinderInfo::Default, thunk_ty, body);
            let r = b.mk_lam(x_id, BinderInfo::Default, first_ty, r);
            let r = b.mk_lam(beta_id, BinderInfo::Implicit, type_u.clone(), r);
            let r = b.mk_lam(alpha_id, BinderInfo::Implicit, type_u.clone(), r);
            b.finish(r)
        };

        let inst_value = Expr::apps(class_mk, [option_const, field_value]);

        self.add_decl(Declaration::Definition {
            name: Name::from_string(&inst_name),
            level_params: vec![u],
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

        Ok(())
    }
}
