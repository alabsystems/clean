// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The Lean-faithful monad class hierarchy (2026-09-28, prelude soundness fix).
//!
//! # Why this replaced three axioms
//!
//! Until 2026-09-28 the default prelude registered
//!
//! ```text
//! axiom Pure.pure : {m : Type u → Type v} → {α : Type u} → α → m α
//! axiom Bind.bind : {m : Type u → Type v} → {α β : Type u} → m α → (α → m β) → m β
//! axiom Monad     : (Type u → Type v) → Type (max (u+1) v)
//! ```
//!
//! The first two are inhabited in NO model: `Pure.pure (fun _ => Empty) Nat 0`
//! is an `Empty`, and `Bind.bind` at the contravariant family
//! `fun X => X → Empty` produces one too, so `Empty.elim` proves `False` in
//! every default `clean check` environment
//! (`docs/issues/2026-09-28-prelude-pure-proves-false.md`, repros in
//! `tests_prelude_monad_consistency.rs`). Lean has no such axioms: `Pure` and
//! `Bind` are classes, and `Pure.pure` is a PROJECTION that needs an instance,
//! of which the empty family has none.
//!
//! # What this module registers (shapes read off pinned Lean v4.30.0-rc2)
//!
//! ```text
//! class Applicative (f : Type u → Type v)
//!     extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f
//! class Monad (m : Type u → Type v) : Type (max (u+1) v)
//!     extends Applicative m, Bind m
//! Applicative.mk {f} [toFunctor] [toPure] [toSeq] [toSeqLeft] [toSeqRight]
//! Monad.mk {m} [toApplicative] [toBind]
//! @Pure.pure : {f} → [self : Pure f] → {α} → α → f α          (projection)
//! @Bind.bind : {m} → [self : Bind m] → {α β} → m α → (α → m β) → m β
//! ```
//!
//! plus the parent projections `Applicative.to*` / `Monad.to*`, each an
//! INSTANCE (Lean registers a class's parent projections as instances, at the
//! default priority 1000 — read off the shipped `.olean` with
//! `getInstancePriority?`), and the core monad instances: `Id.instMonad`,
//! `instMonadOption`, `instMonadIO` (Clean-native: `IO` is an opaque type
//! here, not `EIO`) and, on the builtin `clean check` lane only,
//! `instMonadList` (Clean-native; Lean core has no `List` monad).
//!
//! Every instance is built by [`monad_mk_from`] from a `Pure` and a `Bind`
//! instance, with the remaining fields given Lean's `Monad` defaults
//! (`map f x := bind x (pure ∘ f)`, `seq f x := bind f fun y => y <$> x ()`,
//! …), beta-reduced. Nothing here is an axiom; every declaration is
//! kernel-checked by `add_decl` / `add_inductive`.
//!
//! IMPORT MODE (`suppress_lossy_structure_stubs`): withheld; `.olean`s carry Lean's.

use crate::env::monad_term::{cst, lparam, monad_kind, type_at, MonadInst, Tele};
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, LEAN_DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// The class result sort `Type (max (u+1) v)` shared by every class over a
/// monad `f : Type u → Type v`.
fn monad_class_sort(u: &Level, v: &Level) -> Expr {
    Expr::sort(Level::succ(Level::max(Level::succ(u.clone()), v.clone())))
}

/// Build `Monad.mk M (Applicative.mk M functor pureI seq seqLeft seqRight) bindI`
/// for a carrier `M : Type u → Type v` from a `Pure M` and a `Bind M`
/// instance, filling `map`/`mapConst`/`seq`/`seqLeft`/`seqRight` with Lean's
/// `Monad` defaults (`Init/Prelude.lean`, `class Monad`), beta-reduced.
///
/// `parent` is the telescope the result will be closed under (it may be an
/// empty root); every lambda built here is a child of it.
pub(crate) fn monad_mk_from(
    u: &Level,
    v: &Level,
    carrier: &Expr,
    pure_inst: &Expr,
    bind_inst: &Expr,
    parent: &Tele,
) -> Expr {
    let uv = [u.clone(), v.clone()];
    let ty_u = type_at(u);
    let m_at = |a: &Expr| Expr::app(carrier.clone(), a.clone());
    let pure = |a: &Expr, x: Expr| {
        Expr::apps(
            cst("Pure.pure", &uv),
            [carrier.clone(), pure_inst.clone(), a.clone(), x],
        )
    };
    let bind = |a: &Expr, b: &Expr, x: Expr, f: Expr| {
        Expr::apps(
            cst("Bind.bind", &uv),
            [
                carrier.clone(),
                bind_inst.clone(),
                a.clone(),
                b.clone(),
                x,
                f,
            ],
        )
    };
    let unit = cst("Unit", &[]);
    let unit_unit = cst("Unit.unit", &[]);

    // map := fun {α β} (f : α → β) (x : M α) => bind x (fun y => pure (f y))
    let map = {
        let mut t = Tele::child(parent);
        let a = t.imp(ty_u.clone());
        let b = t.imp(ty_u.clone());
        let f = t.arg(Expr::arrow(a.clone(), b.clone()));
        let x = t.arg(m_at(&a));
        let k = {
            let mut t2 = Tele::child(&t);
            let y = t2.arg(a.clone());
            t2.lam(pure(&b, Expr::app(f, y)))
        };
        t.lam(bind(&a, &b, x, k))
    };
    // mapConst := fun {α β} (a : α) (x : M β) => bind x (fun _ => pure a)
    let map_const = {
        let mut t = Tele::child(parent);
        let a = t.imp(ty_u.clone());
        let b = t.imp(ty_u.clone());
        let av = t.arg(a.clone());
        let x = t.arg(m_at(&b));
        let k = {
            let mut t2 = Tele::child(&t);
            let _ = t2.arg(b.clone());
            t2.lam(pure(&a, av))
        };
        t.lam(bind(&b, &a, x, k))
    };
    // seq := fun {α β} (mf : M (α → β)) (x : Unit → M α) =>
    //          bind mf (fun g => bind (x ()) (fun y => pure (g y)))
    let seq = {
        let mut t = Tele::child(parent);
        let a = t.imp(ty_u.clone());
        let b = t.imp(ty_u.clone());
        let ab = Expr::arrow(a.clone(), b.clone());
        let mf = t.arg(m_at(&ab));
        let x = t.arg(Expr::arrow(unit.clone(), m_at(&a)));
        let k = {
            let mut t2 = Tele::child(&t);
            let g = t2.arg(ab.clone());
            let inner = {
                let mut t3 = Tele::child(&t2);
                let y = t3.arg(a.clone());
                t3.lam(pure(&b, Expr::app(g, y)))
            };
            t2.lam(bind(&a, &b, Expr::app(x, unit_unit.clone()), inner))
        };
        t.lam(bind(&ab, &b, mf, k))
    };
    // seqLeft := fun {α β} (x : M α) (y : Unit → M β) =>
    //              bind x (fun a => bind (y ()) (fun _ => pure a))
    let seq_left = {
        let mut t = Tele::child(parent);
        let a = t.imp(ty_u.clone());
        let b = t.imp(ty_u.clone());
        let x = t.arg(m_at(&a));
        let y = t.arg(Expr::arrow(unit.clone(), m_at(&b)));
        let k = {
            let mut t2 = Tele::child(&t);
            let av = t2.arg(a.clone());
            let inner = {
                let mut t3 = Tele::child(&t2);
                let _ = t3.arg(b.clone());
                t3.lam(pure(&a, av))
            };
            t2.lam(bind(&b, &a, Expr::app(y, unit_unit.clone()), inner))
        };
        t.lam(bind(&a, &a, x, k))
    };
    // seqRight := fun {α β} (x : M α) (y : Unit → M β) => bind x (fun _ => y ())
    let seq_right = {
        let mut t = Tele::child(parent);
        let a = t.imp(ty_u.clone());
        let b = t.imp(ty_u.clone());
        let x = t.arg(m_at(&a));
        let y = t.arg(Expr::arrow(unit.clone(), m_at(&b)));
        let k = {
            let mut t2 = Tele::child(&t);
            let _ = t2.arg(a.clone());
            t2.lam(Expr::app(y, unit_unit.clone()))
        };
        t.lam(bind(&a, &b, x, k))
    };

    let functor = Expr::apps(cst("Functor.mk", &uv), [carrier.clone(), map, map_const]);
    let seq_i = Expr::apps(cst("Seq.mk", &uv), [carrier.clone(), seq]);
    let seq_left_i = Expr::apps(cst("SeqLeft.mk", &uv), [carrier.clone(), seq_left]);
    let seq_right_i = Expr::apps(cst("SeqRight.mk", &uv), [carrier.clone(), seq_right]);
    let applicative = Expr::apps(
        cst("Applicative.mk", &uv),
        [
            carrier.clone(),
            functor,
            pure_inst.clone(),
            seq_i,
            seq_left_i,
            seq_right_i,
        ],
    );
    Expr::apps(
        cst("Monad.mk", &uv),
        [carrier.clone(), applicative, bind_inst.clone()],
    )
}

impl Environment {
    /// Register the Lean-faithful monad hierarchy: the `Applicative` and
    /// `Monad` classes with their parent projections (each an instance), and
    /// the `Pure.pure` / `Bind.bind` projections. See the module doc.
    ///
    /// # Contract
    ///
    /// ENSURES: On success, `self.monad_classes_init == true`
    /// ENSURES: Idempotent
    /// ENSURES: No axiom is registered.
    pub(crate) fn init_monad_classes(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs || self.monad_classes_init {
            return Ok(());
        }
        self.init_unit()?;
        self.init_functor_class()?;
        self.init_seq_classes()?;
        self.init_pure_bind_classes()?;

        self.add_class_projection("Pure", "Pure.pure", 0, None)?;
        self.add_class_projection("Bind", "Bind.bind", 0, None)?;

        // The class sorts are spelled as Lean's `.olean` serializes them, so
        // the `.olean` import meets a type-EQUAL name
        // (`data/prelude_collision_census.json`): `Applicative` states no
        // sort and Lean infers the normalized `Sort (max (u+2) (v+1))`;
        // `Monad` writes `Type (max (u+1) v)`, kept as written.
        let (u, v) = (lparam("u"), lparam("v"));
        self.add_parent_class(
            "Applicative",
            Expr::sort(Level::max(
                Level::succ(Level::succ(u.clone())),
                Level::succ(v.clone()),
            )),
            &[
                ("toFunctor", "Functor"),
                ("toPure", "Pure"),
                ("toSeq", "Seq"),
                ("toSeqLeft", "SeqLeft"),
                ("toSeqRight", "SeqRight"),
            ],
        )?;
        self.add_parent_class(
            "Monad",
            monad_class_sort(&u, &v),
            &[("toApplicative", "Applicative"), ("toBind", "Bind")],
        )?;

        self.monad_classes_init = true;
        Ok(())
    }

    /// `<proj> : {f : Type u → Type v} → [self : <Class> f] → <field type>
    ///          := fun {f} [self] => self.<idx>`.
    ///
    /// The field type is read off the class constructor, so it is the field
    /// exactly as the structure declares it. With `register_as_instance_of`
    /// set, the projection is also registered as an instance of that class
    /// (a parent projection).
    fn add_class_projection(
        &mut self,
        class: &str,
        proj: &str,
        idx: u32,
        register_as_instance_of: Option<&str>,
    ) -> Result<(), EnvError> {
        let (u, v) = (lparam("u"), lparam("v"));
        let uv = [u.clone(), v.clone()];
        let ctor = self
            .get_constructor(&Name::from_string(&format!("{class}.mk")))
            .ok_or_else(|| EnvError::UnknownInductive(Name::from_string(class)))?
            .clone();

        let mut t = Tele::new();
        let f = t.imp(monad_kind(&u, &v));
        let class_f = Expr::app(cst(class, &uv), f.clone());
        let self_ = t.inst(class_f);
        // The constructor type is `{f} → field_0 → … → Class f` (parameters
        // first); instantiate the parameter, then skip `idx` fields.
        let mut field_ty = ctor
            .type_
            .instantiate_level_params_direct(&ctor.level_params, &uv);
        field_ty = match field_ty.kind() {
            crate::expr::ExprKind::Pi(_, _, body) => body.instantiate(&f),
            _ => return Err(EnvError::NotStructure(Name::from_string(class))),
        };
        for _ in 0..idx {
            field_ty = match field_ty.kind() {
                // Fields of these classes never depend on earlier fields.
                crate::expr::ExprKind::Pi(_, _, body) => {
                    body.instantiate(&Expr::sort(Level::zero()))
                }
                _ => return Err(EnvError::NotStructure(Name::from_string(class))),
            };
        }
        let field_ty = match field_ty.kind() {
            crate::expr::ExprKind::Pi(_, dom, _) => (**dom).clone(),
            _ => return Err(EnvError::NotStructure(Name::from_string(class))),
        };
        let ty = t.pi(field_ty);
        let val = t.lam(Expr::proj(Name::from_string(class), idx, self_));

        self.add_decl(Declaration::Definition {
            name: Name::from_string(proj),
            level_params: vec![Name::from_string("u"), Name::from_string("v")],
            type_: ty,
            value: val,
            is_reducible: true,
        })?;
        if let Some(parent_class) = register_as_instance_of {
            self.register_instance(KernelInstanceInfo {
                name: Name::from_string(proj),
                class_name: Name::from_string(parent_class),
                priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }
        Ok(())
    }

    /// A class over `f : Type u → Type v` whose fields are exactly its
    /// parents, each an instance-implicit constructor binder (`class C (f)
    /// extends P₁ f, …, Pₙ f` with no own fields), plus its parent
    /// projections registered as instances.
    fn add_parent_class(
        &mut self,
        class: &str,
        class_sort: Expr,
        parents: &[(&str, &str)],
    ) -> Result<(), EnvError> {
        let (u, v) = (lparam("u"), lparam("v"));
        let uv = [u.clone(), v.clone()];
        let ctor_type = {
            let mut t = Tele::new();
            let f = t.imp(monad_kind(&u, &v));
            for (_, parent) in parents {
                let _ = t.inst(Expr::app(cst(parent, &uv), f.clone()));
            }
            t.pi(Expr::app(cst(class, &uv), f))
        };
        self.add_inductive(InductiveDecl {
            level_params: vec![Name::from_string("u"), Name::from_string("v")],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string(class),
                type_: Expr::pi(BinderInfo::Default, monad_kind(&u, &v), class_sort),
                constructors: vec![Constructor {
                    name: Name::from_string(&format!("{class}.mk")),
                    type_: ctor_type,
                }],
            }],
        })?;
        self.register_structure_fields(
            Name::from_string(class),
            parents.iter().map(|(f, _)| Name::from_string(f)).collect(),
        )?;
        self.register_structure_parents(
            Name::from_string(class),
            parents
                .iter()
                .map(|(f, p)| (Name::from_string(f), Name::from_string(p)))
                .collect(),
        );
        self.register_class(KernelClassInfo {
            name: Name::from_string(class),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });
        for (idx, (field, parent)) in parents.iter().enumerate() {
            let idx = u32::try_from(idx).unwrap_or(u32::MAX);
            self.add_class_projection(class, &format!("{class}.{field}"), idx, Some(parent))?;
        }
        Ok(())
    }

    /// Register `name : Monad.{u,v} carrier := monad_mk_from(…)` under the
    /// given telescope of instance parameters, and register it as a `Monad`
    /// instance. `build` receives the open telescope and returns
    /// `(u, v, carrier, pure_inst, bind_inst)`.
    pub(crate) fn add_monad_instance(
        &mut self,
        name: &str,
        level_params: &[&str],
        build: impl FnOnce(&mut Tele) -> (Level, Level, Expr, Expr, Expr),
    ) -> Result<(), EnvError> {
        let mut t = Tele::new();
        let (u, v, carrier, pure_inst, bind_inst) = build(&mut t);
        let monad_ty = Expr::app(cst("Monad", &[u.clone(), v.clone()]), carrier.clone());
        let value = monad_mk_from(&u, &v, &carrier, &pure_inst, &bind_inst, &t);
        self.add_decl(Declaration::Definition {
            name: Name::from_string(name),
            level_params: level_params.iter().map(|p| Name::from_string(p)).collect(),
            type_: t.pi(monad_ty),
            value: t.lam(value),
            is_reducible: true,
        })?;
        self.register_instance(KernelInstanceInfo {
            name: Name::from_string(name),
            class_name: Name::from_string("Monad"),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
        Ok(())
    }

    /// `Id.instMonad` and `instMonadOption` (Lean core), from the leaf
    /// `instPure*` / `instBind*` instances `data_monad_insts.rs` registers.
    ///
    /// # Contract
    ///
    /// ENSURES: Idempotent
    pub(crate) fn init_core_monad_instances(&mut self) -> Result<(), EnvError> {
        if self.suppress_lossy_structure_stubs || self.core_monad_instances_init {
            return Ok(());
        }
        self.init_monad_classes()?;
        self.init_monad_id_insts()?;
        self.init_monad_option_insts()?;
        for (inst, carrier, pure_i, bind_i) in [
            ("Id.instMonad", "Id", "instPureId", "instBindId"),
            (
                "instMonadOption",
                "Option",
                "instPureOption",
                "instBindOption",
            ),
        ] {
            self.add_monad_instance(inst, &["u"], |_| {
                let u = lparam("u");
                (
                    u.clone(),
                    u.clone(),
                    cst(carrier, std::slice::from_ref(&u)),
                    cst(pure_i, std::slice::from_ref(&u)),
                    cst(bind_i, &[u]),
                )
            })?;
        }
        self.core_monad_instances_init = true;
        Ok(())
    }

    /// `instMonadIO : Monad IO` from the opaque `IO.pure` / `IO.bind`
    /// (Clean-native: Lean's `IO` is `EIO IO.Error` with `instMonadEIO`; here
    /// `IO` is an opaque type, so its monad structure is its two opaque
    /// operations). Called by [`Environment::init_io`].
    pub(crate) fn init_io_monad_instance(&mut self) -> Result<(), EnvError> {
        self.init_monad_classes()?;
        let z = [Level::zero(), Level::zero()];
        let io = cst("IO", &[]);
        let pure_i = Expr::apps(cst("Pure.mk", &z), [io.clone(), cst("IO.pure", &[])]);
        let bind_i = Expr::apps(cst("Bind.mk", &z), [io.clone(), cst("IO.bind", &[])]);
        self.add_monad_instance("instMonadIO", &[], |_| {
            (Level::zero(), Level::zero(), io, pure_i, bind_i)
        })
    }

    /// `instMonadList` — Clean-native (Lean core has no `List` monad), for the
    /// builtin `clean check` lane only; see `init_monad_list_insts`.
    pub(crate) fn init_list_monad_instance(&mut self) -> Result<(), EnvError> {
        self.init_monad_classes()?;
        self.add_monad_instance("instMonadList", &["u"], |_| {
            let u = lparam("u");
            (
                u.clone(),
                u.clone(),
                cst("List", std::slice::from_ref(&u)),
                cst("instPureList", std::slice::from_ref(&u)),
                cst("instBindList", &[u]),
            )
        })
    }
}

/// `MonadInst` for a `[Monad m]` binder of a telescope.
pub(crate) fn monad_inst(u: &Level, v: &Level, m: &Expr, inst: &Expr) -> MonadInst {
    MonadInst {
        u: u.clone(),
        v: v.clone(),
        m: m.clone(),
        inst: inst.clone(),
    }
}
