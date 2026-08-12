// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Equivalence` / `Setoid` / `HasEquiv` / `Quotient` — the Lean 4 core
//! quotient-by-a-setoid package.
//!
//! The kernel already carries the five quotient PRIMITIVES (`Quot`, `Quot.mk`,
//! `Quot.lift`, `Quot.ind`, `Quot.sound`) as `QuotVal` records seeded by
//! [`crate::quot::init_quot_vals`] (`quot.rs:508`, installed through
//! [`Environment::init_quot`]), and the ι-rule
//! `Quot.lift f h (Quot.mk r a) ≡ f a` already fires in
//! `tc/reduction/mod.rs::try_quot_reduction`. **Nothing in this module touches
//! the kernel or the TCB**: every declaration below is an ordinary CHECKED
//! `add_inductive` / `add_decl`, and the whole package's axiom closure is
//! exactly `{Quot.sound}` (a foundational quotient primitive already in the
//! census) — no new axiom, no `add_decl_structural`, no `add_decl_unchecked`.
//!
//! # Ground truth
//!
//! Every signature here was read off Lean 4 **v4.30.0**
//! (`~/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Init/Core.lean`)
//! and cross-checked against that toolchain's own elaborated output
//! (`set_option pp.universes true; set_option pp.explicit true; #print …`),
//! so the binder infos, universe parameters and value spellings below are the
//! ones Lean actually stores — not a reading of the surface syntax. The source
//! line for each declaration is cited above its registration.
//!
//! Two binder conventions bite here, and both are Lean-verified above each
//! registration:
//!
//! * **Type formers take the class-header binders**: `Setoid (α : Sort u)` and
//!   `HasEquiv (α : Sort u)` take `α` EXPLICITLY; `Equivalence {α : Sort u}
//!   (r : α → α → Prop)` takes `α` implicitly and `r` explicitly, exactly as
//!   written in the `structure`/`class` header.
//! * **Constructors and projections take the inductive params IMPLICITLY** —
//!   `Setoid.mk {α : Sort u} (r) (iseqv)`, `HasEquiv.mk {α : Sort u} (Equiv)`,
//!   `Equivalence.mk {α} {r} (refl) (symm) (trans)` — and a class projection
//!   additionally takes the structure argument INSTANCE-implicit
//!   (`Setoid.r {α} [self : Setoid α]`), per `elab_structure.rs`'s
//!   `StructureKind::Class` contract.
//!
//! Reducibility is likewise Lean-verified (`getReducibilityStatusCore`):
//! `HasEquiv.Equiv`, `Quotient.lift`, `Quotient.liftOn` and `Quot.liftOn` are
//! `reducible`; `Setoid.r`, `Setoid.iseqv`, `Quotient`, `Quotient.mk` and
//! `Quotient.mk'` are `semireducible` (Clean: `is_reducible: false`, which
//! `add_decl` turns into `Reducibility::Regular(height)`). The single
//! judgement call is `instHasEquivOfSetoid`, which Lean 4.30 marks
//! `implicitReducible` — a status Clean's boolean does not model; it is
//! registered `is_reducible: false` + a registered instance, which is
//! exactly Lean's `implicit_reducible` (see the note at its registration).
//!
//! Binder construction goes through [`EnvDeclBuilder`] throughout — no
//! hand-rolled de Bruijn indices (#1403/#1442/#1443/#1444).

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{
    Constructor, Declaration, EnvError, Environment, InductiveDecl, InductiveType, KernelClassInfo,
    KernelInstanceInfo, LEAN_DEFAULT_INSTANCE_PRIORITY,
};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;
use crate::quot::names as quot_names;

/// `Expr::const_` over a string literal — the spelling every neighbouring
/// prelude module uses inline.
fn konst(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

/// The shape of every setoid relation: `α → α → Prop`.
///
/// `alpha` must be an `EnvDeclBuilder` FVar (not a BVar) — FVars are
/// depth-independent, so the two nested `Expr::pi`s need no index shifting.
fn rel_type(alpha: &Expr) -> Expr {
    Expr::pi(
        BinderInfo::Default,
        alpha.clone(),
        Expr::pi(BinderInfo::Default, alpha.clone(), Expr::prop()),
    )
}

/// `@Eq.{v} β lhs rhs`.
fn eq_at(v_level: &Level, beta: &Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(konst("Eq", vec![v_level.clone()]), [beta.clone(), lhs, rhs])
}

/// The head of `a ≈ b` for a `Setoid` instance:
/// `@HasEquiv.Equiv.{u, 0} α (@instHasEquivOfSetoid.{u} α inst)`.
///
/// Lean elaborates `≈` in the `Setoid` namespace to exactly this — the `≈`
/// notation is `HasEquiv.Equiv`, and the instance found is
/// `instHasEquivOfSetoid` at `v := 0` (`Init/Core.lean:1560`). Spelling it
/// this way (rather than the definitionally-equal `@Setoid.r.{u} α inst`) is
/// what makes `Setoid.refl`/`Quotient.sound`/`Quotient.lift` byte-faithful to
/// the `.olean`, which matters because the `.olean` importer dedups by name.
fn setoid_equiv_head(u_level: &Level, alpha: &Expr, inst: &Expr) -> Expr {
    Expr::apps(
        konst("HasEquiv.Equiv", vec![u_level.clone(), Level::zero()]),
        [
            alpha.clone(),
            Expr::apps(
                konst("instHasEquivOfSetoid", vec![u_level.clone()]),
                [alpha.clone(), inst.clone()],
            ),
        ],
    )
}

/// `@Setoid.r.{u} α s` — the underlying relation of a setoid.
fn setoid_r_app(u_level: &Level, alpha: &Expr, s: &Expr) -> Expr {
    Expr::apps(
        konst("Setoid.r", vec![u_level.clone()]),
        [alpha.clone(), s.clone()],
    )
}

/// `@Quotient.{u} α s`.
fn quotient_app(u_level: &Level, alpha: &Expr, s: &Expr) -> Expr {
    Expr::apps(
        konst("Quotient", vec![u_level.clone()]),
        [alpha.clone(), s.clone()],
    )
}

/// `@Quotient.mk.{u} α s a`.
fn quotient_mk_app(u_level: &Level, alpha: &Expr, s: &Expr, a: Expr) -> Expr {
    Expr::apps(
        konst("Quotient.mk", vec![u_level.clone()]),
        [alpha.clone(), s.clone(), a],
    )
}

impl Environment {
    /// Register the `Equivalence` / `Setoid` / `HasEquiv` / `Quotient`
    /// package (Lean 4 core `Init/Core.lean`).
    ///
    /// Registers, in dependency order:
    ///
    /// | name | kind | Lean 4.30 `Init/Core.lean` |
    /// |---|---|---|
    /// | `Equivalence`, `Equivalence.mk`, `.refl`, `.symm`, `.trans` | structure + 3 theorems | 1311 |
    /// | `Setoid`, `Setoid.mk`, `Setoid.r`, `Setoid.iseqv` | class + def + theorem | 1554 |
    /// | `HasEquiv`, `HasEquiv.mk`, `HasEquiv.Equiv` | class + reducible def | 489 |
    /// | `instHasEquivOfSetoid` | instance | 1560 |
    /// | `Setoid.refl`, `Setoid.symm`, `Setoid.trans` | theorems | 1567/1571/1575 |
    /// | `Quot.liftOn`, `Quot.inductionOn` | reducible def + theorem | 1817/1822 |
    /// | `Quotient`, `.mk`, `.mk'`, `.sound`, `.lift`, `.ind`, `.liftOn`, `.inductionOn` | def/theorem cluster | 1955-2040 |
    ///
    /// `Quotient.exact` is deliberately NOT registered — see the module-level
    /// note in the handoff: v4.30 derives it through the private auxiliary
    /// `Quotient.rel_of_eq`, and reconstructing that derivation by hand would
    /// be speculative. It is a missing convenience, not a gap in the package's
    /// soundness story.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: dependencies (`Eq`, `True`/`Prop` core, the `Quot` primitives)
    ///          are initialized first
    /// ENSURES: every declaration goes through the CHECKED `add_inductive` /
    ///          `add_decl` path — no axiom is added, and the package's
    ///          transitive axiom closure is `{Quot.sound}`
    /// ENSURES: Idempotent — `add_inductive` is idempotent by [R12] and every
    ///          `add_decl` goes through `add_decl_if_absent`
    ///
    /// # Errors
    ///
    /// Returns [`EnvError`] if any declaration fails its kernel type check or
    /// if a required dependency is missing.
    pub(crate) fn init_quotient_setoid(&mut self) -> Result<(), EnvError> {
        // `Eq` (used by every lift's respect-obligation) and the `Quot`
        // primitives (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`,
        // `Quot.sound`). Both are idempotent.
        self.init_eq()?;
        self.init_quot();

        self.init_equivalence_structure()?;
        self.init_setoid_class()?;
        self.init_has_equiv_class()?;
        self.init_setoid_equiv_lemmas()?;
        self.init_quot_companions()?;
        self.init_quotient_family()?;

        Ok(())
    }

    /// `structure Equivalence {α : Sort u} (r : α → α → Prop) : Prop`
    /// (`Init/Core.lean:1311`).
    ///
    /// Elaborated form (Lean 4.30 `#print`):
    /// ```text
    /// structure Equivalence.{u} {α : Sort u} (r : α → α → Prop) : Prop
    /// Equivalence.mk.{u} {α : Sort u} {r : α → α → Prop}
    ///   (refl : ∀ (x : α), r x x)
    ///   (symm : ∀ {x y : α}, r x y → r y x)
    ///   (trans : ∀ {x y z : α}, r x y → r y z → r x z) : @Equivalence.{u} α r
    /// ```
    ///
    /// Note the binder split: the type former takes `{α}` IMPLICIT and `(r)`
    /// EXPLICIT (the `structure` header), while the constructor takes BOTH
    /// params implicitly. The three projections are `theorem`s (the structure
    /// is a `Prop`), each spelled as a `Proj` on the structure argument —
    /// exactly Lean's `fun α r self => self.1/2/3` — which is the same
    /// Prop-structure projection idiom `init_and` uses for `And.left`.
    fn init_equivalence_structure(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::sort(u_level.clone());
        let equivalence = |alpha: &Expr, r: &Expr| {
            Expr::apps(
                konst("Equivalence", vec![u_level.clone()]),
                [alpha.clone(), r.clone()],
            )
        };

        // Equivalence.{u} : {α : Sort u} → (α → α → Prop) → Prop
        let equivalence_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let rel = rel_type(&alpha);
            let (r_id, _r) = b.fresh_local(rel.clone());
            let e = Expr::prop();
            let e = b.mk_pi(r_id, BinderInfo::Default, rel, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        // Equivalence.mk.{u} : {α : Sort u} → {r : α → α → Prop} →
        //   (∀ x, r x x) → (∀ {x y}, r x y → r y x) →
        //   (∀ {x y z}, r x y → r y z → r x z) → @Equivalence α r
        let equivalence_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let rel = rel_type(&alpha);
            let (r_id, r) = b.fresh_local(rel.clone());

            let (refl_ty, symm_ty, trans_ty) = equivalence_field_types(&b, &alpha, &r);

            let (refl_id, _) = b.fresh_local(refl_ty.clone());
            let (symm_id, _) = b.fresh_local(symm_ty.clone());
            let (trans_id, _) = b.fresh_local(trans_ty.clone());

            let e = equivalence(&alpha, &r);
            let e = b.mk_pi(trans_id, BinderInfo::Default, trans_ty, e);
            let e = b.mk_pi(symm_id, BinderInfo::Default, symm_ty, e);
            let e = b.mk_pi(refl_id, BinderInfo::Default, refl_ty, e);
            let e = b.mk_pi(r_id, BinderInfo::Implicit, rel, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        self.add_inductive(InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 2,
            types: vec![InductiveType {
                name: Name::from_string("Equivalence"),
                type_: equivalence_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Equivalence.mk"),
                    type_: equivalence_mk_type,
                }],
            }],
        })?;

        self.register_structure_fields(
            Name::from_string("Equivalence"),
            vec![
                Name::from_string("refl"),
                Name::from_string("symm"),
                Name::from_string("trans"),
            ],
        )?;

        // Equivalence.refl.{u} : ∀ {α : Sort u} {r : α → α → Prop},
        //   @Equivalence α r → ∀ (x : α), r x x            := fun α r self => self.1
        // Equivalence.symm.{u} : ... → ∀ {x y : α}, r x y → r y x   := self.2
        // Equivalence.trans.{u} : ... → ∀ {x y z}, ... → ... → ...  := self.3
        //
        // All three are THEOREMS in Lean (`Prop`-valued structure), so they
        // are registered as `Declaration::Theorem` — `Reducibility::Opaque`,
        // which is harmless: their results are `Prop`s and proof irrelevance
        // covers every use.
        for (idx, field) in [(0u32, "refl"), (1u32, "symm"), (2u32, "trans")] {
            let projection_name = format!("Equivalence.{field}");

            let projection_type = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
                let rel = rel_type(&alpha);
                let (r_id, r) = b.fresh_local(rel.clone());
                let equiv_ar = equivalence(&alpha, &r);
                let (self_id, _) = b.fresh_local(equiv_ar.clone());

                let (refl_ty, symm_ty, trans_ty) = equivalence_field_types(&b, &alpha, &r);
                let body = match idx {
                    0 => refl_ty,
                    1 => symm_ty,
                    _ => trans_ty,
                };

                let e = b.mk_pi(self_id, BinderInfo::Default, equiv_ar, body);
                let e = b.mk_pi(r_id, BinderInfo::Implicit, rel, e);
                let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
                b.finish(e)
            };

            let projection_value = {
                let mut b = EnvDeclBuilder::new();
                let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
                let rel = rel_type(&alpha);
                let (r_id, r) = b.fresh_local(rel.clone());
                let equiv_ar = equivalence(&alpha, &r);
                let (self_id, self_var) = b.fresh_local(equiv_ar.clone());

                let body = Expr::proj(Name::from_string("Equivalence"), idx, self_var);
                let e = b.mk_lam(self_id, BinderInfo::Default, equiv_ar, body);
                let e = b.mk_lam(r_id, BinderInfo::Implicit, rel, e);
                let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
                b.finish(e)
            };

            self.add_decl_if_absent(Declaration::Theorem {
                name: Name::from_string(&projection_name),
                level_params: vec![u.clone()],
                type_: projection_type,
                value: projection_value,
            })?;
        }

        Ok(())
    }

    /// ```lean
    /// class Setoid (α : Sort u) where
    ///   r : α → α → Prop
    ///   iseqv : Equivalence r
    /// ```
    /// (`Init/Core.lean:1554`.)
    ///
    /// Elaborated form (Lean 4.30 `#print`):
    /// ```text
    /// class Setoid.{u} (α : Sort u) : Sort (max 1 u)
    /// Setoid.mk.{u} {α : Sort u} (r : α → α → Prop) (iseqv : @Equivalence.{u} α r) : Setoid.{u} α
    /// def     Setoid.r.{u}     : {α : Sort u} → [self : Setoid.{u} α] → α → α → Prop
    /// theorem Setoid.iseqv.{u} : ∀ {α : Sort u} [self : Setoid.{u} α],
    ///                              @Equivalence.{u} α (@Setoid.r.{u} α self)
    /// ```
    ///
    /// `Sort (max 1 u)` is `max`, NOT `imax` — same reasoning as `Inhabited`
    /// (`data_typeclasses.rs`): `imax 1 u` collapses to `0` at `u = 0`, which
    /// is not provably nonzero, so the elimination gate would strip large
    /// elimination from `Setoid.rec`.
    fn init_setoid_class(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::sort(u_level.clone());
        // Sort (max 1 u)
        let setoid_sort = Expr::sort(Level::max(Level::succ(Level::zero()), u_level.clone()));
        let setoid =
            |alpha: &Expr| Expr::app(konst("Setoid", vec![u_level.clone()]), alpha.clone());

        // Setoid.{u} : (α : Sort u) → Sort (max 1 u)   — α EXPLICIT (class header)
        let setoid_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _alpha) = b.fresh_local(sort_u.clone());
            let e = b.mk_pi(alpha_id, BinderInfo::Default, sort_u.clone(), setoid_sort);
            b.finish(e)
        };

        // Setoid.mk.{u} : {α : Sort u} → (r : α → α → Prop) →
        //                 (iseqv : @Equivalence α r) → Setoid α
        // — α IMPLICIT in the constructor.
        let setoid_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let rel = rel_type(&alpha);
            let (r_id, r) = b.fresh_local(rel.clone());
            let equiv_ar = Expr::apps(
                konst("Equivalence", vec![u_level.clone()]),
                [alpha.clone(), r.clone()],
            );
            let (iseqv_id, _) = b.fresh_local(equiv_ar.clone());

            let e = setoid(&alpha);
            let e = b.mk_pi(iseqv_id, BinderInfo::Default, equiv_ar, e);
            let e = b.mk_pi(r_id, BinderInfo::Default, rel, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        self.add_inductive(InductiveDecl {
            level_params: vec![u.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("Setoid"),
                type_: setoid_type,
                constructors: vec![Constructor {
                    name: Name::from_string("Setoid.mk"),
                    type_: setoid_mk_type,
                }],
            }],
        })?;

        self.register_structure_fields(
            Name::from_string("Setoid"),
            vec![Name::from_string("r"), Name::from_string("iseqv")],
        )?;

        // `Setoid` is a `class`: one parameter, no `outParam`, no
        // `semiOutParam` (the header is a bare `(α : Sort u)`).
        self.register_class(KernelClassInfo {
            name: Name::from_string("Setoid"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // Setoid.r : {α : Sort u} → [self : Setoid α] → α → α → Prop
        //          := fun α self => self.1
        //
        // Lean reducibility: SEMIREDUCIBLE (verified with
        // `getReducibilityStatusCore`), unlike most Clean prelude projections
        // which are registered reducible. Faithful is what matters here: the
        // one place the unfolding is load-bearing (`Quotient s ≡ Quot
        // (Setoid.r s)`) runs at default transparency, where `Regular` unfolds.
        let setoid_r_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (self_id, _) = b.fresh_local(setoid_alpha.clone());
            let e = rel_type(&alpha);
            let e = b.mk_pi(self_id, BinderInfo::InstImplicit, setoid_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        let setoid_r_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (self_id, self_var) = b.fresh_local(setoid_alpha.clone());
            let body = Expr::proj(Name::from_string("Setoid"), 0, self_var);
            let e = b.mk_lam(self_id, BinderInfo::InstImplicit, setoid_alpha, body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Setoid.r"),
            level_params: vec![u.clone()],
            type_: setoid_r_type,
            value: setoid_r_value,
            // Lean has this semireducible, and MEASURED 2026-08-11: making it
            // reducible (Clean's local habit for comparable projections) does
            // NOT change the fixture score, so Lean fidelity is free here and
            // is kept. The residual `Quotient s = Quot (Setoid.r s)` / sound
            // rfl identities are blocked further down the chain, not by this.
            is_reducible: false,
        })?;

        // Setoid.iseqv : ∀ {α : Sort u} [self : Setoid α],
        //                  @Equivalence α (@Setoid.r α self)   := fun α self => self.2
        //
        // A THEOREM in Lean (the field is `Prop`-valued even though `Setoid`
        // is not a `Prop`). The declared type spells the relation as
        // `@Setoid.r α self`; the `Proj` value's inferred type spells it
        // `Setoid.2 self` — δ on `Setoid.r` closes the gap.
        let setoid_iseqv_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (self_id, self_var) = b.fresh_local(setoid_alpha.clone());
            let e = Expr::apps(
                konst("Equivalence", vec![u_level.clone()]),
                [alpha.clone(), setoid_r_app(&u_level, &alpha, &self_var)],
            );
            let e = b.mk_pi(self_id, BinderInfo::InstImplicit, setoid_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        let setoid_iseqv_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (self_id, self_var) = b.fresh_local(setoid_alpha.clone());
            let body = Expr::proj(Name::from_string("Setoid"), 1, self_var);
            let e = b.mk_lam(self_id, BinderInfo::InstImplicit, setoid_alpha, body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string("Setoid.iseqv"),
            level_params: vec![u],
            type_: setoid_iseqv_type,
            value: setoid_iseqv_value,
        })?;

        Ok(())
    }

    /// ```lean
    /// class HasEquiv (α : Sort u) where
    ///   Equiv : α → α → Sort v
    /// attribute [reducible] HasEquiv.Equiv
    /// ```
    /// (`Init/Core.lean:489`/`494`.)
    ///
    /// Elaborated form (Lean 4.30 `#print`):
    /// ```text
    /// class HasEquiv.{u, v} (α : Sort u) : Sort (max u (v + 1))
    /// HasEquiv.mk.{u, v} {α : Sort u} (Equiv : α → α → Sort v) : HasEquiv.{u, v} α
    /// @[reducible] def HasEquiv.Equiv.{u, v} :
    ///   {α : Sort u} → [self : HasEquiv.{u, v} α] → α → α → Sort v
    /// ```
    ///
    /// TWO universe parameters: the carrier at `u`, the equivalence's codomain
    /// at `v` (`≈` is allowed to be data-valued, not just `Prop`-valued).
    /// `instHasEquivOfSetoid` then instantiates `v := 0`.
    fn init_has_equiv_class(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let sort_u = Expr::sort(u_level.clone());
        let sort_v = Expr::sort(v_level.clone());
        // Sort (max u (v+1))
        let has_equiv_sort = Expr::sort(Level::max(u_level.clone(), Level::succ(v_level.clone())));
        let has_equiv_levels = vec![u_level.clone(), v_level.clone()];
        let has_equiv =
            |alpha: &Expr| Expr::app(konst("HasEquiv", has_equiv_levels.clone()), alpha.clone());
        // α → α → Sort v
        let equiv_field_type = |alpha: &Expr| {
            Expr::pi(
                BinderInfo::Default,
                alpha.clone(),
                Expr::pi(BinderInfo::Default, alpha.clone(), sort_v.clone()),
            )
        };

        // HasEquiv.{u,v} : (α : Sort u) → Sort (max u (v+1))  — α EXPLICIT
        let has_equiv_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, _alpha) = b.fresh_local(sort_u.clone());
            let e = b.mk_pi(
                alpha_id,
                BinderInfo::Default,
                sort_u.clone(),
                has_equiv_sort,
            );
            b.finish(e)
        };

        // HasEquiv.mk.{u,v} : {α : Sort u} → (α → α → Sort v) → HasEquiv α
        let has_equiv_mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let field = equiv_field_type(&alpha);
            let (field_id, _) = b.fresh_local(field.clone());
            let e = has_equiv(&alpha);
            let e = b.mk_pi(field_id, BinderInfo::Default, field, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        self.add_inductive(InductiveDecl {
            level_params: vec![u.clone(), v.clone()],
            num_params: 1,
            types: vec![InductiveType {
                name: Name::from_string("HasEquiv"),
                type_: has_equiv_type,
                constructors: vec![Constructor {
                    name: Name::from_string("HasEquiv.mk"),
                    type_: has_equiv_mk_type,
                }],
            }],
        })?;

        self.register_structure_fields(
            Name::from_string("HasEquiv"),
            vec![Name::from_string("Equiv")],
        )?;

        // One parameter, and NO `outParam`/`semiOutParam`: the Lean header is a
        // bare `(α : Sort u)`. (`semiOutParam` would be needed for the `Coe`
        // family; nothing in this package uses it — see the handoff note.)
        self.register_class(KernelClassInfo {
            name: Name::from_string("HasEquiv"),
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });

        // HasEquiv.Equiv : {α : Sort u} → [self : HasEquiv.{u,v} α] → α → α → Sort v
        //                := fun α self => self.1
        // `@[reducible]` in Lean (`attribute [reducible] HasEquiv.Equiv`,
        // Init/Core.lean:494) — LOAD-BEARING: `Quotient.lift`/`Quotient.sound`
        // are only well-typed because `HasEquiv.Equiv α (instHasEquivOfSetoid
        // α s)` reduces to `Setoid.r α s`, and Lean keeps that reduction
        // available at `Reducible` transparency.
        let equiv_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let inst_ty = has_equiv(&alpha);
            let (self_id, _) = b.fresh_local(inst_ty.clone());
            let e = equiv_field_type(&alpha);
            let e = b.mk_pi(self_id, BinderInfo::InstImplicit, inst_ty, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        let equiv_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let inst_ty = has_equiv(&alpha);
            let (self_id, self_var) = b.fresh_local(inst_ty.clone());
            let body = Expr::proj(Name::from_string("HasEquiv"), 0, self_var);
            let e = b.mk_lam(self_id, BinderInfo::InstImplicit, inst_ty, body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("HasEquiv.Equiv"),
            level_params: vec![u, v],
            type_: equiv_type,
            value: equiv_value,
            is_reducible: true,
        })?;

        Ok(())
    }

    /// ```lean
    /// instance {α : Sort u} [Setoid α] : HasEquiv α := ⟨Setoid.r⟩
    /// ```
    /// (`Init/Core.lean:1560`, auto-named `instHasEquivOfSetoid`) plus
    /// `Setoid.refl` / `Setoid.symm` / `Setoid.trans`
    /// (`Init/Core.lean:1567`/`1571`/`1575`).
    ///
    /// Elaborated forms (Lean 4.30 `#print`):
    /// ```text
    /// @[implicit_reducible] def instHasEquivOfSetoid.{u} :
    ///   {α : Sort u} → [Setoid.{u} α] → HasEquiv.{u, 0} α :=
    ///   fun {α} [inst : Setoid.{u} α] => @HasEquiv.mk.{u, 0} α (@Setoid.r.{u} α inst)
    ///
    /// theorem Setoid.refl.{u} : ∀ {α : Sort u} [inst : Setoid.{u} α] (a : α),
    ///   @HasEquiv.Equiv.{u, 0} α (@instHasEquivOfSetoid.{u} α inst) a a :=
    ///   fun {α} [inst] a =>
    ///     @Equivalence.refl.{u} α (@Setoid.r.{u} α inst) (@Setoid.iseqv.{u} α inst) a
    /// ```
    /// (`symm`/`trans` likewise, with `{a b}` / `{a b c}` implicit.)
    ///
    /// The `v := 0` instantiation of `HasEquiv` is what makes `≈` a `Prop` for
    /// setoids.
    fn init_setoid_equiv_lemmas(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let sort_u = Expr::sort(u_level.clone());
        let setoid =
            |alpha: &Expr| Expr::app(konst("Setoid", vec![u_level.clone()]), alpha.clone());
        // HasEquiv.{u, 0} α — the instance's declared class type.
        let has_equiv_0 = |alpha: &Expr| {
            Expr::app(
                konst("HasEquiv", vec![u_level.clone(), Level::zero()]),
                alpha.clone(),
            )
        };

        // instHasEquivOfSetoid : {α : Sort u} → [Setoid α] → HasEquiv.{u,0} α
        let inst_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (inst_id, _) = b.fresh_local(setoid_alpha.clone());
            let e = has_equiv_0(&alpha);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, setoid_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        // value: fun {α} [inst] => @HasEquiv.mk.{u,0} α (@Setoid.r.{u} α inst)
        let inst_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (inst_id, inst) = b.fresh_local(setoid_alpha.clone());
            let body = Expr::apps(
                konst("HasEquiv.mk", vec![u_level.clone(), Level::zero()]),
                [alpha.clone(), setoid_r_app(&u_level, &alpha, &inst)],
            );
            let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, setoid_alpha, body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };

        // Lean marks this `implicit_reducible`: "unfolded at
        // `TransparencyMode.instances` OR ABOVE" (v4.30
        // `Lean/ReducibilityAttrs.lean:20`) — deliberately NOT at
        // `.reducible`. Clean's boolean cannot name that status directly, but
        // it reproduces it EXACTLY as `Regular` + a registered instance:
        // `unfold_with_transparency` (env/unfold.rs:217-220) unfolds any
        // registered non-`Opaque` instance once `mode == Instances`, whatever
        // its reducibility. So `false` here plus the `ensure_exact_instance`
        // below is bit-for-bit Lean; `true` would additionally expose it to
        // every `Reducible`-transparency path (`with_reducible`, `simp`/
        // `dsimp` matching, whnfR unification), letting Clean accept `≈`
        // rewrites Lean rejects and changing elaborated normal forms.
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("instHasEquivOfSetoid"),
            level_params: vec![u.clone()],
            type_: inst_type.clone(),
            value: inst_value.clone(),
            is_reducible: false,
        })?;

        // Registered with `type_`/`value` populated: the instance's binders
        // (`{α}` implicit, `[Setoid α]` instance-implicit) differ from what a
        // projection constant would carry, and the elaborator's InstanceTable
        // is rebuilt from exactly these fields (Fix #443).
        //
        // Priority: Lean's unannotated `instance` default is 1000
        // (`LEAN_DEFAULT_INSTANCE_PRIORITY`) — NOT Clean's fabricated
        // `DEFAULT_INSTANCE_PRIORITY` (100), which is reserved for instances
        // whose real priority is unknown. This one mirrors a real Lean
        // instance, so its real priority is known.
        //
        // `ensure_exact_instance` (not `register_instance`) keeps the whole
        // initializer idempotent: a second call accepts the existing entry
        // only if it matches exactly, and fails closed on metadata drift
        // instead of silently appending a duplicate registry row.
        self.ensure_exact_instance(KernelInstanceInfo {
            name: Name::from_string("instHasEquivOfSetoid"),
            class_name: Name::from_string("HasEquiv"),
            priority: LEAN_DEFAULT_INSTANCE_PRIORITY,
            type_: Some(inst_type),
            value: Some(inst_value),
        })?;

        // Setoid.refl : ∀ {α} [inst : Setoid α] (a : α), a ≈ a
        let refl_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (inst_id, inst) = b.fresh_local(setoid_alpha.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let equiv = setoid_equiv_head(&u_level, &alpha, &inst);
            let e = Expr::apps(equiv, [a.clone(), a.clone()]);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, setoid_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        let refl_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (inst_id, inst) = b.fresh_local(setoid_alpha.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let body = Expr::apps(
                konst("Equivalence.refl", vec![u_level.clone()]),
                [
                    alpha.clone(),
                    setoid_r_app(&u_level, &alpha, &inst),
                    Expr::apps(
                        konst("Setoid.iseqv", vec![u_level.clone()]),
                        [alpha.clone(), inst.clone()],
                    ),
                    a,
                ],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, setoid_alpha, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string("Setoid.refl"),
            level_params: vec![u.clone()],
            type_: refl_type,
            value: refl_value,
        })?;

        // Setoid.symm : ∀ {α} [inst] {a b : α}, a ≈ b → b ≈ a
        let symm_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (inst_id, inst) = b.fresh_local(setoid_alpha.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (b_id, bb) = b.fresh_local(alpha.clone());
            let equiv = setoid_equiv_head(&u_level, &alpha, &inst);
            let hyp = Expr::apps(equiv.clone(), [a.clone(), bb.clone()]);
            let concl = Expr::apps(equiv, [bb.clone(), a.clone()]);
            let e = Expr::pi(BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(b_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, setoid_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        let symm_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (inst_id, inst) = b.fresh_local(setoid_alpha.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (b_id, bb) = b.fresh_local(alpha.clone());
            let equiv = setoid_equiv_head(&u_level, &alpha, &inst);
            let hyp = Expr::apps(equiv, [a.clone(), bb.clone()]);
            let (h_id, h) = b.fresh_local(hyp.clone());
            let body = Expr::apps(
                konst("Equivalence.symm", vec![u_level.clone()]),
                [
                    alpha.clone(),
                    setoid_r_app(&u_level, &alpha, &inst),
                    Expr::apps(
                        konst("Setoid.iseqv", vec![u_level.clone()]),
                        [alpha.clone(), inst.clone()],
                    ),
                    a.clone(),
                    bb.clone(),
                    h,
                ],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, hyp, body);
            let e = b.mk_lam(b_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, setoid_alpha, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string("Setoid.symm"),
            level_params: vec![u.clone()],
            type_: symm_type,
            value: symm_value,
        })?;

        // Setoid.trans : ∀ {α} [inst] {a b c : α}, a ≈ b → b ≈ c → a ≈ c
        let trans_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (inst_id, inst) = b.fresh_local(setoid_alpha.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (b_id, bb) = b.fresh_local(alpha.clone());
            let (c_id, cc) = b.fresh_local(alpha.clone());
            let equiv = setoid_equiv_head(&u_level, &alpha, &inst);
            let hyp1 = Expr::apps(equiv.clone(), [a.clone(), bb.clone()]);
            let hyp2 = Expr::apps(equiv.clone(), [bb.clone(), cc.clone()]);
            let concl = Expr::apps(equiv, [a.clone(), cc.clone()]);
            let e = Expr::pi(
                BinderInfo::Default,
                hyp1,
                Expr::pi(BinderInfo::Default, hyp2, concl),
            );
            let e = b.mk_pi(c_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_pi(b_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_pi(inst_id, BinderInfo::InstImplicit, setoid_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        let trans_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (inst_id, inst) = b.fresh_local(setoid_alpha.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (b_id, bb) = b.fresh_local(alpha.clone());
            let (c_id, cc) = b.fresh_local(alpha.clone());
            let equiv = setoid_equiv_head(&u_level, &alpha, &inst);
            let hyp1 = Expr::apps(equiv.clone(), [a.clone(), bb.clone()]);
            let hyp2 = Expr::apps(equiv, [bb.clone(), cc.clone()]);
            let (h1_id, h1) = b.fresh_local(hyp1.clone());
            let (h2_id, h2) = b.fresh_local(hyp2.clone());
            let body = Expr::apps(
                konst("Equivalence.trans", vec![u_level.clone()]),
                [
                    alpha.clone(),
                    setoid_r_app(&u_level, &alpha, &inst),
                    Expr::apps(
                        konst("Setoid.iseqv", vec![u_level.clone()]),
                        [alpha.clone(), inst.clone()],
                    ),
                    a.clone(),
                    bb.clone(),
                    cc.clone(),
                    h1,
                    h2,
                ],
            );
            let e = b.mk_lam(h2_id, BinderInfo::Default, hyp2, body);
            let e = b.mk_lam(h1_id, BinderInfo::Default, hyp1, e);
            let e = b.mk_lam(c_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_lam(b_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_lam(inst_id, BinderInfo::InstImplicit, setoid_alpha, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string("Setoid.trans"),
            level_params: vec![u],
            type_: trans_type,
            value: trans_value,
        })?;

        Ok(())
    }

    /// `Quot.liftOn` and `Quot.inductionOn` — the two `Quot` companions the
    /// `Quotient` cluster is defined in terms of (`Init/Core.lean:1817`,
    /// `1822`).
    ///
    /// Elaborated forms (Lean 4.30 `#print`):
    /// ```text
    /// @[reducible] protected def Quot.liftOn.{u, v} :
    ///   {α : Sort u} → {β : Sort v} → {r : α → α → Prop} →
    ///   @Quot.{u} α r → (f : α → β) →
    ///   (∀ (a b : α), r a b → @Eq.{v} β (f a) (f b)) → β :=
    ///   fun {α} {β} {r} q f c => @Quot.lift.{u, v} α r β f c q
    ///
    /// protected theorem Quot.inductionOn.{u} :
    ///   ∀ {α : Sort u} {r : α → α → Prop} {motive : @Quot.{u} α r → Prop}
    ///     (q : @Quot.{u} α r), (∀ (a : α), motive (@Quot.mk.{u} α r a)) → motive q :=
    ///   fun {α} {r} {motive} q h => @Quot.ind.{u} α r motive h q
    /// ```
    ///
    /// Watch the binder ORDER on `Quot.liftOn`: `{α} {β} {r}` — `β` comes
    /// BEFORE `r`, unlike the primitive `Quot.lift`, whose telescope is
    /// `{α} {r} {β}`.
    fn init_quot_companions(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let sort_u = Expr::sort(u_level.clone());
        let sort_v = Expr::sort(v_level.clone());
        let quot = |alpha: &Expr, r: &Expr| {
            Expr::apps(
                Expr::const_(quot_names::QUOT.clone(), vec![u_level.clone()]),
                [alpha.clone(), r.clone()],
            )
        };

        // Quot.liftOn : {α : Sort u} → {β : Sort v} → {r : α → α → Prop} →
        //   Quot α r → (f : α → β) → (∀ a b, r a b → f a = f b) → β
        let lift_on_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let rel = rel_type(&alpha);
            let (r_id, r) = b.fresh_local(rel.clone());
            let quot_ar = quot(&alpha, &r);
            let (q_id, _q) = b.fresh_local(quot_ar.clone());
            let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let c_ty = respect_obligation(&b, &v_level, &alpha, &beta, &r, &f);
            let (c_id, _c) = b.fresh_local(c_ty.clone());

            let e = beta.clone();
            let e = b.mk_pi(c_id, BinderInfo::Default, c_ty, e);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_pi(q_id, BinderInfo::Default, quot_ar, e);
            let e = b.mk_pi(r_id, BinderInfo::Implicit, rel, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        // value: fun {α} {β} {r} q f c => @Quot.lift.{u,v} α r β f c q
        let lift_on_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let rel = rel_type(&alpha);
            let (r_id, r) = b.fresh_local(rel.clone());
            let quot_ar = quot(&alpha, &r);
            let (q_id, q) = b.fresh_local(quot_ar.clone());
            let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let c_ty = respect_obligation(&b, &v_level, &alpha, &beta, &r, &f);
            let (c_id, c) = b.fresh_local(c_ty.clone());

            let body = Expr::apps(
                Expr::const_(
                    quot_names::QUOT_LIFT.clone(),
                    vec![u_level.clone(), v_level.clone()],
                ),
                [alpha.clone(), r.clone(), beta.clone(), f.clone(), c, q],
            );
            let e = b.mk_lam(c_id, BinderInfo::Default, c_ty, body);
            let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_lam(q_id, BinderInfo::Default, quot_ar, e);
            let e = b.mk_lam(r_id, BinderInfo::Implicit, rel, e);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Quot.liftOn"),
            level_params: vec![u.clone(), v],
            type_: lift_on_type,
            value: lift_on_value,
            is_reducible: true,
        })?;

        // Quot.inductionOn : ∀ {α} {r} {motive : Quot α r → Prop} (q : Quot α r),
        //   (∀ a, motive (Quot.mk α r a)) → motive q
        let motive_type =
            |quot_ar: &Expr| Expr::pi(BinderInfo::Default, quot_ar.clone(), Expr::prop());

        let induction_on_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let rel = rel_type(&alpha);
            let (r_id, r) = b.fresh_local(rel.clone());
            let quot_ar = quot(&alpha, &r);
            let motive_ty = motive_type(&quot_ar);
            let (motive_id, motive) = b.fresh_local(motive_ty.clone());
            let (q_id, q) = b.fresh_local(quot_ar.clone());

            // h : (a : α) → motive (Quot.mk α r a)
            let h_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(alpha.clone());
                let mk_a = Expr::apps(
                    Expr::const_(quot_names::QUOT_MK.clone(), vec![u_level.clone()]),
                    [alpha.clone(), r.clone(), a],
                );
                let body = Expr::app(motive.clone(), mk_a);
                let e = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body);
                c.finish_child(e)
            };
            let (h_id, _h) = b.fresh_local(h_ty.clone());

            let e = Expr::app(motive.clone(), q);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, e);
            let e = b.mk_pi(q_id, BinderInfo::Default, quot_ar, e);
            let e = b.mk_pi(motive_id, BinderInfo::Implicit, motive_ty, e);
            let e = b.mk_pi(r_id, BinderInfo::Implicit, rel, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        // value: fun {α} {r} {motive} q h => @Quot.ind.{u} α r motive h q
        let induction_on_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let rel = rel_type(&alpha);
            let (r_id, r) = b.fresh_local(rel.clone());
            let quot_ar = quot(&alpha, &r);
            let motive_ty = motive_type(&quot_ar);
            let (motive_id, motive) = b.fresh_local(motive_ty.clone());
            let (q_id, q) = b.fresh_local(quot_ar.clone());
            let h_ty = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (a_id, a) = c.fresh_local(alpha.clone());
                let mk_a = Expr::apps(
                    Expr::const_(quot_names::QUOT_MK.clone(), vec![u_level.clone()]),
                    [alpha.clone(), r.clone(), a],
                );
                let body = Expr::app(motive.clone(), mk_a);
                let e = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body);
                c.finish_child(e)
            };
            let (h_id, h) = b.fresh_local(h_ty.clone());

            let body = Expr::apps(
                Expr::const_(quot_names::QUOT_IND.clone(), vec![u_level.clone()]),
                [alpha.clone(), r.clone(), motive.clone(), h, q],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let e = b.mk_lam(q_id, BinderInfo::Default, quot_ar, e);
            let e = b.mk_lam(motive_id, BinderInfo::Implicit, motive_ty, e);
            let e = b.mk_lam(r_id, BinderInfo::Implicit, rel, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string("Quot.inductionOn"),
            level_params: vec![u],
            type_: induction_on_type,
            value: induction_on_value,
        })?;

        Ok(())
    }

    /// The `Quotient` cluster (`Init/Core.lean:1955`-`2040`).
    ///
    /// Elaborated forms (Lean 4.30 `#print`, `pp.explicit`/`pp.universes`):
    /// ```text
    /// def Quotient.{u} : {α : Sort u} → Setoid.{u} α → Sort u :=
    ///   fun {α} s => @Quot.{u} α (@Setoid.r.{u} α s)
    ///
    /// protected def Quotient.mk.{u} : {α : Sort u} → (s : Setoid.{u} α) → α → @Quotient.{u} α s :=
    ///   fun {α} s a => @Quot.mk.{u} α (@Setoid.r.{u} α s) a
    ///
    /// protected def Quotient.mk'.{u} : {α : Sort u} → [s : Setoid.{u} α] → α → @Quotient.{u} α s :=
    ///   fun {α} [s] a => @Quotient.mk.{u} α s a
    ///
    /// theorem Quotient.sound.{u} : ∀ {α} {s} {a b : α}, a ≈ b →
    ///   @Eq.{u} (@Quotient.{u} α s) (@Quotient.mk.{u} α s a) (@Quotient.mk.{u} α s b) :=
    ///   fun {α} {s} {a b} =>
    ///     @Quot.sound.{u} α (@HasEquiv.Equiv.{u,0} α (@instHasEquivOfSetoid.{u} α s)) a b
    ///
    /// @[reducible] protected def Quotient.lift.{u, v} := fun {α} {β} {s} f =>
    ///   @Quot.lift.{u, v} α (@HasEquiv.Equiv.{u,0} α (@instHasEquivOfSetoid.{u} α s)) β f
    ///
    /// protected theorem Quotient.ind.{u} := fun {α} {s} {motive} =>
    ///   @Quot.ind.{u} α (@Setoid.r.{u} α s) motive
    ///
    /// @[reducible] protected def Quotient.liftOn.{u, v} := fun {α} {β} {s} q f c =>
    ///   @Quot.liftOn.{u, v} α β (@Setoid.r.{u} α s) q f c
    ///
    /// protected theorem Quotient.inductionOn.{u} := fun {α} {s} {motive} q h =>
    ///   @Quot.inductionOn.{u} α (@Setoid.r.{u} α s) (fun x => motive x) q h
    /// ```
    ///
    /// Two shape traps, both Lean-verified:
    /// * `Quotient.mk` takes the setoid EXPLICITLY, `Quotient.mk'` takes it
    ///   INSTANCE-IMPLICITLY — they are different declarations, not aliases.
    /// * `Quotient.ind` takes the motive-hypothesis FIRST and the quotient
    ///   value LAST; `Quotient.inductionOn` takes `q` FIRST. Getting these
    ///   backwards silently breaks `induction … using Quotient.ind`.
    ///
    /// `Quotient.lift`/`.sound` spell the relation as
    /// `HasEquiv.Equiv α (instHasEquivOfSetoid α s)` while
    /// `Quotient.ind`/`.liftOn`/`.inductionOn` spell it `Setoid.r α s`. That
    /// asymmetry is Lean's, reproduced verbatim; the two are definitionally
    /// equal (δ on the instance + structure projection).
    fn init_quotient_family(&mut self) -> Result<(), EnvError> {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let sort_u = Expr::sort(u_level.clone());
        let sort_v = Expr::sort(v_level.clone());
        let setoid =
            |alpha: &Expr| Expr::app(konst("Setoid", vec![u_level.clone()]), alpha.clone());

        // Quotient : {α : Sort u} → Setoid α → Sort u
        //          := fun {α} s => @Quot α (@Setoid.r α s)
        let quotient_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, _s) = b.fresh_local(setoid_alpha.clone());
            let e = sort_u.clone();
            let e = b.mk_pi(s_id, BinderInfo::Default, setoid_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        let quotient_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let body = Expr::apps(
                Expr::const_(quot_names::QUOT.clone(), vec![u_level.clone()]),
                [alpha.clone(), setoid_r_app(&u_level, &alpha, &s)],
            );
            let e = b.mk_lam(s_id, BinderInfo::Default, setoid_alpha, body);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Quotient"),
            level_params: vec![u.clone()],
            type_: quotient_type,
            value: quotient_value,
            is_reducible: false,
        })?;

        // Quotient.mk : {α : Sort u} → (s : Setoid α) → α → Quotient α s
        //             := fun {α} s a => @Quot.mk α (@Setoid.r α s) a
        let mk_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let e = quotient_app(&u_level, &alpha, &s);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::Default, setoid_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        let mk_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let body = Expr::apps(
                Expr::const_(quot_names::QUOT_MK.clone(), vec![u_level.clone()]),
                [alpha.clone(), setoid_r_app(&u_level, &alpha, &s), a],
            );
            let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_lam(s_id, BinderInfo::Default, setoid_alpha, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Quotient.mk"),
            level_params: vec![u.clone()],
            type_: mk_type,
            value: mk_value,
            is_reducible: false,
        })?;

        // Quotient.mk' : {α : Sort u} → [s : Setoid α] → α → Quotient α s
        //              := fun {α} [s] a => @Quotient.mk α s a
        let mk_prime_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let (a_id, _a) = b.fresh_local(alpha.clone());
            let e = quotient_app(&u_level, &alpha, &s);
            let e = b.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::InstImplicit, setoid_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        let mk_prime_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let body = quotient_mk_app(&u_level, &alpha, &s, a);
            let e = b.mk_lam(a_id, BinderInfo::Default, alpha.clone(), body);
            let e = b.mk_lam(s_id, BinderInfo::InstImplicit, setoid_alpha, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Quotient.mk'"),
            level_params: vec![u.clone()],
            type_: mk_prime_type,
            value: mk_prime_value,
            is_reducible: false,
        })?;

        // Quotient.sound : ∀ {α} {s} {a b : α}, a ≈ b →
        //   @Eq.{u} (Quotient α s) (Quotient.mk α s a) (Quotient.mk α s b)
        //   := fun {α} {s} {a b} => @Quot.sound α (a ≈ ·) a b
        let sound_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (b_id, bb) = b.fresh_local(alpha.clone());
            let hyp = Expr::apps(
                setoid_equiv_head(&u_level, &alpha, &s),
                [a.clone(), bb.clone()],
            );
            let concl = eq_at(
                &u_level,
                &quotient_app(&u_level, &alpha, &s),
                quotient_mk_app(&u_level, &alpha, &s, a.clone()),
                quotient_mk_app(&u_level, &alpha, &s, bb.clone()),
            );
            let e = Expr::pi(BinderInfo::Default, hyp, concl);
            let e = b.mk_pi(b_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_pi(a_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_pi(s_id, BinderInfo::Implicit, setoid_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        let sound_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let (a_id, a) = b.fresh_local(alpha.clone());
            let (b_id, bb) = b.fresh_local(alpha.clone());
            // Partially applied (α, r, a, b) — the `h` argument is left to the
            // caller, exactly as Lean stores it.
            let body = Expr::apps(
                Expr::const_(quot_names::QUOT_SOUND.clone(), vec![u_level.clone()]),
                [
                    alpha.clone(),
                    setoid_equiv_head(&u_level, &alpha, &s),
                    a.clone(),
                    bb.clone(),
                ],
            );
            let e = b.mk_lam(b_id, BinderInfo::Implicit, alpha.clone(), body);
            let e = b.mk_lam(a_id, BinderInfo::Implicit, alpha.clone(), e);
            let e = b.mk_lam(s_id, BinderInfo::Implicit, setoid_alpha, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string("Quotient.sound"),
            level_params: vec![u.clone()],
            type_: sound_type,
            value: sound_value,
        })?;

        // Quotient.lift : {α} → {β : Sort v} → {s : Setoid α} → (f : α → β) →
        //   (∀ a b, a ≈ b → f a = f b) → Quotient α s → β
        //   := fun {α} {β} {s} f => @Quot.lift α (a ≈ ·) β f
        let lift_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let equiv = setoid_equiv_head(&u_level, &alpha, &s);
            let h_ty = respect_obligation(&b, &v_level, &alpha, &beta, &equiv, &f);
            let (h_id, _h) = b.fresh_local(h_ty.clone());
            let (q_id, _q) = b.fresh_local(quotient_app(&u_level, &alpha, &s));

            let e = beta.clone();
            let e = b.mk_pi(
                q_id,
                BinderInfo::Default,
                quotient_app(&u_level, &alpha, &s),
                e,
            );
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, e);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_pi(s_id, BinderInfo::Implicit, setoid_alpha, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        let lift_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            // Partially applied (α, r, β, f) — `h` and `q` are left to the
            // caller, exactly as Lean stores it.
            let body = Expr::apps(
                Expr::const_(
                    quot_names::QUOT_LIFT.clone(),
                    vec![u_level.clone(), v_level.clone()],
                ),
                [
                    alpha.clone(),
                    setoid_equiv_head(&u_level, &alpha, &s),
                    beta.clone(),
                    f.clone(),
                ],
            );
            let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, body);
            let e = b.mk_lam(s_id, BinderInfo::Implicit, setoid_alpha, e);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Quotient.lift"),
            level_params: vec![u.clone(), v.clone()],
            type_: lift_type,
            value: lift_value,
            is_reducible: true,
        })?;

        // Quotient.ind : ∀ {α} {s} {motive : Quotient α s → Prop},
        //   ((a : α) → motive (Quotient.mk α s a)) → (q : Quotient α s) → motive q
        //   := fun {α} {s} {motive} => @Quot.ind α (@Setoid.r α s) motive
        //
        // NOTE the argument order: hypothesis FIRST, `q` LAST (the mirror of
        // `Quotient.inductionOn` below).
        let ind_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let quotient_as = quotient_app(&u_level, &alpha, &s);
            let motive_ty = Expr::pi(BinderInfo::Default, quotient_as.clone(), Expr::prop());
            let (motive_id, motive) = b.fresh_local(motive_ty.clone());
            let h_ty = motive_hypothesis(&b, &u_level, &alpha, &s, &motive);
            let (h_id, _h) = b.fresh_local(h_ty.clone());
            let (q_id, q) = b.fresh_local(quotient_as.clone());

            let e = Expr::app(motive.clone(), q);
            let e = b.mk_pi(q_id, BinderInfo::Default, quotient_as, e);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, e);
            let e = b.mk_pi(motive_id, BinderInfo::Implicit, motive_ty, e);
            let e = b.mk_pi(s_id, BinderInfo::Implicit, setoid_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        let ind_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let quotient_as = quotient_app(&u_level, &alpha, &s);
            let motive_ty = Expr::pi(BinderInfo::Default, quotient_as, Expr::prop());
            let (motive_id, motive) = b.fresh_local(motive_ty.clone());
            let body = Expr::apps(
                Expr::const_(quot_names::QUOT_IND.clone(), vec![u_level.clone()]),
                [
                    alpha.clone(),
                    setoid_r_app(&u_level, &alpha, &s),
                    motive.clone(),
                ],
            );
            let e = b.mk_lam(motive_id, BinderInfo::Implicit, motive_ty, body);
            let e = b.mk_lam(s_id, BinderInfo::Implicit, setoid_alpha, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string("Quotient.ind"),
            level_params: vec![u.clone()],
            type_: ind_type,
            value: ind_value,
        })?;

        // Quotient.liftOn : {α} → {β : Sort v} → {s} → (q : Quotient α s) →
        //   (f : α → β) → (c : ∀ a b, a ≈ b → f a = f b) → β
        //   := fun {α} {β} {s} q f c => @Quot.liftOn α β (@Setoid.r α s) q f c
        let lift_on_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let quotient_as = quotient_app(&u_level, &alpha, &s);
            let (q_id, _q) = b.fresh_local(quotient_as.clone());
            let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let equiv = setoid_equiv_head(&u_level, &alpha, &s);
            let c_ty = respect_obligation(&b, &v_level, &alpha, &beta, &equiv, &f);
            let (c_id, _c) = b.fresh_local(c_ty.clone());

            let e = beta.clone();
            let e = b.mk_pi(c_id, BinderInfo::Default, c_ty, e);
            let e = b.mk_pi(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_pi(q_id, BinderInfo::Default, quotient_as, e);
            let e = b.mk_pi(s_id, BinderInfo::Implicit, setoid_alpha, e);
            let e = b.mk_pi(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        let lift_on_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let (beta_id, beta) = b.fresh_local(sort_v.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let quotient_as = quotient_app(&u_level, &alpha, &s);
            let (q_id, q) = b.fresh_local(quotient_as.clone());
            let f_ty = Expr::pi(BinderInfo::Default, alpha.clone(), beta.clone());
            let (f_id, f) = b.fresh_local(f_ty.clone());
            let equiv = setoid_equiv_head(&u_level, &alpha, &s);
            let c_ty = respect_obligation(&b, &v_level, &alpha, &beta, &equiv, &f);
            let (c_id, c) = b.fresh_local(c_ty.clone());

            let body = Expr::apps(
                konst("Quot.liftOn", vec![u_level.clone(), v_level.clone()]),
                [
                    alpha.clone(),
                    beta.clone(),
                    setoid_r_app(&u_level, &alpha, &s),
                    q,
                    f.clone(),
                    c,
                ],
            );
            let e = b.mk_lam(c_id, BinderInfo::Default, c_ty, body);
            let e = b.mk_lam(f_id, BinderInfo::Default, f_ty, e);
            let e = b.mk_lam(q_id, BinderInfo::Default, quotient_as, e);
            let e = b.mk_lam(s_id, BinderInfo::Implicit, setoid_alpha, e);
            let e = b.mk_lam(beta_id, BinderInfo::Implicit, sort_v.clone(), e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Definition {
            name: Name::from_string("Quotient.liftOn"),
            level_params: vec![u.clone(), v],
            type_: lift_on_type,
            value: lift_on_value,
            is_reducible: true,
        })?;

        // Quotient.inductionOn : ∀ {α} {s} {motive : Quotient α s → Prop}
        //   (q : Quotient α s), ((a : α) → motive (Quotient.mk α s a)) → motive q
        //   := fun {α} {s} {motive} q h =>
        //        @Quot.inductionOn α (@Setoid.r α s) (fun x => motive x) q h
        //
        // NOTE: `q` comes FIRST here (it is `@[elab_as_elim]`), the mirror of
        // `Quotient.ind` above.
        let induction_on_type = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let quotient_as = quotient_app(&u_level, &alpha, &s);
            let motive_ty = Expr::pi(BinderInfo::Default, quotient_as.clone(), Expr::prop());
            let (motive_id, motive) = b.fresh_local(motive_ty.clone());
            let (q_id, q) = b.fresh_local(quotient_as.clone());
            let h_ty = motive_hypothesis(&b, &u_level, &alpha, &s, &motive);
            let (h_id, _h) = b.fresh_local(h_ty.clone());

            let e = Expr::app(motive.clone(), q);
            let e = b.mk_pi(h_id, BinderInfo::Default, h_ty, e);
            let e = b.mk_pi(q_id, BinderInfo::Default, quotient_as, e);
            let e = b.mk_pi(motive_id, BinderInfo::Implicit, motive_ty, e);
            let e = b.mk_pi(s_id, BinderInfo::Implicit, setoid_alpha, e);
            let e = b.mk_pi(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        let induction_on_value = {
            let mut b = EnvDeclBuilder::new();
            let (alpha_id, alpha) = b.fresh_local(sort_u.clone());
            let setoid_alpha = setoid(&alpha);
            let (s_id, s) = b.fresh_local(setoid_alpha.clone());
            let quotient_as = quotient_app(&u_level, &alpha, &s);
            let motive_ty = Expr::pi(BinderInfo::Default, quotient_as.clone(), Expr::prop());
            let (motive_id, motive) = b.fresh_local(motive_ty.clone());
            let (q_id, q) = b.fresh_local(quotient_as.clone());
            let h_ty = motive_hypothesis(&b, &u_level, &alpha, &s, &motive);
            let (h_id, h) = b.fresh_local(h_ty.clone());

            // Lean stores the motive η-EXPANDED here (`fun x => motive x`);
            // reproduced verbatim so the `.olean` importer's name-dedup cannot
            // shadow the genuine declaration with a differently-spelled body.
            let motive_eta = {
                let mut c = EnvDeclBuilder::child_of(&b);
                let (x_id, x) = c.fresh_local(quotient_as.clone());
                let body = Expr::app(motive.clone(), x);
                let e = c.mk_lam(x_id, BinderInfo::Default, quotient_as.clone(), body);
                c.finish_child(e)
            };

            let body = Expr::apps(
                konst("Quot.inductionOn", vec![u_level.clone()]),
                [
                    alpha.clone(),
                    setoid_r_app(&u_level, &alpha, &s),
                    motive_eta,
                    q,
                    h,
                ],
            );
            let e = b.mk_lam(h_id, BinderInfo::Default, h_ty, body);
            let e = b.mk_lam(q_id, BinderInfo::Default, quotient_as, e);
            let e = b.mk_lam(motive_id, BinderInfo::Implicit, motive_ty, e);
            let e = b.mk_lam(s_id, BinderInfo::Implicit, setoid_alpha, e);
            let e = b.mk_lam(alpha_id, BinderInfo::Implicit, sort_u.clone(), e);
            b.finish(e)
        };
        self.add_decl_if_absent(Declaration::Theorem {
            name: Name::from_string("Quotient.inductionOn"),
            level_params: vec![u],
            type_: induction_on_type,
            value: induction_on_value,
        })?;

        Ok(())
    }
}

/// The three `Equivalence` field types over an already-allocated
/// `(α, r)` pair: `(refl, symm, trans)`.
///
/// * `refl  : ∀ (x : α), r x x`
/// * `symm  : ∀ {x y : α}, r x y → r y x`
/// * `trans : ∀ {x y z : α}, r x y → r y z → r x z`
///
/// Matching `Init/Core.lean:1313`/`1315`/`1317`: `refl`'s binder is EXPLICIT,
/// `symm`'s and `trans`'s are IMPLICIT.
fn equivalence_field_types(parent: &EnvDeclBuilder, alpha: &Expr, r: &Expr) -> (Expr, Expr, Expr) {
    let refl = {
        let mut c = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = c.fresh_local(alpha.clone());
        let body = Expr::apps(r.clone(), [x.clone(), x]);
        let e = c.mk_pi(x_id, BinderInfo::Default, alpha.clone(), body);
        c.finish_child(e)
    };

    let symm = {
        let mut c = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = c.fresh_local(alpha.clone());
        let (y_id, y) = c.fresh_local(alpha.clone());
        let hyp = Expr::apps(r.clone(), [x.clone(), y.clone()]);
        let concl = Expr::apps(r.clone(), [y.clone(), x.clone()]);
        let e = Expr::pi(BinderInfo::Default, hyp, concl);
        let e = c.mk_pi(y_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = c.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        c.finish_child(e)
    };

    let trans = {
        let mut c = EnvDeclBuilder::child_of(parent);
        let (x_id, x) = c.fresh_local(alpha.clone());
        let (y_id, y) = c.fresh_local(alpha.clone());
        let (z_id, z) = c.fresh_local(alpha.clone());
        let hyp1 = Expr::apps(r.clone(), [x.clone(), y.clone()]);
        let hyp2 = Expr::apps(r.clone(), [y.clone(), z.clone()]);
        let concl = Expr::apps(r.clone(), [x.clone(), z.clone()]);
        let e = Expr::pi(
            BinderInfo::Default,
            hyp1,
            Expr::pi(BinderInfo::Default, hyp2, concl),
        );
        let e = c.mk_pi(z_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = c.mk_pi(y_id, BinderInfo::Implicit, alpha.clone(), e);
        let e = c.mk_pi(x_id, BinderInfo::Implicit, alpha.clone(), e);
        c.finish_child(e)
    };

    (refl, symm, trans)
}

/// The lift respect-obligation `(a b : α) → rel a b → @Eq.{v} β (f a) (f b)`.
///
/// `rel` is the relation HEAD (already applied to its own parameters), so this
/// serves both the `Quot` spelling (`r`, a bare local) and the `Quotient`
/// spelling (`@HasEquiv.Equiv α (@instHasEquivOfSetoid α s)`).
fn respect_obligation(
    parent: &EnvDeclBuilder,
    v_level: &Level,
    alpha: &Expr,
    beta: &Expr,
    rel: &Expr,
    f: &Expr,
) -> Expr {
    let mut c = EnvDeclBuilder::child_of(parent);
    let (a_id, a) = c.fresh_local(alpha.clone());
    let (b_id, b) = c.fresh_local(alpha.clone());
    let hyp = Expr::apps(rel.clone(), [a.clone(), b.clone()]);
    let concl = eq_at(
        v_level,
        beta,
        Expr::app(f.clone(), a.clone()),
        Expr::app(f.clone(), b.clone()),
    );
    let e = Expr::pi(BinderInfo::Default, hyp, concl);
    let e = c.mk_pi(b_id, BinderInfo::Default, alpha.clone(), e);
    let e = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), e);
    c.finish_child(e)
}

/// The induction hypothesis `(a : α) → motive (@Quotient.mk.{u} α s a)`.
fn motive_hypothesis(
    parent: &EnvDeclBuilder,
    u_level: &Level,
    alpha: &Expr,
    s: &Expr,
    motive: &Expr,
) -> Expr {
    let mut c = EnvDeclBuilder::child_of(parent);
    let (a_id, a) = c.fresh_local(alpha.clone());
    let body = Expr::app(motive.clone(), quotient_mk_app(u_level, alpha, s, a));
    let e = c.mk_pi(a_id, BinderInfo::Default, alpha.clone(), body);
    c.finish_child(e)
}
