// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Application binders the way Lean's `ElabAppArgs` treats them.
//!
//! A strict-implicit `⦃x⦄` binder is filled only while explicit arguments
//! remain (`processStrictImplicitArg`, `Lean/Elab/App.lean:767-774`), even
//! after `whnfForall` has exposed it by unfolding a definition such as
//! `Function.Injective f := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂`; and a `fun`
//! value never has implicit arguments inserted into it. Measured on
//! `Mathlib/Logic/Function/Basic.lean` and `Mathlib/Data/Subtype.lean`
//! (`Function.Injective.comp_left`, `Subtype.val_injective`,
//! `Function.bijective_iff_existsUnique`, …): every shape came back as
//! `f ?a₁ = f ?a₂ → ?a₁ = ?a₂` against `Injective f`.
//!
//! Generalized field notation consumes a receiver's leading implicits before
//! it resolves the field (`consumeImplicits` + `resolveLValLoop`,
//! `Lean/Elab/App.lean:1512-1545`); see `FIELD_HEADER`. And the expected
//! type is propagated into an application before its explicit arguments
//! (`propagateExpectedType`, App.lean:414-458); see `PROPAGATE_HEADER`.
//!
//! Every fixture was ground-truthed on the pinned v4.30.0-rc2 `lean` binary
//! (2026-09-12/13): the accepted ones elaborate there as written, and each
//! fixture handed to `rejects` is refused there with a type mismatch.

use crate::elaborate_decl_and_register_with_warning;
use clean_kernel::Environment;
use clean_parser::parse_file;

fn elab(env: &mut Environment, src: &str) -> Option<String> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(env, d) {
            return Some(format!("{e:?}"));
        }
    }
    None
}

/// Definitions shared by the strict-implicit fixtures: `InjS` unfolds to a
/// `⦃⦄` Pi, `InjE` is the same with explicit binders (the control). Each
/// declaration is elaborated on its own here, so no `namespace`/`open`.
const STRICT_HEADER: &str = "\
def InjS {α β : Sort _} (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂\n\
def InjE {α β : Sort _} (f : α → β) : Prop := ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂\n\
def Involutive2 {α : Sort _} (f : α → α) : Prop := ∀ x, f (f x) = x\n\
axiom Involutive2.injective {α : Sort _} {f : α → α} (h : Involutive2 f) : InjS f\n\
structure Sub' (α : Type) (p : α → Prop) where\n\
\x20 val : α\n\
\x20 prop : p val\n\
axiom Sub'.ext' {α : Type} {p : α → Prop} : ∀ {a b : Sub' α p}, a.val = b.val → a = b\n\
axiom pimapS {ι : Sort _} {α β : ι → Sort _} {f : ∀ i, α i → β i}\n\
\x20   (hf : ∀ i, InjS (f i)) : InjS (fun (g : ∀ i, α i) i => f i (g i))\n\
axiom pimapE {ι : Sort _} {α β : ι → Sort _} {f : ∀ i, α i → β i}\n\
\x20   (hf : ∀ i, InjE (f i)) : InjE (fun (g : ∀ i, α i) i => f i (g i))\n\
theorem inj_of {α β : Sort _} (f : α → β) (h : InjS f) : InjS f := h\n\
theorem compS {α β γ : Sort _} {g : β → γ} {f : α → β} (hg : InjS g) (hf : InjS f) :\n\
\x20   InjS (fun x => g (f x)) := fun _ _ h => hf (hg h)\n\
axiom not_involutive2 : Involutive2 Not\n\
theorem coe_inj' {α : Type} {p : α → Prop} : InjS (fun (a : Sub' α p) => a.val) :=\n\
\x20 fun _ _ h => Sub'.ext' h\n";

fn accepts(decl: &str, why: &str) {
    let mut env = Environment::with_prelude();
    let src = format!("{STRICT_HEADER}{decl}");
    if let Some(e) = elab(&mut env, &src) {
        panic!("{why} (Lean accepts it): {e}");
    }
}

#[test]
fn test_strict_implicit_application_without_pending_argument_keeps_the_binder() {
    // `Function.Injective.comp_left` / `bijective_of_subsingleton` shape.
    accepts(
        "theorem a_app {α β : Sort _} (f : α → β) (h : InjS f) : InjS f := inj_of f h\n",
        "no argument follows the unfolded `⦃a₁ a₂⦄`, so it must stay a binder",
    );
}

#[test]
fn test_strict_implicit_bare_identifier_consumes_only_leading_implicits() {
    // `Subtype.val_injective := coe_injective` shape.
    accepts(
        "theorem a_ident {α : Type} {p : α → Prop} : InjS (fun (a : Sub' α p) => a.val) :=\n\
         \x20 coe_inj'\n",
        "the leading `{α} {p}` are filled and the `⦃⦄` tail is kept",
    );
}

#[test]
fn test_strict_implicit_field_notation_result_keeps_the_binder() {
    // `Function.not_injective`-style `h.injective` with nothing after it.
    accepts(
        "theorem a_field : InjS Not := not_involutive2.injective\n",
        "a field-notation result of `⦃⦄` type is not applied further",
    );
}

#[test]
fn test_strict_implicit_identifier_argument_keeps_the_binder() {
    // `Subtype.restrict_injective` / `map_injective` shape.
    accepts(
        "theorem a_arg {α β : Type} {f : α → β} (p : α → Prop) (h : InjS f) :\n\
         \x20   InjS (fun (a : Sub' α p) => f a.val) := compS h coe_inj'\n",
        "an identifier argument in an `InjS` slot keeps its `⦃⦄` binders",
    );
}

#[test]
fn test_strict_implicit_local_as_lambda_body_keeps_the_binder() {
    // `Function.Bijective.piMap` / `Injective.piMap` shape, with its control.
    accepts(
        "theorem a_lam {α β γ : Sort _} {g : β → γ} (hg : InjS g) :\n\
         \x20   InjS (fun (x : α → β) (a : α) => g (x a)) := pimapS fun _ => hg\n",
        "a local of `⦃⦄`-unfolding type as a lambda body is not applied",
    );
    accepts(
        "theorem a_lam_ctrl {α β γ : Sort _} {g : β → γ} (hg : InjE g) :\n\
         \x20   InjE (fun (x : α → β) (a : α) => g (x a)) := pimapE fun _ => hg\n",
        "the explicit-binder control",
    );
}

#[test]
fn test_fun_with_implicit_binders_checks_against_a_strict_pi() {
    // `Function.bijective_iff_existsUnique`: `fun {_a a'} h ↦ …` against
    // `Injective f`; binder annotations are not part of definitional equality.
    accepts(
        "theorem a_funimp {α β : Sort _} (f : α → β) (he : ∀ a a', f a = f a' → a = a') :\n\
         \x20   InjS f := fun {_a a'} h => he _ _ h\n",
        "a `fun {..}` value is not instantiated at its own implicit binders",
    );
    accepts(
        "theorem a_funimp_ctrl {α β : Sort _} (f : α → β) (he : ∀ a a', f a = f a' → a = a') :\n\
         \x20   InjS f := fun ⦃_a a'⦄ h => he _ _ h\n",
        "the same lambda spelled with `⦃⦄`",
    );
}

#[test]
fn test_strict_implicit_filled_when_an_explicit_argument_follows() {
    accepts(
        "theorem a_pending {α β : Sort _} (f : α → β) (hf : InjS f) (a b : α)\n\
         \x20   (h : f a = f b) : a = b := hf h\n",
        "an explicit argument after the unfolded `⦃a₁ a₂⦄` fills them",
    );
    accepts(
        "theorem a_pending_field {α : Sort _} (f : α → α) (hf : Involutive2 f) (a b : α)\n\
         \x20   (h : f a = f b) : a = b := hf.injective h\n",
        "the same through field notation",
    );
}

/// Shapes Lean rejects (`Type mismatch`), pinned so the stop rule does not
/// drift into accepting more than Lean does.
const REJECT_HEADER: &str =
    "def InjS {α β : Sort _} (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂\n\
     def SubS {α : Sort _} (s t : α → Prop) : Prop := ∀ ⦃a⦄, s a → t a\n";

fn rejects(decl: &str, why: &str) {
    let mut env = Environment::with_prelude();
    let src = format!("{REJECT_HEADER}{decl}");
    if elab(&mut env, &src).is_none() {
        panic!("{why} (Lean rejects it with a type mismatch)");
    }
}

#[test]
fn test_strict_implicit_bare_value_is_not_its_instantiated_body() {
    // `h : s ⊆ t` is not `a ∈ s → a ∈ t`: nothing fills `⦃a⦄` here.
    rejects(
        "theorem r_strict_body {α : Sort _} (s t : α → Prop) (h : SubS s t) (a : α) :\n\
         \x20   s a → t a := h\n",
        "a bare `⦃⦄`-typed value must not be instantiated to meet an arrow",
    );
}

#[test]
fn test_implicit_led_local_is_not_a_strict_pi() {
    rejects(
        "theorem r_implicit_local {α β : Sort _} (f : α → β)\n\
         \x20   (h : ∀ {a b : α}, f a = f b → a = b) : InjS f := h\n",
        "a `{}`-led local has its implicits filled, which then cannot meet `⦃⦄`",
    );
}

#[test]
fn test_fun_with_an_implicit_binder_is_not_applied_to_meet_an_arrow() {
    rejects(
        "def r_fun_implicit : Nat → Nat := fun {α : Type} (x : Nat) => x\n",
        "a `fun {α}` value keeps its binder, so it is not a `Nat → Nat`",
    );
}

/// Generalized field notation on a receiver whose type leads with implicit
/// binders (`Subtype.coe_inj`, `Subtype.coe_ne_coe`,
/// `Function.extend_val_apply`, `Function.extend_val_apply'` in
/// `Mathlib/Data/Subtype.lean`): Lean's `consumeImplicits` fills them without
/// unfolding anything, then `resolveLValAux` reads the consumed type's own
/// head (`C.field`), or `Function.field` for a `∀`, and unfolds one
/// definition at a time only on a miss.
const FIELD_HEADER: &str = "\
def Function.Injective' {α β : Sort _} (f : α → β) : Prop := ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂\n\
theorem Function.Injective'.eq_iff {α β : Sort _} {f : α → β} (I : Function.Injective' f)\n\
\x20   {a b : α} : f a = f b ↔ a = b := ⟨I a b, fun h => h ▸ rfl⟩\n\
axiom inj3 {α : Sort _} {p : α → Prop} : Function.Injective' (fun (a : Subtype p) => a.val)\n\
def Function.twice' {α : Sort _} (f : α → α) (x : α) : α := f (f x)\n\
def idd {α : Type} (x : α) : α := x\n\
axiom Function.extend' {α β γ : Sort _} (f : α → β) (g : α → γ) (j : β → γ) : β → γ\n\
axiom Function.extend'_def {α β γ : Sort _} (f : α → β) (g : α → γ) (j : β → γ) (b : β) :\n\
\x20 Function.extend' f g j b = j b\n\
structure Bar (α : Type) where\n\
\x20 x : α\n\
def Foo (α : Type) : Type := Bar α\n\
def Foo.tag {α : Type} (_ : Foo α) : α → α := fun a => a\n\
def Bar.tag {α : Type} (_ : Bar α) : α → Bool := fun _ => true\n\
def Bar.pick {α : Type} (_ : Bar α) : α → α := fun a => a\n\
axiom mkFoo {α : Type} : Foo α\n";

fn field_accepts(decl: &str, why: &str) {
    let mut env = Environment::with_prelude();
    let src = format!("{FIELD_HEADER}{decl}");
    if let Some(e) = elab(&mut env, &src) {
        panic!("{why} (Lean accepts it): {e}");
    }
}

#[test]
fn test_field_notation_resolves_on_the_head_of_the_consumed_receiver_type() {
    // `Subtype.coe_inj := coe_injective.eq_iff`.
    field_accepts(
        "theorem coe_inj_row {α : Sort _} {p : α → Prop} {a b : Subtype p} :\n\
         \x20   a.val = b.val ↔ a = b := inj3.eq_iff\n",
        "`inj3.eq_iff` is `Function.Injective'.eq_iff` once `{α} {p}` are filled",
    );
    field_accepts(
        "theorem coe_inj_ctl {α : Sort _} {p : α → Prop} {a b : Subtype p} :\n\
         \x20   a.val = b.val ↔ a = b := (@inj3 α p).eq_iff\n",
        "the control with the implicits supplied",
    );
}

#[test]
fn test_field_notation_on_an_implicit_led_function_uses_the_function_namespace() {
    // `Function.extend_val_apply`: `val.extend g j b`.
    field_accepts(
        "theorem ev_row {β γ : Sort _} {p : β → Prop} (g : {x // p x} → γ) (j : β → γ) (b : β) :\n\
         \x20   Subtype.val.extend' g j b = j b := Function.extend'_def _ _ _ _\n",
        "`Subtype.val` consumed to `Subtype ?p → ?α` names `Function.extend'`",
    );
    field_accepts(
        "theorem fn_ns_row : idd.twice' 0 = 0 := rfl\n",
        "`idd` consumed to `?α → ?α` names `Function.twice'`",
    );
    field_accepts(
        "theorem fn_ns_ctl1 (f : Nat → Nat) : f.twice' 0 = f (f 0) := rfl\n\
         theorem fn_ns_ctl2 : (@idd Nat).twice' 0 = 0 := rfl\n",
        "the explicit-arrow and pre-applied controls",
    );
}

#[test]
fn test_field_notation_prefers_the_unreduced_head_and_unfolds_only_on_a_miss() {
    // `Foo α := Bar α`: `Foo.tag` wins over `Bar.tag` (Clean used to reduce
    // first and pick `Bar.tag : … → Bool`); `Foo.pick` is absent, so one δ
    // step reaches `Bar.pick`.
    field_accepts(
        "theorem head_first (n : Nat) : mkFoo.tag n = n := rfl\n",
        "the consumed type's own head `Foo` names `Foo.tag`",
    );
    field_accepts(
        "theorem unfold_step (n : Nat) : mkFoo.pick n = n := rfl\n",
        "a miss on `Foo.pick` unfolds `Foo` to `Bar` and finds `Bar.pick`",
    );
}

/// Lean's `propagateExpectedType` (`Lean/Elab/App.lean:414-458`): before an
/// explicit argument is elaborated, a result type that does not depend on the
/// remaining arguments is unified with the expected type, so the arguments
/// meet slots it has already pinned. Shapes of `Function.Surjective.forall₂`,
/// `exists₂`, `injective_comp_right` (`Mathlib/Logic/Function/Basic.lean`),
/// `Subtype.coe_eq_of_eq_mk`, `Subtype.map_involutive`
/// (`Mathlib/Data/Subtype.lean`) and `eq_const_of_subsingleton`
/// (`Mathlib/Logic/Unique.lean`).
const PROPAGATE_HEADER: &str = "\
axiom funext2 {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x} (h : ∀ x, f x = g x) : f = g\n\
axiom congr_fun2 {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x} (h : f = g) (a : α) :\n\
\x20 f a = g a\n\
axiom sselim {α : Sort _} (a b : α) : a = b\n\
axiom Subtype.ext2 {α : Sort u} {p : α → Prop} :\n\
\x20 ∀ {a1 a2 : {x // p x}}, Subtype.val a1 = Subtype.val a2 → a1 = a2\n\
axiom iff_trans2 {a b c : Prop} (h1 : a ↔ b) (h2 : b ↔ c) : a ↔ c\n\
axiom forall_congr2 {α : Sort _} {p q : α → Prop} (h : ∀ a, p a ↔ q a) : (∀ a, p a) ↔ ∀ a, q a\n\
def Surjective2 {α β : Sort _} (f : α → β) : Prop := ∀ b, ∃ a, f a = b\n\
def InjS2 {α β : Sort _} (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂\n\
axiom Surjective2.forall' {α β : Sort _} {f : α → β} (hf : Surjective2 f) {p : β → Prop} :\n\
\x20   (∀ y, p y) ↔ ∀ x, p (f x)\n\
def Subtype.map2 {α β : Sort _} {p : α → Prop} {q : β → Prop} (f : α → β)\n\
\x20   (h : ∀ a, p a → q (f a)) : Subtype p → Subtype q := fun x => ⟨f x.val, h x.val x.property⟩\n\
def Involutive2 {α : Sort _} (f : α → α) : Prop := ∀ x, f (f x) = x\n";

fn propagate_accepts(decl: &str, why: &str) {
    let mut env = Environment::with_prelude();
    let src = format!("{PROPAGATE_HEADER}{decl}");
    if let Some(e) = elab(&mut env, &src) {
        panic!("{why} (Lean accepts it): {e}");
    }
}

#[test]
fn test_expected_type_pins_funext_target_before_the_lambda() {
    // `eq_const_of_subsingleton`: the `▸` must meet `f x = (fun _ ↦ f a) x`,
    // not solve `?g := f` and return `f = f`.
    propagate_accepts(
        "theorem b38 {α β : Sort _} (f : α → β) (a : α) : f = (fun _ => f a) :=\n\
         \x20 funext2 fun x => sselim x a ▸ rfl\n",
        "`funext2`'s `?g` comes from the expected type before the lambda",
    );
    propagate_accepts(
        "theorem b38_ctrl {α β : Sort _} (f : α → β) (a : α) : f = (fun _ => f a) :=\n\
         \x20 funext2 (g := fun _ => f a) fun x => sselim x a ▸ rfl\n",
        "the control with `?g` pinned by hand",
    );
}

#[test]
fn test_expected_type_pins_subtype_ext_endpoints_before_the_argument() {
    // `Subtype.coe_eq_of_eq_mk` and `Subtype.map_involutive`.
    propagate_accepts(
        "theorem b33 {α : Sort _} {p : α → Prop} {a : { a // p a }} {b : α} (h : a.val = b) :\n\
         \x20   a = ⟨b, h ▸ a.2⟩ := Subtype.ext2 h\n",
        "`?a2 := ⟨b, _⟩` is known before `h : ↑a = b` is checked",
    );
    propagate_accepts(
        "theorem b37 {α : Sort _} {p : α → Prop} {f : α → α} (h : ∀ a, p a → p (f a))\n\
         \x20   (hf : Involutive2 f) : Involutive2 (Subtype.map2 f h) :=\n\
         \x20 fun x => Subtype.ext2 (hf x.val)\n",
        "both endpoints come from the lambda body's expected type",
    );
}

#[test]
fn test_expected_type_pins_the_outer_endpoints_of_a_transitivity_chain() {
    // `Function.Surjective.forall₂` / `exists₂`.
    propagate_accepts(
        "theorem b13 {α β : Sort _} {f : α → β} (hf : Surjective2 f) {p : β → β → Prop} :\n\
         \x20   (∀ y₁ y₂, p y₁ y₂) ↔ ∀ x₁ x₂, p (f x₁) (f x₂) :=\n\
         \x20 iff_trans2 (Surjective2.forall' hf) (forall_congr2 fun _ ↦ Surjective2.forall' hf)\n",
        "`iff_trans2`'s `?a`/`?c` are pinned before its arguments",
    );
}

#[test]
fn test_expected_type_propagates_at_the_argument_after_a_field_notation_head() {
    // `Function.Surjective.injective_comp_right`: `(hf.forall).2 <| …`
    // propagates over the type left once the receiver is applied.
    propagate_accepts(
        "theorem b15 {α β γ : Sort _} {f : α → β} (hf : Surjective2 f) :\n\
         \x20   InjS2 fun g : β → γ ↦ fun x => g (f x) :=\n\
         \x20 fun _ _ h ↦ funext2 <| (Surjective2.forall' hf).2 <| congr_fun2 h\n",
        "`Iff.mpr`'s proposition is pinned before `congr_fun2 h`",
    );
}

#[test]
fn test_expected_type_is_never_propagated_when_it_is_prop() {
    // Lean skips a literal `Prop` expected type (it is used as a "Bool"), so
    // `List.head! s` keeps its `Bool` carrier and is coerced afterwards.
    propagate_accepts(
        "theorem prop_excl (s : List Bool) (h : (List.head! s : Prop)) : True := True.intro\n",
        "`List.head!`'s carrier comes from `s`, not from the expected `Prop`",
    );
}

#[test]
fn test_expected_type_is_not_propagated_into_a_local_instance_out_param_result() {
    // Lean's `isNextOutParamOfLocalInstanceAndResult`: `myget`'s result `E`
    // is an `outParam` of its own `[GetE C E]`, so the instance fixes
    // `E := Nat` and the result is coerced to `Int` afterwards; propagating
    // `Int` first would search `GetE (List Nat) Int`.
    propagate_accepts(
        "class GetE (C : Type) (E : outParam Type) where\n\
         \x20 get : C → E\n\
         instance instGetEListNat : GetE (List Nat) Nat := ⟨fun _ => 0⟩\n\
         def myget {C : Type} {E : Type} [GetE C E] (c : C) : E := GetE.get c\n\
         def op_row (xs : List Nat) : Int := myget xs\n",
        "`myget`'s `outParam` result comes from the instance, not the expected type",
    );
}

#[test]
fn test_expected_universe_is_not_propagated_into_a_type_former() {
    // The codata seed's `isigmaStep` shape: propagating `Type (max u v)` into
    // `Sigma.{?u', ?v'}` split `max u v =?= max ?u' ?v'` componentwise
    // (`?v' := v`), where Lean postpones the level constraint.
    propagate_accepts(
        "def sigS.{u, v} {I : Type v} (A : I → Type u) (X : I → Type (max u v)) (i : I) :\n\
         \x20   Type (max u v) :=\n\
         \x20 Sigma (fun _ : A i => X i)\n",
        "`Sigma`'s universes come from its argument, not from a split `max`",
    );
    // `it_congr` / `icastB_comp`: the motive's body is elaborated under its
    // codomain `Sort ?u₁`, which its binder domain `B i h'` must not pin.
    propagate_accepts(
        "theorem motS.{u, v} {I : Type v} {A : I → Type u} {B : (i : I) → A i → Type u} {i : I}\n\
         \x20   {l h : A i} (e : l = h) (b : B i h) : B i h = B i h :=\n\
         \x20 @Eq.rec (A i) l (fun h' _ => ∀ _ : B i h', B i h' = B i h') (fun _ => rfl) h e b\n",
        "a binder domain does not pin the motive's result universe",
    );
}

/// A propagated slot is checked with the kernel's complete def-eq, as Lean's
/// `ensureHasType` checks it. `Eq.symm`'s slot is pinned to `rebox f n = f n`
/// before `h` is elaborated; `rebox f n` unfolds to the constructor
/// application `Box1.mk (f n).val`, equal to `f n` only by structure eta,
/// which the structural unifier cannot see (`Box1.mk =?= f`). The shape of
/// `ITreeEco.lean`'s `iVis_inj_k` (`reports/2026-10-18-ivis-inj-k-repro`),
/// red from e03668c7d until the argument check fell back to the kernel. The
/// `.{u}` keeps the rigid-congruence fast path out of it, as in `iVis_inj_k`.
const ETA_ARG_HEADER: &str = "\
structure Box1.{u} (α : Type u) where\n\
\x20 val : α\n\
def rebox.{u} {α : Type u} (f : Nat → Box1 α) (n : Nat) : Box1 α := ⟨(f n).val⟩\n";

#[test]
fn test_propagated_slot_accepts_an_argument_equal_to_it_by_structure_eta() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{ETA_ARG_HEADER}theorem rebox_symm.{{u}} {{α : Type u}} (f : Nat → Box1 α) (n : Nat)\n\
         \x20   (h : rebox f n = rebox f n) : f n = rebox f n :=\n\
         \x20 Eq.symm h\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`h` meets the propagated `rebox f n = f n` up to eta (Lean accepts it): {e}");
    }
    // Control, refused by Lean with "Application type mismatch": the slot is
    // `rebox f n = f n` and `rebox g n` is not `f n` by any reduction.
    let mut env = Environment::with_prelude();
    let src = format!(
        "{ETA_ARG_HEADER}theorem rebox_symm_bad.{{u}} {{α : Type u}} (f g : Nat → Box1 α) (n : Nat)\n\
         \x20   (h : rebox g n = rebox g n) : f n = rebox f n :=\n\
         \x20 Eq.symm h\n"
    );
    let e = elab(&mut env, &src).expect("`rebox g n` is not `f n`: Lean refuses it");
    assert!(
        e.contains("TypeMismatch"),
        "refused for the wrong reason: {e}"
    );
}

/// The same def-eq fallback, with no propagation involved: `takesEq f n`
/// pins the slot to `f n = f n` from its own binders, and `h : rebox f n =
/// f n` meets it only by structure eta. Lean accepts it; Clean refused it
/// ("cannot unify an application with a free variable") until the
/// explicit-argument check fell back to the elaborator's def-eq.
#[test]
fn test_explicit_argument_equal_to_its_slot_by_structure_eta_is_accepted() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{ETA_ARG_HEADER}def takesEq.{{u}} {{α : Type u}} (f : Nat → Box1 α) (n : Nat) (h : f n = f n) : Nat := 0\n\
         def useEta.{{u}} {{α : Type u}} (f : Nat → Box1 α) (n : Nat) (h : rebox f n = f n) : Nat :=\n\
         \x20 takesEq f n h\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("`rebox f n = f n` is `f n = f n` up to eta (Lean accepts it): {e}");
    }
}

/// The fallback's def-eq never assigns a RIGID universe parameter. Lean
/// refuses both with "Application type mismatch" (`PUnit.{u + 1}` is not
/// `PUnit.{1}`; `Type u` is not `Type`). Clean's level callback used to
/// record `u := 0` for the declared `u`, so the fallback answered `true`,
/// elaboration accepted, and only the kernel's re-check of the finished
/// declaration refused it ("Kernel check failed ... expected PUnit, got
/// PUnit"). The refusal must come from elaboration, as Lean's does.
#[test]
fn test_explicit_argument_check_never_assigns_a_rigid_universe_parameter() {
    for (what, src) in [
        (
            "PUnit.{u+1} against PUnit.{1}",
            "def takesP1 (x : PUnit.{1}) : Nat := 0\n\
             def useIt.{u} (y : PUnit.{u+1}) : Nat := takesP1 y\n",
        ),
        (
            "Sort (u+1) against Sort 1",
            "def takesS1 (x : Sort 1) : Nat := 0\n\
             def useS.{u} (y : Sort (u+1)) : Nat := takesS1 y\n",
        ),
    ] {
        let mut env = Environment::with_prelude();
        let e = elab(&mut env, src).unwrap_or_else(|| panic!("{what}: Lean refuses it"));
        assert!(
            e.contains("TypeMismatch") && !e.contains("Kernel"),
            "{what}: refused by the kernel's re-check, not by elaboration: {e}"
        );
    }
}

/// B14 holds at the fallback: an `@[irreducible]` definition stays folded,
/// so `h : foo = 1` does not meet `1 = 1` (Lean: "Application type
/// mismatch").
#[test]
fn test_explicit_argument_check_keeps_irreducible_definitions_folded() {
    let mut env = Environment::with_prelude();
    let src = "@[irreducible] def foo : Nat := 1\n\
               def takesEq (h : (1 : Nat) = 1) : Nat := 0\n\
               def useFoo (h : foo = 1) : Nat := takesEq h\n";
    let e = elab(&mut env, src).expect("`foo` is irreducible: Lean refuses `takesEq h`");
    assert!(
        e.contains("TypeMismatch"),
        "refused for the wrong reason: {e}"
    );
}

/// `rec_heq_of_heq` (`Mathlib/Logic/Basic.lean`): propagation alone is not
/// enough. The propagated constraint is
/// `@HEq (?motive ?a' ?e) (@Eq.rec ?α ?a ?motive ?x ?a' ?e) ?β ?y =?=
/// @HEq (C b) (e ▸ x) β y`, whose FIRST argument pair is an implicit,
/// non-pattern flex application that only the `Eq.rec` pair can solve
/// (`?motive := fun b _ => C b`). Lean's `isDefEqArgs` postpones implicit
/// arguments (`Lean/Meta/ExprDefEq.lean:301-359`); see
/// `unify/unifier/postponed_args.rs`.
const REC_HEQ_HEADER: &str = "\
axiom eqRec_heq_iff_heq' {α : Sort _} {a : α} {motive : (a' : α) → a = a' → Sort _}\n\
\x20   {x : motive a rfl} {a' : α} {e : a = a'} {β : Sort _} {y : β} :\n\
\x20   HEq (@Eq.rec α a motive x a' e) y ↔ HEq x y\n";

#[test]
fn test_stuck_implicit_argument_is_unified_after_the_explicit_ones() {
    let mut env = Environment::with_prelude();
    let src = format!(
        "{REC_HEQ_HEADER}\
         theorem rec_heq_of_heq' {{α β : Sort _}} {{a b : α}} {{C : α → Sort _}} {{x : C a}} {{y : β}}\n\
         \x20   (e : a = b) (h : HEq x y) : HEq (e ▸ x) y :=\n\
         \x20 eqRec_heq_iff_heq'.mpr h\n\
         theorem rec_heq_of_heq_ctl {{α β : Sort _}} {{a b : α}} {{C : α → Sort _}} {{x : C a}} {{y : β}}\n\
         \x20   (e : a = b) (h : HEq x y) : HEq (e ▸ x) y :=\n\
         \x20 (@eqRec_heq_iff_heq' α a (fun b _ => C b) x b e β y).mpr h\n"
    );
    if let Some(e) = elab(&mut env, &src) {
        panic!("the motive comes from the `Eq.rec` pair, not from `HEq`'s type argument (Lean accepts it): {e}");
    }
}

#[test]
fn test_stuck_implicit_postponement_does_not_accept_a_swapped_heq() {
    // Lean: "Application type mismatch: The argument h has type y ≍ x but is
    // expected to have type x ≍ y".
    let mut env = Environment::with_prelude();
    let src = format!(
        "{REC_HEQ_HEADER}\
         theorem rec_heq_bad {{α β : Sort _}} {{a b : α}} {{C : α → Sort _}} {{x : C a}} {{y : β}}\n\
         \x20   (e : a = b) (h : HEq y x) : HEq (e ▸ x) y :=\n\
         \x20 eqRec_heq_iff_heq'.mpr h\n"
    );
    let err = elab(&mut env, &src).expect("Lean rejects a swapped `HEq` hypothesis");
    assert!(
        err.contains("TypeMismatch"),
        "expected a type mismatch, got: {err}"
    );
}

/// Named arguments on a head that is not a declared constant with its own
/// binders: Lean matches `(x := e)` against the binder names of the head's
/// TYPE after `whnf` (`ElabAppArgs`, `Lean/Elab/App.lean:803-815`). For a
/// local `h : InjS f` those names exist only in `InjS`'s VALUE
/// (`Function.injective_comp_left_iff`, `Mathlib/Logic/Function/Basic.lean`:
/// "invalid named argument `(a₁ := …)` for `<non-constant function head>`").
const NAMED_HEADER: &str = "\
def InjS {α β : Sort _} (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂\n\
def Surj {α β : Sort _} (f : α → β) : Prop := ∀ b, ∃ a, f a = b\n\
def Rel2 (r : Nat → Nat → Prop) : Prop := ∀ {x y : Nat}, r x y → r y x\n\
abbrev InjS' {α β : Sort _} (f : α → β) : Prop := InjS f\n\
theorem inj_id : InjS (fun x : Nat => x) := fun _ _ h => h\n";

fn named(decl: &str) -> Option<String> {
    let mut env = Environment::with_prelude();
    elab(&mut env, &format!("{NAMED_HEADER}{decl}"))
}

fn named_accepts(decl: &str, why: &str) {
    if let Some(e) = named(decl) {
        panic!("{why} (Lean accepts it): {e}");
    }
}

#[test]
fn test_named_args_on_a_local_bind_by_the_names_in_its_types_definition() {
    named_accepts(
        "theorem n1 {α β : Type} (f : α → β) (h : InjS f) (x y : α) (e : f x = f y) : x = y :=\n\
         \x20 h (a₁ := x) (a₂ := y) e\n",
        "`a₁`/`a₂` are the `⦃⦄` binders of `InjS`'s value",
    );
    named_accepts(
        "theorem n4 {α β : Type} (f : α → β) (h : InjS f) (x y : α) (e : f x = f y) : x = y :=\n\
         \x20 h (a₂ := y) e\n",
        "an unnamed earlier `⦃⦄` binder is still filled by unification",
    );
    // The row itself: `h (a₁ := fun _ ↦ b₁) (a₂ := fun _ ↦ b₂) …`.
    named_accepts(
        "theorem n5 {α β γ : Type} [Nonempty α] {g : β → γ}\n\
         \x20   (h : InjS (fun (f : α → β) => fun x => g (f x)))\n\
         \x20   (b₁ b₂ : β) (eq : g b₁ = g b₂) (a : α) : b₁ = b₂ :=\n\
         \x20 congrFun (h (a₁ := fun _ => b₁) (a₂ := fun _ => b₂) (funext fun _ => eq)) a\n",
        "`Function.injective_comp_left_iff`'s named arguments on the local `h`",
    );
    named_accepts(
        "theorem c2 {α β : Type} (f : α → β) (h : Surj f) (y : β) : ∃ a, f a = y := h (b := y)\n",
        "an explicit `∀ b` binder is named too",
    );
    named_accepts(
        "theorem c3 (r : Nat → Nat → Prop) (h : Rel2 r) (a b : Nat) (hab : r a b) : r b a :=\n\
         \x20 h (y := b) (x := a) hab\n",
        "out-of-order names land in their own `{}` slots",
    );
}

#[test]
fn test_named_args_follow_a_chain_of_definitions_and_a_binderless_constant() {
    named_accepts(
        "theorem c4 {α β : Type} (f : α → β) (h : InjS' f) (x y : α) (e : f x = f y) : x = y :=\n\
         \x20 h (a₁ := x) (a₂ := y) e\n",
        "`InjS' f` unfolds to `InjS f` and then to the `∀` that carries the names",
    );
    named_accepts(
        "theorem c1 (x y : Nat) (e : x = y) : x = y := inj_id (a₁ := x) (a₂ := y) e\n",
        "a constant with no binders of its own is named through its type as well",
    );
}

#[test]
fn test_named_args_on_a_local_bind_by_name_not_by_position() {
    // Lean: "Application type mismatch: The argument e has type f x = f y but
    // is expected to have type f y = f x". Swapping the NAMES swaps the slots.
    let err = named(
        "theorem r3 {α β : Type} (f : α → β) (h : InjS f) (x y : α) (e : f x = f y) : x = y :=\n\
         \x20 h (a₁ := y) (a₂ := x) e\n",
    )
    .expect("swapped names must not check");
    assert!(err.contains("TypeMismatch"), "got: {err}");
    // Lean: "Invalid argument name `zz` for function".
    let err = named(
        "theorem r1 {α β : Type} (f : α → β) (h : InjS f) (x y : α) (e : f x = f y) : x = y :=\n\
         \x20 h (zz := x) (a₂ := y) e\n",
    )
    .expect("an unknown name must be refused");
    assert!(err.contains("unknown named argument"), "got: {err}");
    // Lean: "Argument `a₁` was already set".
    let err = named(
        "theorem r2 {α β : Type} (f : α → β) (h : InjS f) (x y : α) (e : f x = f y) : x = y :=\n\
         \x20 h (a₁ := x) (a₁ := y) e\n",
    )
    .expect("a name bound twice must be refused");
    assert!(err.contains("already bound"), "got: {err}");
}

#[test]
fn test_named_args_on_a_local_bind_by_the_names_of_a_forall_written_in_place() {
    // Lean reads the names off the local's own `∀` type
    // (`fType.bindingName!`, Lean/Elab/App.lean:803-815). Clean's kernel `Pi`
    // keeps none, so they are recorded where the surface binder becomes a
    // local (`ElabCtx::note_local_forall_binder_names`).
    named_accepts(
        "theorem n2 (h : ∀ {n m : Nat}, n = m → m = n) : 2 = 1 + 1 := h (n := 1 + 1) (m := 2) rfl\n",
        "a declaration binder whose type is a `∀` written in place",
    );
    named_accepts(
        "theorem n2b (h : ∀ {n m : Nat}, n = m → m = n) : 2 = 1 + 1 := h (m := 2) rfl\n",
        "an unnamed earlier `{}` binder is still filled by unification",
    );
    named_accepts(
        "theorem n2c (h : ∀ (n m : Nat), n = m → m = n) (e : 3 = 4) : 4 = 3 := h (m := 4) (n := 3) e\n",
        "out-of-order names land in their own explicit slots",
    );
    named_accepts(
        "theorem n2e (h : ∀ ⦃n m : Nat⦄, n = m → m = n) (a b : Nat) (e : a = b) : b = a := h (n := a) e\n",
        "a `⦃⦄` binder is named too",
    );
    named_accepts(
        "theorem n2d : (∀ {n m : Nat}, n = m → m = n) → 2 = 1 + 1 :=\n\
         \x20 fun (h : ∀ {n m : Nat}, n = m → m = n) => h (n := 1 + 1) (m := 2) rfl\n",
        "a `fun` binder with its type written",
    );
    named_accepts(
        "theorem n2f (a b : Nat) (e : a = b) : b = a :=\n\
         \x20 have h : ∀ {n m : Nat}, n = m → m = n := fun e => e.symm\n\
         \x20 h (n := a) (m := b) e\n",
        "a term-mode `have`",
    );
    named_accepts(
        "theorem n2g (h : ∀ {n m : Nat}, n = m → m = n) (a b : Nat) (e : a = b) : b = a := by\n\
         \x20 exact h (n := a) (m := b) e\n",
        "the declaration binder keeps its names inside a `by` block",
    );
    named_accepts(
        "theorem o2 (a b : Nat) (e : a = b) : b = a := by\n\
         \x20 have h : ∀ {n m : Nat}, n = m → m = n := fun e => e.symm\n\
         \x20 exact h (n := a) (m := b) e\n",
        "a tactic `have` with its type written",
    );
}

#[test]
fn test_named_args_on_a_local_forall_bind_by_name_not_by_position() {
    // Lean: "Application type mismatch: The argument e has type 3 = 4 but is
    // expected to have type 4 = 3". Swapping the NAMES swaps the slots.
    let err = named(
        "theorem r1 (h : ∀ (n m : Nat), n = m → m = n) (e : 3 = 4) : 4 = 3 := h (m := 3) (n := 4) e\n",
    )
    .expect("swapped names must not check");
    assert!(err.contains("TypeMismatch"), "got: {err}");
    // Lean: "Invalid argument name `zz` for function".
    let err =
        named("theorem r2 (h : ∀ {n m : Nat}, n = m → m = n) : 2 = 1 + 1 := h (zz := 1 + 1) rfl\n")
            .expect("an unknown name must be refused");
    assert!(err.contains("unknown named argument"), "got: {err}");
    // Lean: "Argument `n` was already set".
    let err = named(
        "theorem r3 (h : ∀ {n m : Nat}, n = m → m = n) : 2 = 1 + 1 := h (n := 1 + 1) (n := 2) rfl\n",
    )
    .expect("a name bound twice must be refused");
    assert!(err.contains("already bound"), "got: {err}");
}

#[test]
fn test_named_args_on_a_hypothesis_bind_by_the_names_the_statement_wrote() {
    // No binder of `h` spells its `∀`: the type comes from the goal (`intro`)
    // or from the expected type (`fun h =>`), and it IS a `∀` the statement
    // wrote. Lean keeps the names in the kernel term; Clean records every
    // surface `∀` beside the kernel `∀` it elaborated to
    // (`ElabCtx::note_surface_forall_binder_names`) and reads it back by type.
    named_accepts(
        "theorem o1 : (∀ {n m : Nat}, n = m → m = n) → 2 = 1 + 1 := by\n\
         \x20 intro h\n\
         \x20 exact h (n := 1 + 1) (m := 2) rfl\n",
        "a hypothesis `intro` took off the goal",
    );
    named_accepts(
        "theorem o3 : (∀ {n m : Nat}, n = m → m = n) → 2 = 1 + 1 :=\n\
         \x20 fun h => h (n := 1 + 1) (m := 2) rfl\n",
        "a `fun` binder typed by the expected type",
    );
    named_accepts(
        "theorem o5 (p : Nat → Nat → Prop) : (∀ x y, p x y) → p 1 2 := fun h => h (y := 2) (x := 1)\n",
        "explicit binders, out of order",
    );
    named_accepts(
        "theorem o6 (p : Nat → Nat → Prop) (hp : ∀ x y, p x y) : p 1 2 := by\n\
         \x20 have h := hp\n\
         \x20 exact h (y := 2) (x := 1)\n",
        "a `have` whose type is another local's written `∀`",
    );
    // `intro p` mints `p` at the goal's binder depth, which is the id the
    // statement's `∀ p` was elaborated under, so the hypothesis's type is the
    // recorded term here as well.
    named_accepts(
        "theorem o7 : ∀ (p : Nat → Nat → Prop), (∀ x y, p x y) → p 1 2 := by\n\
         \x20 intro p h\n\
         \x20 exact h (y := 2) (x := 1)\n",
        "a `∀` under a binder `intro` re-introduced",
    );
    // Lean: "Application type mismatch: The argument e has type 3 = 4 but is
    // expected to have type 4 = 3". Names select slots, never positions.
    let err = named(
        "theorem ro1 : (∀ (n m : Nat), n = m → m = n) → (3 = 4) → 4 = 3 := by\n\
         \x20 intro h e\n\
         \x20 exact h (m := 3) (n := 4) e\n",
    )
    .expect("swapped names must not check");
    assert!(err.contains("mismatch"), "got: {err}");
}

#[test]
fn test_named_args_on_a_hypothesis_whose_forall_names_are_not_known_are_still_refused() {
    // OPEN GAPS, pinned as refusals. Lean accepts both: the names are in
    // the kernel `∀`. Clean's kernel terms keep none, and the by-type record
    // cannot answer these, so each is refused LOUDLY, never bound by position.
    // The day one of them elaborates, its assertion fails and it becomes an
    // accept pin.
    for (decl, why) in [
        (
            // Two spellings of ONE kernel `∀` with different names: the record
            // is ambiguous, and picking either could bind the wrong slots.
            "theorem amb (h₁ : ∀ {n m : Nat}, n = m → m = n) :\n\
             \x20   (∀ {m n : Nat}, m = n → n = m) → 2 = 1 + 1 := by\n\
             \x20 intro h\n\
             \x20 exact h (m := 1 + 1) (n := 2) rfl\n",
            "ambiguous names for one kernel `∀`",
        ),
        (
            // The hypothesis's `∀` mentions the local `fun` bound for `p`,
            // which is not the local the statement's `∀` was elaborated
            // under, so it is not the recorded term.
            "theorem o8 : ∀ (p : Nat → Nat → Prop), (∀ x y, p x y) → p 1 2 :=\n\
             \x20 fun p h => h (y := 2) (x := 1)\n",
            "a `∀` under a binder `fun` re-introduced",
        ),
    ] {
        let err =
            named(decl).unwrap_or_else(|| panic!("{why}: now elaborates; make it an accept pin"));
        assert!(
            err.contains("invalid named argument") || err.contains("NamedArgBindingFailed"),
            "{why}: got: {err}"
        );
    }
}

/// The import side of the same table: a kernel definition with no surface
/// parameter table, the way the `.olean` loader leaves it, plus the recorded
/// shape of its value (`Environment::record_value_forall_binder_names`; the
/// loader's own reading of `Function.Injective` from the pinned toolchain is
/// pinned in `clean-olean`'s `tests_value_binder_names.rs`).
fn imported_inj(env: &mut Environment, recorded: bool) {
    use clean_kernel::{BinderInfo, Declaration, Expr, Level, Name};
    // def ImpInj : (Nat → Nat) → Prop := fun f => ∀ ⦃a₁ a₂ : Nat⦄, f a₁ = f a₂ → a₁ = a₂
    let nat = || Expr::const_(Name::from_string("Nat"), vec![]);
    let eq = |a: Expr, b: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat(), a, b],
        )
    };
    // Under `fun f`, `∀ a₁`, `∀ a₂`: f = bvar 2, a₁ = bvar 1, a₂ = bvar 0;
    // under the arrow's binder each index is one higher.
    let body = Expr::pi(
        BinderInfo::StrictImplicit,
        nat(),
        Expr::pi(
            BinderInfo::StrictImplicit,
            nat(),
            Expr::pi(
                BinderInfo::Default,
                eq(
                    Expr::app(Expr::bvar(2), Expr::bvar(1)),
                    Expr::app(Expr::bvar(2), Expr::bvar(0)),
                ),
                eq(Expr::bvar(2), Expr::bvar(1)),
            ),
        ),
    );
    let fn_ty = Expr::pi(BinderInfo::Default, nat(), nat());
    env.add_decl(Declaration::Definition {
        name: Name::from_string("ImpInj"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, fn_ty.clone(), Expr::prop()),
        value: Expr::lam(BinderInfo::Default, fn_ty, body),
        is_reducible: false,
    })
    .expect("def ImpInj");
    if recorded {
        env.record_value_forall_binder_names(
            Name::from_string("ImpInj"),
            1,
            vec![
                Name::from_string("a₁"),
                Name::from_string("a₂"),
                Name::anon(),
            ],
        );
    }
}

const IMPORTED_USE: &str =
    "theorem imp (f : Nat → Nat) (h : ImpInj f) (x y : Nat) (e : f x = f y) : x = y :=\n\
     \x20 h (a₂ := y) (a₁ := x) e\n";

#[test]
fn test_named_args_on_a_local_bind_by_an_imported_definitions_recorded_names() {
    let mut env = Environment::with_prelude();
    imported_inj(&mut env, true);
    if let Some(e) = elab(&mut env, IMPORTED_USE) {
        panic!("the recorded value names of `ImpInj` must bind the named arguments: {e}");
    }
}

#[test]
fn test_named_args_on_a_local_without_recorded_value_names_stay_refused() {
    let mut env = Environment::with_prelude();
    imported_inj(&mut env, false);
    let err = elab(&mut env, IMPORTED_USE).expect("no recorded names: the call must be refused");
    assert!(err.contains("binder names"), "got: {err}");
}
