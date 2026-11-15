// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `rw` on a goal whose target is not a proposition, a `dite` whose
//! condition is a hole, and a nested `open … in`. Lean's `rw` closes the
//! goal with `Eq.mpr (congrArg (fun x => G[x]) h) ?new` at any sort; Clean
//! built a `Prop`-only `Eq.subst` and the kernel refused the motive
//! (`expected ι → Prop, got ι → Sort ?u`: Mathlib's `uniqueElim`, measured
//! 2026-09-12). Every fixture was ground-truthed on the pinned v4.30.0-rc2
//! `lean` binary (all accepted).

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

#[test]
fn test_rw_sort_polymorphic_family_goal_elaborates() {
    let mut env = Environment::with_prelude();
    let src = "universe u v\n\
               class Unique' (α : Sort u) where\n\
               \x20 dflt : α\n\
               \x20 uniq : ∀ a : α, a = dflt\n\
               def uniqueElim' {ι : Sort u} {α : ι → Sort v} [Unique' ι]\n\
               \x20   (x : α (Unique'.dflt : ι)) (i : ι) : α i := by\n\
               \x20 rw [Unique'.uniq i]\n\
               \x20 exact x\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`rw` must rewrite a `Sort v`-valued goal through `Eq.mpr`: {e}");
    }
}

#[test]
fn test_rw_type_valued_goal_reverse_rule_elaborates() {
    let mut env = Environment::with_prelude();
    let src = "def castVec {n m : Nat} (h : n = m) (v : Fin n) : Fin m := by\n\
               \x20 rw [← h]\n\
               \x20 exact v\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`rw [← h]` must rewrite a `Type`-valued goal: {e}");
    }
}

#[test]
fn test_rw_prop_goal_keeps_working() {
    let mut env = Environment::with_prelude();
    let src = "theorem propCtl (a b : Nat) (h : a = b) (p : Nat → Prop) (hp : p a) : p b := by\n\
               \x20 rw [← h]\n\
               \x20 exact hp\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("the `Prop` path must be unchanged: {e}");
    }
}

/// `if h : _ then … else …`: the hole's type is a metavariable that only the
/// branches fix. Lean elaborates a `dite` condition against `Prop`, so the
/// hole is `?c : Prop` and `dif_pos' h` pins it to `P` (Mathlib's
/// `dite_eq_or_eq`; ground-truthed on the pinned lean with the two lemmas as
/// axioms, which is how they reach a prelude-only fixture).
#[test]
fn test_dite_hole_condition_is_a_prop_solved_by_the_branches() {
    let mut env = Environment::with_prelude();
    let src = "universe u\n\
               axiom dif_pos' {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α}\n\
               \x20   {e : ¬c → α} : dite c t e = t hc\n\
               axiom dif_neg' {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c → α}\n\
               \x20   {e : ¬c → α} : dite c t e = e hnc\n\
               theorem holeGuard (P : Prop) [Decidable P] (A : P → Nat) (B : ¬P → Nat) :\n\
               \x20   (∃ h, dite P A B = A h) ∨ ∃ h, dite P A B = B h :=\n\
               \x20 if h : _ then Or.inl ⟨h, dif_pos' h⟩ else Or.inr ⟨h, dif_neg' h⟩\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a hole `dite` condition must be a Prop the branches solve: {e}");
    }
}

/// `open X in e` nested in an application argument must survive the macro
/// roundtrip (`Function.extend_const`: `funext fun _ ↦ open scoped Classical
/// in ite_id _`); it used to come back as the identifier `openIn`.
#[test]
fn test_open_in_nested_in_an_argument_keeps_its_namespace() {
    let mut env = Environment::with_prelude();
    let src = "namespace Foo\n\
               theorem baz (n : Nat) : n = n := rfl\n\
               end Foo\n\
               theorem nestedOpenIn (f : Nat → Nat) : f = f := funext fun x => open Foo in baz (f x)\n\
               theorem nestedOpenInApp (a : Nat) : id (open Foo in baz a) = rfl := rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a nested `open … in` must elaborate with its namespace open: {e}");
    }
}

/// `intros a b` introduces exactly the named binders (Lean's `intros` takes
/// `(ident <|> hole)*`); as a nullary tactic its names were parsed as the next
/// tactics — "unknown tactic 'a'" (`Function.IsPartialInv.comp`). Parsed the
/// way `clean check` parses, with the builtin tactic patterns.
#[test]
fn test_intros_with_names_introduces_exactly_those() {
    use crate::tactic::builtins::builtin_tactic_patterns;
    use clean_parser::parse_file_with_tactics;
    let mut env = Environment::with_prelude();
    let src = "theorem introsNamed (p q : Prop) (hq : q) : p → q → q := by\n\
               \x20 intros a b\n\
               \x20 exact b\n\
               theorem introsBare (p q : Prop) : p → q → q := by\n\
               \x20 intros\n\
               \x20 assumption\n";
    let decls = parse_file_with_tactics(src, &builtin_tactic_patterns())
        .unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    for d in &decls {
        if let Err(e) = elaborate_decl_and_register_with_warning(&mut env, d) {
            panic!("`intros` with and without names must work as in Lean: {e:?}");
        }
    }
}

/// A CLASS's own field types may name its parents' fields bare, as a
/// structure's always could (`class C (α) extends P α where h : ∀ a, le a a`;
/// the class path prepends `toParent` as an ordinary field, so nothing bound
/// `le`). Ground-truthed on the pinned lean, parameterized and not.
#[test]
fn test_class_fields_name_inherited_parent_fields() {
    let mut env = Environment::with_prelude();
    let src = "universe u\n\
               class CLE (α : Type u) where\n\
               \x20 le : α → α → Prop\n\
               class CPre (α : Type u) extends CLE α where\n\
               \x20 refl : ∀ a : α, le a a\n\
               class COne where\n\
               \x20 one : Nat\n\
               class CTwo extends COne where\n\
               \x20 pos : one > 0\n\
               theorem useRefl {α : Type u} [CPre α] (a : α) : CLE.le a a := CPre.refl a\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a class field must see its parents' fields by name: {e}");
    }
}

/// `¬b` over a `Bool` is the PROPOSITION `¬(b = true)`; `!b` is `Bool.not b`
/// (`Init/Notation.lean`). Folding `¬` into `Bool.not` made `¬(a == c)` a
/// Bool-valued statement, so `fun h => …` against it had no binder type
/// ("Cannot infer type", `not_beq_of_ne`). Where a `Bool` is expected, `¬b`
/// still elaborates (Lean coerces it back with `decide`), and `!p` over a
/// decidable proposition is `!decide p`. Ground-truthed on the pinned lean.
#[test]
fn test_prefix_not_is_propositional_and_bang_is_boolean() {
    let mut env = Environment::with_prelude();
    let src = "theorem n3 (b : Bool) (hb : b = true → False) : ¬b := fun h => hb h\n\
               theorem n4 {α : Type} [BEq α] (a c : α) (hb : (a == c) = true → False) :\n\
               \x20   ¬(a == c) := fun h => hb h\n\
               def f1 (b : Bool) : Bool := ¬ b\n\
               def f2 (p : Prop) [Decidable p] : Bool := !p\n\
               def f3 (b : Bool) : Bool := !b\n\
               example : f3 true = false := rfl\n\
               example : f2 True = false := rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("`¬`/`!` must follow Lean's two notations: {e}");
    }
}

/// A class-typed `let`/`have`/`letI`/`haveI` local is a local instance for
/// the body, as every local is in Lean (`withNewFVar`); `Preorder.lift`'s
/// `letI _instLE : LE α := …` was "failed to synthesize instance".
/// Ground-truthed on the pinned lean.
#[test]
fn test_let_bound_class_locals_are_local_instances() {
    let mut env = Environment::with_prelude();
    let src = "class MyC (α : Type) where\n\
               \x20 x : α\n\
               def useC (α : Type) [MyC α] : α := MyC.x\n\
               def t1 : Nat := letI _i : MyC Nat := ⟨5⟩; useC Nat\n\
               def t2 : Nat := haveI _i : MyC Nat := ⟨5⟩; useC Nat\n\
               def t3 : Nat := let _i : MyC Nat := ⟨5⟩; useC Nat\n\
               example : t1 = 5 := rfl\n";
    if let Some(e) = elab(&mut env, src) {
        panic!("a class-typed let local must answer instance search in its body: {e}");
    }
}

fn elab_in_file(src: &str) -> Vec<(usize, String)> {
    use crate::tactic::builtins::builtin_tactic_patterns;
    use crate::{preprocess_decl_with_context, FileContext};
    use clean_parser::parse_file_with_tactics;
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file_with_tactics(src, &builtin_tactic_patterns())
        .unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    let mut errors = Vec::new();
    for (i, decl) in decls.iter().enumerate() {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        // The FileContext-aware entry point: it injects the file's `scoped
        // instance` gating, which the context-free one does not.
        if let Err(e) =
            crate::elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        {
            errors.push((i, format!("{e:?}")));
        }
    }
    errors
}

const CLASSICAL_PRELUDE: &str = "namespace Classical\n\
    noncomputable scoped instance (priority := low) propDecidable' (p : Prop) : Decidable p :=\n\
    \x20 Classical.choice (match Classical.em p with\n\
    \x20   | Or.inl h => ⟨Decidable.isTrue h⟩\n\
    \x20   | Or.inr h => ⟨Decidable.isFalse h⟩)\n\
    end Classical\n\
    axiom P : Nat → Prop\n\
    noncomputable def f (n : Nat) [Decidable (P n)] : Nat := if P n then 1 else 2\n";

/// A bare `classical` makes the `Classical`-scoped instances available for
/// the rest of its tactic block (Lean's `classical` adds
/// `Classical.propDecidable` as a local instance); it was a no-op, so a later
/// `exact` needing `Decidable (p x)` failed (`Subtype.surjective_restrict`).
/// Without `classical` the same block must still fail, as in the pinned lean.
#[test]
fn test_classical_tactic_scopes_the_classical_instances() {
    let with = format!(
        "{CLASSICAL_PRELUDE}theorem withClassical (n : Nat) : ∃ k : Nat, k = k := by\n\
         \x20 classical\n\
         \x20 exact ⟨f n, rfl⟩\n"
    );
    let errors = elab_in_file(&with);
    assert!(
        errors.is_empty(),
        "`classical` must scope propDecidable': {errors:?}"
    );
    let without = format!(
        "{CLASSICAL_PRELUDE}theorem withoutClassical (n : Nat) : ∃ k : Nat, k = k := by\n\
         \x20 exact ⟨f n, rfl⟩\n"
    );
    let errors = elab_in_file(&without);
    assert_eq!(
        errors.len(),
        1,
        "without `classical` the block must fail: {errors:?}"
    );
}
