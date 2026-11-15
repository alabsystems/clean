// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The registered `decide` / `native_decide` (DECISIONS R127) against pinned
//! Lean v4.30.0-rc2 where the review of `fix/decide-lean-faithful` found them
//! wider than Lean: the implication and equality stand-ins Clean uses for core
//! instances its built-in prelude lacks, the instance lookup (local, erased,
//! `local` and `scoped` instances), `have`-bound locals, and `native_decide`
//! through `noncomputable` and `@[implemented_by]` code.
//!
//! Every verdict below was measured on
//! `~/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean` (2026-10-22):
//!
//! ```text
//! (∀ n : Nat, n = n) → 1 = 1 := by decide          failed to synthesize
//! (∀ n : Nat, n = n) → True := by decide           failed to synthesize
//! 1 = 2 → ∀ n : Nat, n = n := by decide            failed to synthesize
//! (∃ n : Nat, n = 2) → True := by native_decide    failed to synthesize
//! five = 5 → 1 = 1 / ¬ (five = 5) → 1 = 1 / ∀ b : Bool, five = 5 → b = b
//!   (five irreducible)  Tactic `decide` failed … forall_prop_decidable …
//!   stuck at match h : five.beq 5
//! (2 = 2) → 1 = 1, (1 = 2) → 3 = 4, 1 = 2 → five = 5, 3 = 3 → 2 + 2 = 4   accepted
//! 3 = 3 → 2 + 2 = 5     Tactic `decide` proved that the proposition … is false
//! some five = some five, (five, 1) = (five, 1), Sum.inl five = Sum.inl five,
//!   some c = some c (axiom c), some nc = some nc (noncomputable nc)   refused
//! some c = some c / some nc = some nc := by native_decide             refused
//! some six = some six, some "a" = some "a", some (-3 : Int) = some (-3),
//!   (six, "b") = (six, "b"), some five = some five := by native_decide accepted
//! some 1 = some 2       Tactic `decide` proved that the proposition … is false
//! [Decidable (1 = 1)] / (inst : Decidable (1 = 1)) / [DecidableEq Nat]
//!   ⊢ 1 = 1 := by decide          did not reduce … stuck at the instance
//! [Decidable (1 = 1)] ⊢ 1 = 1 := by native_decide
//!   Tactic `native_decide` failed: Cannot native decide proposition with free variables
//! instance instQ : Decidable Q := isTrue hQ; Q := by decide          accepted
//! attribute [-instance] instQ; Q := by decide                        failed to synthesize
//! local instance in an open section; scoped instance in its namespace and
//!   under `open Foo in`; C.a ≠ C.b with a scoped DecidableEq C        accepted
//! the same after the section ends / outside the namespace           failed to synthesize
//! have x : Nat := 5; have hx : x = 5 := by decide
//!   Expected type must not contain free variables
//! let x : Nat := 5; have hx : x = 5 := by decide                     accepted
//! noncomputable def nc := 5; nc = 5 := by native_decide
//!   failed to compile definition … depends on 'nc', which is 'noncomputable'
//! @[implemented_by impl] def ref (n) := n  (impl n := n + 1)
//!   ref 1 = 1 := by native_decide    evaluated that the proposition … is false
//!   ref 1 = 2 := by native_decide    accepted (Lean runs `impl`)
//!   ref 1 = 1 := by decide           accepted
//! all_goals / any_goals / skip <;> have x : Nat := 5; then
//!   have hx : x = 5 := by decide       Expected type must not contain free variables
//! all_goals let x : Nat := 5; then the same                          accepted
//! axiom c : Nat: (fun _ => 1) c = 1, (c, 1).2 = 1, some c = some c,
//!   ((Classical.choice ⟨0⟩ : Nat), 1).2 = 1 := by native_decide
//!     `c` (`Classical.choice`) not supported by code generator
//! @[irreducible] stuckDec, instance (priority := high) i2 : DecidableEq Nat
//!   := stuckDec: some 1 = some 1, (1, 2) = (1, 2), Sum.inl 1 = Sum.inl 1
//!   := by decide                    failed … stuck at stuckDec 1 1
//!   some 1 = some 1 := by native_decide; none = none := by decide   accepted
//! axiom ax : DecidableEq Nat; noncomputable instance (priority := high)
//!   axInst := ax: some 1 = some 1 := by decide          stuck at ax 1 1
//!   some 1 = some 1, (1, 2) = (1, 2) := by native_decide
//!     failed to compile definition … depends on 'axInst', which is 'noncomputable'
//! instance (priority := high) okInst := fun a b => Nat.decEq a b: some 1 =
//!   some 1, (1, 2) = (1, 2) := by decide                accepted
//! (c, 1).2 = 1 and the `Classical.choice` row by decide; Qp := by
//!   native_decide (axiom Qp : Prop with an instance); (fun (_ : T → Nat) =>
//!   1) (fun _ => 2) = 1 (axiom T : Type) := by native_decide        accepted
//! ```
//!
//! Each test was red at the head the review named (441809110): there Clean
//! accepted the refused rows above, or refused the accepted instance rows.
//! The combinator and axiom rows came from the second review (d26cdb181),
//! the parameter-instance rows from the third (8281dee6f).

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::parse_file;

fn inner_failure(result: &ElabResult) -> Option<String> {
    match result {
        ElabResult::Failed { error, .. } => Some(error.to_string()),
        ElabResult::Multiple(results) => results.iter().find_map(inner_failure),
        _ => None,
    }
}

/// Elaborate every declaration of `source` against a fresh prelude; the
/// environment on success, the first error's message otherwise.
fn elaborate_file(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .map_err(|e| e.to_string())?;
        if let Some(failure) = inner_failure(&result) {
            return Err(failure);
        }
    }
    Ok(env)
}

#[track_caller]
fn expect_accepted(source: &str) {
    if let Err(e) = elaborate_file(source) {
        panic!("pinned Lean accepts this; Clean refused it: {e}\n{source}");
    }
}

#[track_caller]
fn expect_refused(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!("pinned Lean refuses this; Clean accepted it:\n{source}"),
        Err(message) => message,
    }
}

#[track_caller]
fn assert_mentions(message: &str, needle: &str, source: &str) {
    assert!(
        message.contains(needle),
        "expected `{needle}` for\n{source}\ngot: {message}"
    );
}

const NO_INSTANCE: &str = "failed to synthesize\n  Decidable";
const STUCK: &str = "did not reduce to `isTrue` or `isFalse`";
const FIVE: &str = "@[irreducible] def five : Nat := 5\n";

/// Lean's implication instance (`forall_prop_decidable`) needs `[Decidable p]`
/// and `[Decidable q]` before anything reduces.
#[test]
fn test_implication_needs_both_instances() {
    for source in [
        "theorem t : (∀ n : Nat, n = n) → 1 = 1 := by decide\n",
        "theorem t : (∀ n : Nat, n = n) → True := by decide\n",
        "theorem t : 1 = 2 → ∀ n : Nat, n = n := by decide\n",
        "theorem t : (∃ n : Nat, n = 2) → True := by native_decide\n",
    ] {
        assert_mentions(&expect_refused(source), NO_INSTANCE, source);
    }
}

/// `if hp : p then … else isTrue …`: the hypothesis is reduced first, so a
/// stuck hypothesis refuses the implication whatever the conclusion is, and a
/// false one accepts it without reducing the conclusion.
#[test]
fn test_implication_reduces_the_hypothesis_first() {
    for goal in [
        "five = 5 → 1 = 1",
        "¬ (five = 5) → 1 = 1",
        "∀ b : Bool, five = 5 → b = b",
    ] {
        let source = format!("{FIVE}theorem t : {goal} := by decide\n");
        assert_mentions(
            &expect_refused(&source),
            "Tactic `decide` failed for proposition",
            &source,
        );
    }
    let source = "theorem t : 3 = 3 → 2 + 2 = 5 := by decide\n";
    assert_mentions(
        &expect_refused(source),
        "Tactic `decide` proved that the proposition",
        source,
    );
    for goal in [
        "(2 = 2) → 1 = 1",
        "(1 = 2) → 3 = 4",
        "1 = 2 → five = 5",
        "3 = 3 → 2 + 2 = 4",
        "∀ a b : Bool, a = true → b = true → (a && b) = true",
    ] {
        expect_accepted(&format!("{FIVE}theorem t : {goal} := by decide\n"));
    }
}

/// Lean's derived `DecidableEq` reduces every leaf (`Nat.decEq`), so equal
/// sides are not enough: a leaf that does not reduce leaves it stuck.
#[test]
fn test_equality_standin_reduces_every_leaf() {
    let decls = "axiom c : Nat\nnoncomputable def nc : Nat := Classical.choice ⟨0⟩\n";
    for (goal, tactic) in [
        ("some five = some five", "decide"),
        ("(five, 1) = (five, 1)", "decide"),
        ("(Sum.inl five : Sum Nat Nat) = Sum.inl five", "decide"),
        ("some c = some c", "decide"),
        ("some c = some c", "native_decide"),
        ("some nc = some nc", "decide"),
        ("some nc = some nc", "native_decide"),
    ] {
        let source = format!("{FIVE}{decls}theorem t : {goal} := by {tactic}\n");
        expect_refused(&source);
    }
    let source = "theorem t : some 1 = some 2 := by decide\n";
    assert_mentions(
        &expect_refused(source),
        "Tactic `decide` proved that the proposition",
        source,
    );
    for (goal, tactic) in [
        ("some six = some six", "decide"),
        ("some \"a\" = some \"a\"", "decide"),
        ("some (-3 : Int) = some (-3)", "decide"),
        ("(six, \"b\") = (six, \"b\")", "decide"),
        ("some five = some five", "native_decide"),
    ] {
        expect_accepted(&format!(
            "{FIVE}def six : Nat := 6\ntheorem t : {goal} := by {tactic}\n"
        ));
    }
}

/// The derived instance compares each leaf with its type parameter's own
/// instance, global or local (third review, Q1): a stuck or axiom-backed
/// `DecidableEq Nat` leaves `some 1 = some 1` stuck, and `native_decide`
/// refuses code that reaches a `noncomputable` one. No leaf, no comparison:
/// `none = none` holds whatever the instance does.
#[test]
fn test_equation_standin_reduces_the_parameter_instances() {
    let stuck = "@[irreducible] def stuckDec : DecidableEq Nat := fun a b => Nat.decEq a b\n\
        instance (priority := high) i2 : DecidableEq Nat := stuckDec\n";
    for goal in [
        "some (1 : Nat) = some 1",
        "((1 : Nat), (2 : Nat)) = (1, 2)",
        "(Sum.inl 1 : Sum Nat Nat) = Sum.inl 1",
    ] {
        let source = format!("{stuck}theorem t : {goal} := by decide\n");
        assert_mentions(&expect_refused(&source), STUCK, &source);
    }
    expect_accepted(&format!(
        "{stuck}theorem t : some (1 : Nat) = some 1 := by native_decide\n"
    ));
    expect_accepted(&format!(
        "{stuck}theorem t : (none : Option Nat) = none := by decide\n"
    ));

    let axiomatic = "axiom ax : DecidableEq Nat\n\
        noncomputable instance (priority := high) axInst : DecidableEq Nat := ax\n";
    let source = format!("{axiomatic}theorem t : some (1 : Nat) = some 1 := by decide\n");
    assert_mentions(&expect_refused(&source), STUCK, &source);
    for goal in ["some (1 : Nat) = some 1", "((1 : Nat), (2 : Nat)) = (1, 2)"] {
        let source = format!("{axiomatic}theorem t : {goal} := by native_decide\n");
        assert_mentions(
            &expect_refused(&source),
            "depends on 'axInst', which is 'noncomputable'",
            &source,
        );
    }

    let reducing = "instance (priority := high) okInst : DecidableEq Nat := \
        fun a b => Nat.decEq a b\n";
    for goal in ["some (1 : Nat) = some 1", "((1 : Nat), (2 : Nat)) = (1, 2)"] {
        expect_accepted(&format!("{reducing}theorem t : {goal} := by decide\n"));
    }
}

/// A class-typed hypothesis is a local instance, found first; it is a free
/// variable, so reduction is stuck (and `native_decide` refuses it outright).
#[test]
fn test_local_instance_hypothesis_is_used() {
    for source in [
        "theorem t [Decidable (1 = 1)] : 1 = 1 := by decide\n",
        "theorem t (inst : Decidable (1 = 1)) : 1 = 1 := by decide\n",
        "theorem t [DecidableEq Nat] : (1 : Nat) = 1 := by decide\n",
    ] {
        assert_mentions(&expect_refused(source), STUCK, source);
    }
    let source = "theorem t [Decidable (1 = 1)] : 1 = 1 := by native_decide\n";
    assert_mentions(
        &expect_refused(source),
        "Cannot native decide proposition with free variables",
        source,
    );
    expect_accepted("theorem t (x : Nat) : 2 + 2 = 4 := by decide\n");
}

const Q: &str = "axiom Q : Prop\naxiom hQ : Q\n";

/// `attribute [-instance]` erases the instance for `decide` too.
#[test]
fn test_erased_instance_is_not_used() {
    let instance = "instance instQ : Decidable Q := Decidable.isTrue hQ\n";
    expect_accepted(&format!("{Q}{instance}theorem t : Q := by decide\n"));
    let source = format!("{Q}{instance}attribute [-instance] instQ\ntheorem t : Q := by decide\n");
    assert_mentions(&expect_refused(&source), NO_INSTANCE, &source);
}

/// `local` and `scoped` instances answer `decide` where they are in scope,
/// and only there.
#[test]
fn test_local_and_scoped_instances_follow_scope() {
    let local = "section\nlocal instance instQ : Decidable Q := Decidable.isTrue hQ\n";
    expect_accepted(&format!("{Q}{local}theorem t : Q := by decide\nend\n"));
    let source = format!("{Q}{local}end\ntheorem t : Q := by decide\n");
    assert_mentions(&expect_refused(&source), NO_INSTANCE, &source);

    let scoped = "namespace Foo\nscoped instance instQF : Decidable Q := Decidable.isTrue hQ\n";
    expect_accepted(&format!("{Q}{scoped}theorem t : Q := by decide\nend Foo\n"));
    expect_accepted(&format!(
        "{Q}{scoped}end Foo\nopen Foo in\ntheorem t : Q := by decide\n"
    ));
    let source = format!("{Q}{scoped}end Foo\ntheorem t : Q := by decide\n");
    assert_mentions(&expect_refused(&source), NO_INSTANCE, &source);

    expect_accepted(
        "inductive C | a | b\n\
         def C.dec : (x y : C) → Decidable (x = y)\n\
         \x20 | .a, .a => Decidable.isTrue rfl\n\
         \x20 | .b, .b => Decidable.isTrue rfl\n\
         \x20 | .a, .b => Decidable.isFalse (fun h => C.noConfusion h)\n\
         \x20 | .b, .a => Decidable.isFalse (fun h => C.noConfusion h)\n\
         namespace C\n\
         scoped instance instDC : DecidableEq C := C.dec\n\
         theorem tC : C.a ≠ C.b := by decide\n\
         end C\n",
    );
}

/// Lean's `zetaReduce` unfolds `let` locals only: a `have` local is opaque, so
/// a goal mentioning it has a free variable.
#[test]
fn test_have_local_is_a_free_variable() {
    let source =
        "theorem t : True := by\n  have x : Nat := 5\n  have hx : x = 5 := by decide\n  trivial\n";
    assert_mentions(
        &expect_refused(source),
        "Expected type must not contain free variables",
        source,
    );
    expect_accepted(
        "theorem t : True := by\n  let x : Nat := 5\n  have hx : x = 5 := by decide\n  trivial\n",
    );
    // A `have` made inside a combinator's focused copy of the goals (second
    // review, R4) is as opaque in the goals it hands back.
    for combinator in ["all_goals ", "any_goals ", "skip <;> "] {
        let source = format!(
            "theorem t : True := by\n  {combinator}have x : Nat := 5\n  \
             have hx : x = 5 := by decide\n  trivial\n"
        );
        assert_mentions(
            &expect_refused(&source),
            "Expected type must not contain free variables",
            &source,
        );
    }
    expect_accepted(
        "theorem t : True := by\n  all_goals let x : Nat := 5\n  \
         have hx : x = 5 := by decide\n  trivial\n",
    );
}

/// Lean's `native_decide` compiles the decision: `noncomputable` code does
/// not compile, and `@[implemented_by]` runs the implementation. Clean's
/// kernel rung evaluates neither, so it refuses both.
#[test]
fn test_native_decide_refuses_code_lean_does_not_compile_or_runs_elsewhere() {
    let source = "noncomputable def nc : Nat := 5\ntheorem t : nc = 5 := by native_decide\n";
    assert_mentions(&expect_refused(source), "noncomputable", source);

    let decls =
        "def impl (n : Nat) : Nat := n + 1\n@[implemented_by impl] def ref (n : Nat) : Nat := n\n";
    let source = format!("{decls}theorem t : ref 1 = 1 := by native_decide\n");
    assert_mentions(&expect_refused(&source), "implemented_by", &source);
    expect_accepted(&format!("{decls}theorem t : ref 1 = 1 := by decide\n"));

    // KNOWN GAP, pinned so it fails loudly the day it closes: pinned Lean
    // ACCEPTS this (its compiled `native_decide` runs `impl`, and asserts the
    // result by an auxiliary axiom). Clean refuses every `@[implemented_by]`
    // reach (DECISIONS R127). When this starts passing, assert Lean's verdict.
    let source = format!("{decls}theorem t : ref 1 = 2 := by native_decide\n");
    assert_mentions(&expect_refused(&source), "implemented_by", &source);
}

/// Lean's code generator refuses an axiom the evaluated code reaches (second
/// review, R8), the `by decide` twins aside; an axiom it erases (a proof, a
/// type) is no obstacle.
#[test]
fn test_native_decide_refuses_code_reaching_an_axiom() {
    let decls = "axiom c : Nat\n";
    for goal in [
        "(c, 1).2 = 1",
        "((Classical.choice ⟨0⟩ : Nat), 1).2 = 1",
        "some c = some c",
    ] {
        let source = format!("{decls}theorem t : {goal} := by native_decide\n");
        assert_mentions(
            &expect_refused(&source),
            "not supported by code generator",
            &source,
        );
    }
    for goal in ["(c, 1).2 = 1", "((Classical.choice ⟨0⟩ : Nat), 1).2 = 1"] {
        expect_accepted(&format!("{decls}theorem t : {goal} := by decide\n"));
    }
    expect_accepted(
        "axiom Qp : Prop\naxiom hQp : Qp\ninstance instQp : Decidable Qp := Decidable.isTrue hQp\n\
         theorem t : Qp := by native_decide\n",
    );
    expect_accepted(
        "axiom T : Type\n\
         theorem t : (fun (_ : T → Nat) => (1 : Nat)) (fun _ => 2) = 1 := by native_decide\n",
    );
    expect_accepted("theorem t : (2 : Nat) + 2 = 4 := by native_decide\n");

    // KNOWN OVER-ACCEPTANCE, pinned so it fails loudly the day it closes:
    // pinned Lean REFUSES this ("`c` not supported by code generator"), but
    // Clean's tactic bridge beta-reduces every goal before a tactic runs
    // (`infer/elab_tactic.rs`), so `native_decide` sees `1 = 1` and no `c`
    // (DECISIONS R127). When this starts refusing, assert Lean's message.
    expect_accepted(&format!(
        "{decls}theorem t : (fun (_ : Nat) => (1 : Nat)) c = 1 := by native_decide\n"
    ));
}
