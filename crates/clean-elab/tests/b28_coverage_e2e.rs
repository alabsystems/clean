// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Brick B28 (docs/plans/GAP_SWEEP_2026-07-09.md) — four small sweep-remainder
//! fidelity items, each end-to-end (parse → elaborate → kernel-check) and each
//! fixed loud-and-correct against Lean 4 core:
//!
//! 1. **universes — universe-offset ceiling.** Lean caps a syntactic universe
//!    offset `Sort (u + n)` at `maxUniverseOffset = 32`
//!    (`src/Lean/Elab/Level.lean` `checkUniverseOffset`, `unless n <= max`).
//!    Clean over-accepted every offset (33..macro-depth) and blew the
//!    macro-expansion depth on a huge one (`u + 9999`). Now `n > 32` is a loud
//!    typed parse error; `n <= 32` is accepted unchanged.
//!
//! 2. **term_sugar/p19 — Nat→Int coercion at the ascription boundary.**
//!    `(5 : Int)` elaborates to a genuine `Int` (`@OfNat.ofNat Int 5 _`, defeq
//!    to `Int.ofNat 5`), NOT a `Nat`; a genuine `Int`/`Nat` mismatch stays
//!    loud. (This lane was already correct at HEAD via
//!    `elab_nat_literal_with_expected`; these are the value pins that lock it.)
//!
//! 3. **match/p14 — as-pattern over an all-wildcard multi-arg ctor.**
//!    `w@(_ :: _)` (and the explicit `w@(List.cons _ _)`) crashed with a
//!    "different shape: Discriminant(3) vs Discriminant(4)" mismatch: both `_`
//!    fields minted the SAME fresh alias name, collapsing head and tail onto one
//!    binder. Now each wildcard field gets a distinct name and `w` binds the
//!    whole matched value.
//!
//! 4. **structures/p19 — anonymous struct literal on the LHS of `=`.**
//!    `{ x := 1 } = s` failed "struct literal requires type annotation or
//!    expected type": the generic app path elaborated the LHS before `s` could
//!    supply its type. Now the type-carrying operand is elaborated first and the
//!    struct literal takes its type (Lean `binop%` / `StructInst.lean`). The
//!    `{…} = {…}` (no type source) and wrong-value cases stay loud.
//!
//! Every accepted term is kernel-re-checked by `add_decl`, so these are
//! strictly-narrowing: a wrong value still fails LOUD (see the rejection tests),
//! never a silent over-accept and never a `sorryAx`.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Parse + elaborate + kernel-check + register every decl in `source` on top of
/// the `--prelude lean4-core` environment (with_prelude + strict monads), the
/// same lane the release `clean check --prelude lean4-core` binary uses. Err
/// carries the first parse/elab/kernel/inner failure.
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    env.set_lean4_core_strict_monads(true);
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "inner declaration(s) failed:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

/// Transitive axiom closure of a registered declaration (empty = proof-grade).
fn axiom_closure(env: &Environment, name: &str) -> Vec<String> {
    env.axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"))
        .iter()
        .map(std::string::ToString::to_string)
        .collect()
}

fn assert_accepts(source: &str, what: &str) -> Environment {
    match elaborate_module(source) {
        Ok(env) => env,
        Err(e) => panic!("{what} must elaborate + kernel-check, but failed:\n{e}"),
    }
}

fn assert_empty_closure(env: &Environment, name: &str) {
    let closure = axiom_closure(env, name);
    assert!(
        closure.is_empty(),
        "{name} must have an EMPTY transitive axiom closure (no sorryAx, no stubs), got {closure:?}"
    );
}

/// Assert `source` fails loud somewhere in parse/elab/kernel (fail-closed), and
/// the rejection is never laundered into a `sorry` axiom.
fn assert_rejected(source: &str, what: &str) -> String {
    match elaborate_module(source) {
        Ok(_) => {
            panic!("{what} must be rejected (fail-closed), but it elaborated and kernel-checked")
        }
        Err(e) => {
            assert!(
                !e.to_lowercase().contains("sorry"),
                "{what}: rejection must NOT be laundered into a sorry axiom; got: {e}"
            );
            e
        }
    }
}

// A shared 2-field structure + a concrete inhabitant `s : P`.
const STRUCT_P: &str =
    "structure P where\n  x : Nat\n  y : Nat\n\ndef s : P := { x := 1, y := 2 }\n";

// ---------------------------------------------------------------------------
// Item 1 — universes: universe-offset ceiling (maxUniverseOffset = 32).
// ---------------------------------------------------------------------------

#[test]
fn test_universe_offset_huge_rejected_loud() {
    // The flagship over-accept: `Sort (u + 9999)`. Before B28 this either
    // over-accepted (small offsets) or blew the macro-expansion depth (huge
    // offsets); now it is a loud typed parse error naming the offset + max.
    let e = assert_rejected(
        "def big (X : Sort (u + 9999)) : Nat := 0\n",
        "universe offset u + 9999",
    );
    assert!(
        e.contains("offset") && e.contains("32"),
        "rejection must name the universe offset and the max (32); got: {e}"
    );
    assert!(
        !e.to_lowercase().contains("macro expansion depth"),
        "must be a clean offset error, not a macro-depth blowup; got: {e}"
    );
}

#[test]
fn test_universe_offset_just_over_ceiling_rejected() {
    // Boundary: 33 > 32 rejected.
    let e = assert_rejected(
        "def big (X : Sort (u + 33)) : Nat := 0\n",
        "universe offset u + 33",
    );
    assert!(e.contains("offset") && e.contains("32"), "got: {e}");
}

#[test]
fn test_universe_offset_at_ceiling_accepted() {
    // Boundary: 32 <= 32 accepted (offset value 32 is exactly the cap).
    assert_accepts(
        "def big (X : Sort (u + 32)) : Nat := 0\n",
        "universe offset u + 32 (at the ceiling)",
    );
}

#[test]
fn test_universe_offset_small_accepted() {
    assert_accepts(
        "def big (X : Sort (u + 5)) : Nat := 0\n",
        "universe offset u + 5",
    );
}

// ---------------------------------------------------------------------------
// Item 2 — term_sugar/p19: Nat→Int coercion at the ascription boundary.
// ---------------------------------------------------------------------------

#[test]
fn test_int_ascription_is_genuine_int_value_pin() {
    // `(5 : Int)` is a genuine Int, defeq to `Int.ofNat 5`.
    let env = assert_accepts(
        "theorem p19a : (5 : Int) = Int.ofNat 5 := rfl\n",
        "(5 : Int) = Int.ofNat 5 := rfl",
    );
    assert_empty_closure(&env, "p19a");
}

#[test]
fn test_int_ascription_supports_int_arithmetic() {
    // A genuine Int participates in Int arithmetic (would fail if it stayed Nat
    // in an Int-expecting position).
    let env = assert_accepts(
        "def useInt (n : Int) : Int := n + 1\n\
         theorem p19b : useInt (5 : Int) = 6 := rfl\n",
        "useInt (5 : Int) = 6 := rfl",
    );
    assert_empty_closure(&env, "p19b");
}

#[test]
fn test_int_ascription_into_nat_stays_loud() {
    // The genuine Int/Nat mismatch is still rejected loudly — the ascribed Int
    // does not silently pass as a Nat.
    assert_rejected(
        "def badA : Nat := (5 : Int)\n",
        "def badA : Nat := (5 : Int) (Int in a Nat slot)",
    );
}

// ---------------------------------------------------------------------------
// Item 3 — match/p14: as-pattern over an all-wildcard multi-arg constructor.
// ---------------------------------------------------------------------------

#[test]
fn test_as_pattern_wildcard_cons_binds_whole_value() {
    // `w@(_ :: _)` binds the WHOLE matched value to `w`; the head/tail wildcards
    // must NOT collapse onto a single binder.
    let env = assert_accepts(
        "def headTail (xs : List Nat) : List Nat :=\n  \
           match xs with\n  \
           | w@(_ :: _) => w\n  \
           | [] => []\n\
         theorem p14a : headTail [1, 2, 3] = [1, 2, 3] := rfl\n",
        "w@(_ :: _) binds the whole list",
    );
    assert_empty_closure(&env, "p14a");
}

#[test]
fn test_as_pattern_explicit_cons_wildcards() {
    // The explicit spelling `w@(List.cons _ _)` hit the same collapse.
    assert_accepts(
        "def headTail (xs : List Nat) : List Nat :=\n  \
           match xs with\n  \
           | w@(List.cons _ _) => w\n  \
           | [] => []\n\
         theorem p14c : headTail [7] = [7] := rfl\n",
        "w@(List.cons _ _)",
    );
}

#[test]
fn test_as_pattern_wildcard_cons_wrong_value_loud() {
    // Fail-closed: `w` really is the whole value, so a wrong pin is rejected.
    assert_rejected(
        "def headTail (xs : List Nat) : List Nat :=\n  \
           match xs with\n  \
           | w@(_ :: _) => w\n  \
           | [] => []\n\
         theorem p14bad : headTail [1, 2, 3] = [1, 2] := rfl\n",
        "wrong as-pattern value pin",
    );
}

#[test]
fn test_as_pattern_named_cons_fields_still_work() {
    // Regression: the already-working named-field form is untouched.
    assert_accepts(
        "def headTail (xs : List Nat) : List Nat :=\n  \
           match xs with\n  \
           | w@(a :: rest) => w\n  \
           | [] => []\n\
         theorem p14d : headTail [4, 5] = [4, 5] := rfl\n",
        "w@(a :: rest)",
    );
}

// ---------------------------------------------------------------------------
// Item 4 — structures/p19: anonymous struct literal on the LHS of `=`.
// ---------------------------------------------------------------------------

#[test]
fn test_struct_lit_lhs_of_eq_value_pin() {
    let src = format!("{STRUCT_P}theorem p19s : {{ x := 1, y := 2 }} = s := rfl\n");
    let env = assert_accepts(&src, "{ x := 1, y := 2 } = s (struct lit on LHS)");
    assert_empty_closure(&env, "p19s");
}

#[test]
fn test_struct_lit_rhs_of_eq_still_works() {
    // Regression: the RHS form already worked (operand-0 pins the type).
    let src = format!("{STRUCT_P}theorem p19r : s = {{ x := 1, y := 2 }} := rfl\n");
    assert_accepts(&src, "s = { x := 1, y := 2 } (struct lit on RHS)");
}

#[test]
fn test_struct_lit_lhs_of_eq_wrong_value_loud() {
    // Fail-closed: a struct literal that does not equal `s` is rejected.
    let src = format!("{STRUCT_P}theorem p19bad : {{ x := 1, y := 3 }} = s := rfl\n");
    assert_rejected(&src, "wrong struct-lit value on LHS of =");
}

#[test]
fn test_struct_lit_both_sides_untyped_stays_loud() {
    // No operand can supply the structure type — stays loud (Lean rejects this
    // too: "invalid { } notation, expected type is not known").
    let src =
        format!("{STRUCT_P}theorem p19amb : {{ x := 1, y := 2 }} = {{ x := 1, y := 2 }} := rfl\n");
    assert_rejected(&src, "{ … } = { … } with no type source");
}
