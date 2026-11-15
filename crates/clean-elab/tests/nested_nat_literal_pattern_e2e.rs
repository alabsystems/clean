// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A `Nat` literal in a NESTED pattern position means that literal
//! (`some 7`, `(3, _)`, `8 :: xs`), not `0`.
//!
//! ## The defect this guards (meaning, 2026-09-17)
//!
//! `ElabCtx::bind_nested_pattern_plan_inner` planned EVERY nested `Nat` literal
//! sub-pattern as the constructor `Nat.zero`, whatever the literal was — the
//! top-level path desugars `k` to `Nat.succ^k Nat.zero` (#796) but the nested
//! path never did. So
//!
//! ```text
//! def O : Option Nat → Nat
//!   | some 7 => 1
//!   | _      => 0
//! ```
//!
//! elaborated as though it read `| some 0 => 1`, and `rfl` PROVED
//! `O (some 0) = 1` and `O (some 7) = 0`. Nothing downstream can catch this:
//! the kernel faithfully checks the term it is handed, and the term is a
//! well-typed definition of a different function than the source names. Every
//! shape that routes a sub-pattern through the nested planner was affected —
//! `match`/equation arms, `if let`, `do`-`match`, and the recursor path (a
//! `List Nat` table keyed on literal heads).
//!
//! ## What is asserted
//!
//! For each shape: the literal arm fires on ITS literal (`rfl`, axiom-free),
//! the default fires on `0` and on every other value, and the close negative
//! twins — the pre-fix claims `f <literal-0-shaped input> = <arm value>` and
//! `f <the literal> = <default value>` — are REJECTED and register nothing.
//! `Nat` literal `0` in the same nested position keeps meaning `0`.

use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

fn elaborate_all(env: &mut Environment, source: &str) {
    try_elaborate_into(env, source)
        .unwrap_or_else(|e| panic!("source must elaborate and kernel-check: {e}\n{source}"));
}

/// A registered `rfl` theorem: present, re-inferable to its statement, and with
/// an EMPTY axiom closure (pure reduction — no `sorry`, no fabricated axiom).
fn assert_rfl_theorem(env: &Environment, name: &str) {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered"));
    let proof = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("`{name}` must carry a proof value"));
    let tc = TypeChecker::new(env);
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("`{name}` proof must infer a type: {e}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "`{name}` proof type must be def-eq to its statement"
    );
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    assert!(deps.is_empty(), "`{name}` must be axiom-free; got {deps:?}");
}

fn assert_all_rfl(env: &Environment, names: &[&str]) {
    for name in names {
        assert_rfl_theorem(env, name);
    }
}

/// A false claim must be rejected AND leave nothing registered.
fn assert_rejected(env: &mut Environment, name: &str, source: &str) {
    let result = try_elaborate_into(env, source);
    assert!(result.is_err(), "false claim must be rejected: {source}");
    assert!(
        env.get_const(&Name::from_string(name)).is_none(),
        "rejected `{name}` must not be registered"
    );
}

// ---------------------------------------------------------------------------
// `match` on a constructor with a literal field — the measured shape.
// ---------------------------------------------------------------------------

#[test]
fn option_literal_field_matches_that_literal() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "\
def O : Option Nat → Nat
  | some 7 => 1
  | _      => 0
theorem o_seven : O (some 7) = 1 := rfl
theorem o_zero : O (some 0) = 0 := rfl
theorem o_six : O (some 6) = 0 := rfl
theorem o_eight : O (some 8) = 0 := rfl
theorem o_none : O none = 0 := rfl
",
    );
    assert_all_rfl(&env, &["o_seven", "o_zero", "o_six", "o_eight", "o_none"]);
    // The pre-fix meaning, exactly: `some 0` firing the `some 7` arm, and
    // `some 7` falling through to the default.
    assert_rejected(
        &mut env,
        "o_bad_zero",
        "theorem o_bad_zero : O (some 0) = 1 := rfl",
    );
    assert_rejected(
        &mut env,
        "o_bad_seven",
        "theorem o_bad_seven : O (some 7) = 0 := rfl",
    );
}

#[test]
fn option_literal_zero_field_still_matches_zero() {
    // The `k = 0` half of the same planner arm must keep its meaning: this is
    // the shape the nested path was already getting right, and the only one its
    // tests covered.
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "\
def Z : Option Nat → Nat
  | some 0 => 1
  | _      => 0
theorem z_zero : Z (some 0) = 1 := rfl
theorem z_one : Z (some 1) = 0 := rfl
theorem z_none : Z none = 0 := rfl
",
    );
    assert_all_rfl(&env, &["z_zero", "z_one", "z_none"]);
    assert_rejected(&mut env, "z_bad", "theorem z_bad : Z (some 1) = 1 := rfl");
}

#[test]
fn pair_literal_columns_match_their_literals() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "\
def P : Nat × Nat → Nat
  | (3, 4) => 1
  | (3, _) => 2
  | (_, 4) => 3
  | _      => 0
theorem p_34 : P (3, 4) = 1 := rfl
theorem p_35 : P (3, 5) = 2 := rfl
theorem p_04 : P (0, 4) = 3 := rfl
theorem p_00 : P (0, 0) = 0 := rfl
theorem p_30 : P (3, 0) = 2 := rfl
",
    );
    assert_all_rfl(&env, &["p_34", "p_35", "p_04", "p_00", "p_30"]);
    assert_rejected(
        &mut env,
        "p_bad_00",
        "theorem p_bad_00 : P (0, 0) = 1 := rfl",
    );
    assert_rejected(
        &mut env,
        "p_bad_34",
        "theorem p_bad_34 : P (3, 4) = 0 := rfl",
    );
    assert_rejected(
        &mut env,
        "p_bad_order",
        "theorem p_bad_order : P (3, 4) = 2 := rfl",
    );
}

#[test]
fn nested_literal_under_two_constructors() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "\
def N : Option (Option Nat) → Nat
  | some (some 2) => 1
  | _             => 0
theorem n_two : N (some (some 2)) = 1 := rfl
theorem n_zero : N (some (some 0)) = 0 := rfl
theorem n_none : N (some none) = 0 := rfl
",
    );
    assert_all_rfl(&env, &["n_two", "n_zero", "n_none"]);
    assert_rejected(
        &mut env,
        "n_bad",
        "theorem n_bad : N (some (some 0)) = 1 := rfl",
    );
}

// ---------------------------------------------------------------------------
// A THREE-constructor inductive: the interaction point of the two fixes. Each
// nested `casesOn` here has two non-matching minors, so the per-`casesOn`
// sharing inside `wrap_with_nested_ctor_caseson_impl` fires as well as the
// arm-scope one, and the literal's chain sits under both.
// ---------------------------------------------------------------------------

#[test]
fn three_constructor_inductive_with_literal_fields() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "\
inductive Tri where
  | a : Nat → Tri
  | b : Nat → Tri
  | c : Tri
def t1 : Tri → Nat
  | Tri.a 3 => 1
  | Tri.a _ => 2
  | Tri.b 4 => 3
  | _ => 0
theorem t1a : t1 (Tri.a 3) = 1 := rfl
theorem t1b : t1 (Tri.a 0) = 2 := rfl
theorem t1c : t1 (Tri.b 4) = 3 := rfl
theorem t1d : t1 (Tri.b 0) = 0 := rfl
theorem t1e : t1 Tri.c = 0 := rfl
",
    );
    assert_all_rfl(&env, &["t1a", "t1b", "t1c", "t1d", "t1e"]);
    // Pre-fix every one of these held instead of its twin above.
    assert_rejected(
        &mut env,
        "t1_bad_a",
        "theorem t1_bad_a : t1 (Tri.a 0) = 1 := rfl",
    );
    assert_rejected(
        &mut env,
        "t1_bad_b",
        "theorem t1_bad_b : t1 (Tri.b 0) = 3 := rfl",
    );
    assert_rejected(
        &mut env,
        "t1_bad_c",
        "theorem t1_bad_c : t1 Tri.c = 3 := rfl",
    );
}

// ---------------------------------------------------------------------------
// The recursor path (`List.rec`): literal heads of a recursive table. This is
// the byte-classifier shape, and its arms carry an induction hypothesis, so it
// travels through `elaborate_rec_arm_with_fallback` rather than the plain
// constructor-dispatch chain.
// ---------------------------------------------------------------------------

#[test]
fn recursive_list_literal_heads_match_their_literals() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "\
def L : List Nat → Nat
  | [] => 0
  | 8 :: xs => 1000 + L xs
  | 9 :: xs => 1001 + L xs
  | _ :: xs => L xs
theorem l_nil : L [] = 0 := rfl
theorem l_eight : L [8] = 1000 := rfl
theorem l_nine : L [9] = 1001 := rfl
theorem l_zero : L [0] = 0 := rfl
theorem l_seven : L [7] = 0 := rfl
theorem l_two : L [9, 8] = 2001 := rfl
theorem l_skip : L [9, 5, 8] = 2001 := rfl
",
    );
    assert_all_rfl(
        &env,
        &[
            "l_nil", "l_eight", "l_nine", "l_zero", "l_seven", "l_two", "l_skip",
        ],
    );
    // Pre-fix `L [8]` reduced to `0` and `L [0]` to `1000`: both twins passed.
    assert_rejected(
        &mut env,
        "l_bad_eight",
        "theorem l_bad_eight : L [8] = 0 := rfl",
    );
    assert_rejected(
        &mut env,
        "l_bad_zero",
        "theorem l_bad_zero : L [0] = 1000 := rfl",
    );
    assert_rejected(
        &mut env,
        "l_bad_arm",
        "theorem l_bad_arm : L [9] = 1000 := rfl",
    );
}

// ---------------------------------------------------------------------------
// `do`-`match`: its own arm compiler (`elab_do_match.rs`), and pre-fix it did
// not merely mis-select — it swapped the two arms' values outright
// (`D (some 7)` computed `0`, `D (some 0)` computed `1`).
// ---------------------------------------------------------------------------

#[test]
fn do_match_literal_field_matches_that_literal() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "\
def D (o : Option Nat) : Option Nat := do
  match o with
  | some 7 => pure 1
  | _ => pure 0
theorem d_seven : D (some 7) = some 1 := rfl
theorem d_zero : D (some 0) = some 0 := rfl
theorem d_none : D none = some 0 := rfl
",
    );
    assert_all_rfl(&env, &["d_seven", "d_zero", "d_none"]);
    assert_rejected(
        &mut env,
        "d_bad_zero",
        "theorem d_bad_zero : D (some 0) = some 1 := rfl",
    );
    assert_rejected(
        &mut env,
        "d_bad_seven",
        "theorem d_bad_seven : D (some 7) = some 0 := rfl",
    );
}

// ---------------------------------------------------------------------------
// `if let` with a literal inside the pattern: the else branch is the fallback
// of every level of the literal's `Nat.succ` chain.
// ---------------------------------------------------------------------------

#[test]
fn if_let_literal_field_matches_that_literal() {
    let mut env = Environment::with_prelude();
    elaborate_all(
        &mut env,
        "\
def I (o : Option Nat) : Nat := if let some 5 := o then 1 else 0
theorem i_five : I (some 5) = 1 := rfl
theorem i_zero : I (some 0) = 0 := rfl
theorem i_four : I (some 4) = 0 := rfl
theorem i_none : I none = 0 := rfl
",
    );
    assert_all_rfl(&env, &["i_five", "i_zero", "i_four", "i_none"]);
    assert_rejected(
        &mut env,
        "i_bad_zero",
        "theorem i_bad_zero : I (some 0) = 1 := rfl",
    );
    assert_rejected(
        &mut env,
        "i_bad_five",
        "theorem i_bad_five : I (some 5) = 0 := rfl",
    );
}
