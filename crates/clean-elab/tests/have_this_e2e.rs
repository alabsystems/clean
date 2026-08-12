// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! `have` / `this` / nested-`by` elaboration — end-to-end (parse → elaborate →
//! kernel-check). Brick B19 (docs/plans/GAP_SWEEP_2026-07-09.md).
//!
//! Three coupled fidelity gaps against Lean 4 core, each fixed loud-and-correct:
//!
//! - **`tactics_in_terms/p11`** — tactic-mode `have h : T := rfl` failed for
//!   ALL `T` (even closed `2 + 2 = 4`): the body was elaborated WITHOUT the
//!   ascribed expected type, so a polymorphic `rfl` left both sides of the
//!   equation as metavariables and the unifier reported a shape mismatch. Fix:
//!   tactic-mode `have h : T := e` elaborates `e` against `T` (Lean's
//!   `elabHaveCore` → `elabTermEnsuringType`).
//!
//! - **`term_sugar/p21`** — anonymous term-level `have : P := e; this` never
//!   bound `this` (it desugared under an inaccessible `_h`), so `this` was an
//!   unknown identifier. Fix: an anonymous `have` binds the continuation name
//!   `this`, matching Lean's `expandHave`
//!   (`src/Lean/Elab/BuiltinNotation.lean`).
//!
//! - **`tactics_in_terms/p15`** — a parenthesized `by`-block in subterm
//!   position (`(by exact 2) + 3`) ran ZERO tactics: `Paren(ByTactic …)` fell
//!   through to the macro roundtrip, which collapsed the block to
//!   `ByTactic([])`, leaving the goal unsolved. Fix: `Paren(by …)`/`Paren(calc
//!   …)` unwrap to the dedicated tactic path with the surrounding expected type
//!   as the goal (`src/Lean/Elab/Term.lean` postponement semantics).
//!
//! Every accepted `have`/`by` term is kernel-re-checked by `have_`/`add_decl`,
//! so these are strictly-narrowing correctness fixes: a `have`/`by` whose proof
//! does not actually inhabit the ascribed type still fails LOUD (see the
//! rejection tests), never a silent over-accept and never a `sorryAx`.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Parse + elaborate + kernel-check + register every decl in `source` on top of
/// the default prelude. Err carries the first parse/elab/kernel/inner failure.
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
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
        .map(ToString::to_string)
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

/// Assert `source` fails loud somewhere in parse/elab/kernel (fail-closed).
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

// ---------------------------------------------------------------------------
// p11 — tactic-mode `have h : T := rfl` for several T (open Nat / closed Nat /
// Bool eq), plus a Prop-typed non-rfl proof (general expected-type threading).
// ---------------------------------------------------------------------------

#[test]
fn test_tactic_have_rfl_open_nat_eq_solves() {
    // The canonical p11 probe: `have h : n + 0 = n := rfl` inside a by-block.
    let src = "theorem t11a (n : Nat) : n + 0 = n := by\n  \
               have h : n + 0 = n := rfl\n  \
               exact h\n";
    let env = assert_accepts(src, "tactic `have h : n + 0 = n := rfl`");
    assert_empty_closure(&env, "t11a");
}

#[test]
fn test_tactic_have_rfl_closed_nat_eq_solves() {
    let src = "theorem t11b : 2 + 2 = 4 := by\n  \
               have h : 2 + 2 = 4 := rfl\n  \
               exact h\n";
    let env = assert_accepts(src, "tactic `have h : 2 + 2 = 4 := rfl`");
    assert_empty_closure(&env, "t11b");
}

#[test]
fn test_tactic_have_rfl_bool_eq_solves() {
    let src = "theorem t11c : (true && true) = true := by\n  \
               have h : (true && true) = true := rfl\n  \
               exact h\n";
    let env = assert_accepts(src, "tactic `have h : (true && true) = true := rfl`");
    assert_empty_closure(&env, "t11c");
}

#[test]
fn test_tactic_have_prop_nonrfl_proof_threads_type() {
    // A Prop-typed `have` whose proof is a plain proof term (not rfl): the
    // expected-type channel must not disturb the non-rfl path.
    let src = "theorem t11d : True := by\n  \
               have h : True := True.intro\n  \
               exact h\n";
    let env = assert_accepts(src, "tactic `have h : True := True.intro`");
    assert_empty_closure(&env, "t11d");
}

// ---------------------------------------------------------------------------
// p21 — anonymous `have : P := e; this` binds `this` (proof AND value position).
// ---------------------------------------------------------------------------

#[test]
fn test_anon_have_binds_this_proof_position() {
    // The p21 probe: `this` must resolve to the just-introduced proof.
    let src = "theorem haA (n : Nat) (h : n = 3) : n = 3 :=\n  \
               have : n = 3 := h\n  \
               this\n";
    let env = assert_accepts(src, "anonymous `have : n = 3 := h; this`");
    assert_empty_closure(&env, "haA");
}

#[test]
fn test_anon_have_binds_this_value_position() {
    // Value position: `have : Nat := 5; this` must evaluate to 5 (the let value
    // is retained / transparent), so the rfl pin reduces.
    let src = "def hvVal : Nat :=\n  \
               have : Nat := 5\n  \
               this\n\
               theorem hvVal_pin : hvVal = 5 := rfl\n";
    let env = assert_accepts(src, "anonymous value `have : Nat := 5; this`");
    assert_empty_closure(&env, "hvVal");
    assert_empty_closure(&env, "hvVal_pin");
}

#[test]
fn test_named_have_still_binds_its_name() {
    // Regression guard: a NAMED term-level `have x := …; x + 2` keeps binding
    // its own name (the `this` default only applies to the anonymous form).
    let src = "def hvNamed : Nat := have x : Nat := 3; x + 2\n\
               theorem hvNamed_pin : hvNamed = 5 := rfl\n";
    let env = assert_accepts(src, "named `have x : Nat := 3; x + 2`");
    assert_empty_closure(&env, "hvNamed");
    assert_empty_closure(&env, "hvNamed_pin");
}

// ---------------------------------------------------------------------------
// p15 — nested `by` in subterm position gets its expected type (runs its
// tactics instead of collapsing to an empty block).
// ---------------------------------------------------------------------------

#[test]
fn test_nested_by_in_operator_arg_pins() {
    // The p15 probe: `(by exact 2) + 3` must produce `2 + 3 = 5`.
    let src = "def v15 : Nat := (by exact 2) + 3\n\
               theorem v15_pin : v15 = 5 := rfl\n";
    let env = assert_accepts(src, "`def v15 : Nat := (by exact 2) + 3`");
    assert_empty_closure(&env, "v15");
    assert_empty_closure(&env, "v15_pin");
}

#[test]
fn test_nested_by_bare_paren_pins() {
    // Pure `Paren(ByTactic)` with a directly-known expected type.
    let src = "def a1 : Nat := (by exact 2)\n\
               theorem a1_pin : a1 = 2 := rfl\n";
    let env = assert_accepts(src, "`def a1 : Nat := (by exact 2)`");
    assert_empty_closure(&env, "a1");
    assert_empty_closure(&env, "a1_pin");
}

#[test]
fn test_nested_by_in_call_arg_pins() {
    // `by`-block as an ordinary function argument.
    let src = "def av : Nat := Nat.succ (by exact 4)\n\
               theorem av_pin : av = 5 := rfl\n";
    let env = assert_accepts(src, "`def av : Nat := Nat.succ (by exact 4)`");
    assert_empty_closure(&env, "av");
    assert_empty_closure(&env, "av_pin");
}

// ---------------------------------------------------------------------------
// Loud negatives — a `have`/`this` whose proof does not inhabit the ascribed
// type is REJECTED, not silently accepted and not laundered into a sorry.
// ---------------------------------------------------------------------------

#[test]
fn test_tactic_have_wrong_type_rfl_rejected() {
    // `rfl` cannot prove `2 = 3`; the have must fail loud (not accept, not sorry).
    let src = "theorem bad_have : True := by\n  \
               have h : (2 : Nat) = 3 := rfl\n  \
               exact True.intro\n";
    assert_rejected(src, "tactic `have h : (2 : Nat) = 3 := rfl`");
}

#[test]
fn test_anon_have_wrong_type_rejected() {
    // Ascribing `n = 4` to a proof of `n = 3` must be rejected at the have.
    let src = "theorem bad_anon (n : Nat) (h : n = 3) : n = 4 :=\n  \
               have : n = 4 := h\n  \
               this\n";
    assert_rejected(src, "anonymous `have : n = 4 := h` (proof has type n = 3)");
}

#[test]
fn test_nested_by_unsolved_still_loud() {
    // A nested `by` that fails to close its goal must stay LOUD (the fix routes
    // it to the real tactic path, so an empty/failing tactic block errors —
    // it must not silently succeed with a fabricated value).
    let src = "def bad_by : Nat := (by skip) + 3\n";
    assert_rejected(src, "`(by skip) + 3` (tactic leaves the goal unsolved)");
}
