// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Brick 4 — `xs[i]` indexing end-to-end: the `List` `GetElem`/`GetElem?`
//! instances plus the `get_elem_tactic` analog discharging the bounds-proof
//! slot.
//!
//! Lean ground truth (toolchain `v4.30.0-rc2`):
//! - `Init/GetElem.lean:82` — `$x[$i]` → `getElem $x $i (by get_elem_tactic)`
//! - `Init/Tactics.lean:2505-2547` — `get_elem_tactic` = `first | done |
//!   assumption | get_elem_tactic_extensible | fail`, extensible defaults
//!   `omega` / `simp +arith; done` / `trivial`
//! - `Init/Prelude.lean:3059` — `List.get : (as : List α) → Fin as.length → α`
//! - `Init/GetElem.lean:293/339` — `List.instGetElemNatLtLength` /
//!   `List.instGetElem?NatLtLength`
//!
//! Assertion families:
//! 1. POSITIVE flips (audit rows c01-c04 + probe x4) — assumption-discharged
//!    `xs[i]`, explicit-proof `xs[i]'h` / `getElem xs i h`, `xs[i]?`,
//!    `xs[i]!`, and the literal-index case, with `rfl` VALUE PINS proving the
//!    whole chain (instance projection → `List.get` → `List.rec`) computes.
//! 2. MUST-REJECT tripwires (audit §5.1) — no proof in scope, and a
//!    literally-false bound: the proof hole is never sorry-filled, never a
//!    leaked metavariable; rejection is the loud `get_elem_tactic`-analog
//!    error.
//! 3. AXIOM HYGIENE — `List.get`, both instances, and every registered probe
//!    have EMPTY transitive axiom closures.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Parse + elaborate + kernel-check + register every decl in `source` on top
/// of the default prelude. Err carries the first failure.
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

/// Assert `source` fails somewhere in parse/elab/kernel (fail-closed), and
/// return the failure text for shape assertions.
fn expect_rejected(source: &str, what: &str) -> String {
    match elaborate_module(source) {
        Ok(_) => {
            panic!("{what} must be rejected (fail-closed), but it elaborated and kernel-checked")
        }
        Err(e) => e,
    }
}

fn assert_axiom_free(env: &Environment, name: &str) {
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert!(
        deps.is_empty(),
        "{name} must have an EMPTY transitive axiom closure, got: {deps:?}"
    );
}

// =========================================================================
// 1. POSITIVE — the audit-row flips, with value pins
// =========================================================================

#[test]
fn test_getelem_assumption_discharge_c01() {
    // c01: `xs[i]` with `h : i < xs.length` in scope — the hole is closed by
    // `assumption` (Lean's first `get_elem_tactic` step). Both the
    // `List.length xs` and projection `xs.length` hypothesis spellings pin
    // the SAME obligation (the instance's valid predicate is Lean's
    // `fun as i => i < as.length` elaboration).
    let env = elaborate_module(
        r"
def f1 (xs : List Nat) (i : Nat) (h : i < List.length xs) : Nat := xs[i]
def f2 (xs : List Nat) (i : Nat) (h : i < xs.length) : Nat := xs[i]
def f3 {a : Type} (xs : List a) (i : Nat) (h : i < xs.length) : a := xs[i]
",
    )
    .expect("xs[i] with a bounds hypothesis in scope must elaborate (audit row c01)");
    assert_axiom_free(&env, "f1");
    assert_axiom_free(&env, "f2");
    assert_axiom_free(&env, "f3");
}

#[test]
fn test_getelem_explicit_proof_c02_and_x4() {
    // c02: `xs[i]'h` (parser passes `h` in the proof slot — no tactic); x4:
    // the bare-head spelling `getElem xs i h` from the audit's cross-check
    // table. Both need the deferred GetElem instance pinned BEFORE the proof
    // argument unifies (a flex `?valid xs i` invites a wrong higher-order
    // solution).
    let env = elaborate_module(
        r"
def g1 (xs : List Nat) (h : 0 < List.length xs) : Nat := xs[0]'h
def g2 (xs : List Nat) (h : 0 < List.length xs) : Nat := getElem xs 0 h
",
    )
    .expect("explicit-proof getElem forms must elaborate (audit rows c02/x4)");
    assert_axiom_free(&env, "g1");
    assert_axiom_free(&env, "g2");
}

#[test]
fn test_getelem_optional_and_bang_c03_c04_with_value_pins() {
    // c03 `xs[i]!` / c04 `xs[i]?` route through `List.instGetElem?NatLtLength`
    // (`getElem? := List.get?`; `getElem!` additionally needs
    // `Inhabited Nat`). The `rfl` pins prove the fields COMPUTE.
    let env = elaborate_module(
        r"
def q1 (xs : List Nat) : Option Nat := xs[0]?
def b1 (xs : List Nat) : Nat := xs[0]!
theorem q_val : ([5] : List Nat)[0]? = some 5 := rfl
theorem q_miss : ([5] : List Nat)[3]? = none := rfl
theorem b_val : ([7, 8] : List Nat)[1]! = 8 := rfl
",
    )
    .expect("xs[i]? / xs[i]! must elaborate and compute (audit rows c03/c04)");
    for n in ["q1", "b1", "q_val", "q_miss", "b_val"] {
        assert_axiom_free(&env, n);
    }
}

#[test]
fn test_getelem_literal_index_value_pin() {
    // The literal-index case: the obligation `1 < List.length [10, 20, 30]`
    // has no hypothesis to `assumption` — the chain's ground closers must
    // prove it. The `rfl` value pin then exercises the FULL kernel reduction
    // chain: `GetElem.getElem` projection → `List.instGetElemNatLtLength` →
    // `List.get` → `List.rec`/`Nat.rec` iota — `[10,20,30][1] ≡ 20`.
    let env = elaborate_module(
        r"
def l1 : Nat := [1, 2, 3][0]
theorem l_val : ([10, 20, 30] : List Nat)[1] = 20 := rfl
",
    )
    .expect("literal-index xs[i] must elaborate; its bound is decidably true");
    assert_axiom_free(&env, "l1");
    assert_axiom_free(&env, "l_val");
}

// =========================================================================
// 2. MUST-REJECT — the §5.1 silent-wrong tripwires stay loud
// =========================================================================

#[test]
fn test_getelem_no_proof_z_probe_rejected_loud() {
    // THE audit §5.1 z-probe: `xs[0]` with nothing in scope. The obligation
    // `0 < List.length xs` is unprovable; every chain tactic must fail and
    // the result must be the LOUD get_elem_tactic-analog error — never an
    // accepted decl, never sorry, never a leaked metavariable.
    let err = expect_rejected(
        "def g (xs : List Nat) : Nat := xs[0]\n",
        "xs[0] with no bounds proof in scope",
    );
    assert!(
        err.contains("failed to prove index is valid"),
        "rejection must be the get_elem_tactic-analog error, got: {err}"
    );
    assert!(
        !err.contains("sorry"),
        "the bounds hole must never be sorry-filled, got: {err}"
    );
}

#[test]
fn test_getelem_false_literal_bound_rejected_loud() {
    // A literally-FALSE bound: `5 < List.length [1, 2]` is decidably false.
    // The ground closers (decide) must refuse to fabricate a witness.
    let err = expect_rejected(
        "def bad : Nat := [1, 2][5]\n",
        "[1, 2][5] with an out-of-range literal index",
    );
    assert!(
        err.contains("failed to prove index is valid"),
        "rejection must be the get_elem_tactic-analog error, got: {err}"
    );
}

#[test]
fn test_getelem_wrong_explicit_proof_rejected() {
    // An explicit proof of the WRONG proposition in the `'h` slot must not
    // unify with the pinned obligation.
    expect_rejected(
        "def bad2 (xs : List Nat) (h : 0 < 1) : Nat := xs[0]'h\n",
        "xs[0]'h with a proof of the wrong bound",
    );
}

// =========================================================================
// 3. AXIOM HYGIENE — the Brick 4 prelude registrations are axiom-free
// =========================================================================

#[test]
fn test_brick4_registrations_axiom_free() {
    let env = Environment::with_prelude();
    for c in [
        "List.get",
        "List.instGetElemNatLtLength",
        "List.instGetElem?NatLtLength",
        "GetElem.getElem",
        "GetElem?.getElem?",
        "GetElem?.getElem!",
    ] {
        assert_axiom_free(&env, c);
    }
}
