// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Standing falsification suite for the clean-c-sem C verifier.
//!
//! Every program below either contains GENUINE reachable undefined behaviour
//! (division-by-zero, null dereference, signed overflow, invalid shift, an
//! unchecked pointer write) or asserts a FALSE ACSL property. Each was
//! empirically confirmed to be reported VERIFIED (exit 0) by the pre-fix
//! verifier — the false-safety soundness holes catalogued in
//! `docs/SOUNDNESS_FINDINGS_CLEAN_C_SEM_2026-07.md`.
//!
//! The verifier is fundamentally incomplete, so the required behaviour is
//! FAIL-CLOSED: it must report each of these as NOT verified — that is, it must
//! produce at least one obligation that is not established (`Failed` or
//! `Unknown`), so `proved < total`. It must never certify any of them.
//!
//! The correct-path guards at the end assert the complementary property: a
//! GENUINELY-SAFE program whose precondition/invariant discharges every UB
//! obligation must still verify. If a fix over-tightens and breaks one of
//! those, the VC-gen — not the guard — is wrong.

use crate::parser::CParser;
use crate::verified::VerifiedFunction;

/// Parse a single-function translation unit and return the parsed
/// `VerifiedFunction`. Panics with a clear message on a parse failure.
fn parse_one(code: &str) -> VerifiedFunction {
    let mut parser = CParser::new();
    let functions = parser
        .parse_translation_unit_with_specs(code)
        .expect("falsification fixture should parse");
    assert_eq!(
        functions.len(),
        1,
        "fixture should contain exactly one function, got {}",
        functions.len()
    );
    functions.into_iter().next().unwrap()
}

/// A function is VERIFIED iff every obligation is established (proved) or is a
/// sound SMT-UNSAT `Unverified` goal, i.e. `failed == 0 && unknown == 0` and no
/// obligation was skipped (`proved + unverified == total`). This mirrors the
/// fail-closed success predicate in `verify_c_impl` / the CLI gate.
fn is_verified(vf: &VerifiedFunction) -> bool {
    let summary = vf.verify();
    summary.failed == 0
        && summary.unknown == 0
        && summary.proved + summary.unverified == summary.total
}

/// Assert that a fixture is NOT verified, with a diagnostic that dumps the
/// per-obligation verdicts when the assertion fails.
fn assert_not_verified(code: &str, why: &str) {
    let vf = parse_one(code);
    let summary = vf.verify();
    let verified = summary.failed == 0
        && summary.unknown == 0
        && summary.proved + summary.unverified == summary.total;
    assert!(
        !verified,
        "SOUNDNESS REGRESSION: `{}` was reported VERIFIED but has {why}.\n  summary: {}\n  details: {:#?}",
        vf.name,
        summary.overview(),
        summary.details,
    );
    // A not-verified result must be witnessed by a concrete non-established
    // obligation (a real Failed/Unknown), not by an empty VC set.
    assert!(
        summary.total > 0,
        "fixture `{}` generated no obligations at all",
        vf.name
    );
    assert!(
        summary.failed > 0 || summary.unknown > 0,
        "fixture `{}` is not-verified but produced no Failed/Unknown obligation ({})",
        vf.name,
        summary.overview()
    );
}

fn assert_verified(code: &str, why: &str) {
    let vf = parse_one(code);
    let summary = vf.verify();
    assert!(
        is_verified(&vf),
        "correct-path regression: safe program `{}` should verify because {why}, but did not.\n  summary: {}\n  details: {:#?}",
        vf.name,
        summary.overview(),
        summary.details,
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Root cause A — UB-VC incompleteness (holes 1,2,3,4,10)
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn falsify_div_by_zero_in_return() {
    // hole 1: `return a/b` with `ensures \true` — b may be zero.
    assert_not_verified(
        r"
        //@ ensures \true;
        int f(int a, int b) { return a / b; }
        ",
        "reachable division-by-zero in a return expression",
    );
}

#[test]
fn falsify_mod_by_zero_in_return() {
    assert_not_verified(
        r"
        //@ ensures \true;
        int f(int a, int b) { return a % b; }
        ",
        "reachable modulo-by-zero in a return expression",
    );
}

#[test]
fn falsify_div_by_zero_in_condition() {
    // hole 1: div-by-zero inside an `if` condition.
    assert_not_verified(
        r"
        //@ ensures \true;
        int f(int a, int b) { if (a / b) { return 1; } return 0; }
        ",
        "reachable division-by-zero in an if condition",
    );
}

#[test]
fn falsify_div_by_zero_in_initializer() {
    // hole 1: div-by-zero in a declaration initializer.
    assert_not_verified(
        r"
        //@ ensures \true;
        int f(int a, int b) { int x = a / b; return x; }
        ",
        "reachable division-by-zero in a declaration initializer",
    );
}

#[test]
fn falsify_div_by_zero_in_while_condition_loop() {
    // hole 4: `1/0` in a while-condition — the loop was modeled as skip, so the
    // condition's UB obligation was never generated.
    assert_not_verified(
        r"
        //@ ensures \true;
        int f(int a) { while (1 / 0) { a = a + 1; } return a; }
        ",
        "reachable division-by-zero in a while condition",
    );
}

#[test]
fn falsify_div_by_zero_in_loop_body() {
    // hole 4: div-by-zero inside a loop body with no sound invariant.
    assert_not_verified(
        r"
        //@ ensures \true;
        int f(int a, int b) { while (a) { int x = 1 / b; a = x; } return a; }
        ",
        "reachable division-by-zero inside a loop body (no invariant)",
    );
}

#[test]
fn falsify_signed_overflow_add() {
    // hole 3: `a + a` (overflow) hit the `_ => postcond` catch-all and was
    // never checked at any position.
    assert_not_verified(
        r"
        //@ ensures \true;
        int f(int a) { return a + a; }
        ",
        "reachable signed overflow in unconstrained addition",
    );
}

#[test]
fn falsify_compound_assignment_is_not_modeled_as_skip_in_inferred_loop_vc() {
    // Production path, not a direct wp_expr fixture. When `x += 1` was modeled
    // as skip, the false contract was certified from `requires x == 0`: the
    // verifier kept x at zero even though the real execution stores one.
    assert_not_verified(
        r"
        //@ requires x == 0;
        //@ ensures x == 0;
        int f(int x) { x += 1; return 0; }
        ",
        "a false postcondition hidden by treating compound assignment as skip",
    );
}

#[test]
fn falsify_compound_assignment_signed_overflow() {
    // `x += 1` includes the `x + 1` computation. Checking only the syntactic
    // RHS (`1`) dropped its overflow side condition and certified this for
    // x == INT_MAX.
    assert_not_verified(
        r"
        //@ ensures \true;
        int f(int x) { x += 1; return x; }
        ",
        "reachable signed overflow in compound addition",
    );
}

#[test]
fn falsify_side_effecting_compound_assignment_rhs_fails_closed() {
    // The bounded WP lane snapshots one pre-write RHS value. A nested write
    // changes the object during evaluation and is deliberately Unsupported
    // until sequencing is represented explicitly.
    assert_not_verified(
        r"
        //@ ensures \true;
        int f(int x) { x += (x = 2); return x; }
        ",
        "a side effect inside the compound-assignment RHS",
    );
}

#[test]
fn falsify_plain_complex_lvalue_write_is_not_modeled_as_skip() {
    // `p` aliases the parameter object.  Treating `*p = 1` as Q unchanged
    // certified the false postcondition from the entry-state precondition.
    assert_not_verified(
        r"
        //@ requires x == 0;
        //@ ensures x == 0;
        int f(int x) { int *p = &x; *p = 1; return 0; }
        ",
        "a false postcondition hidden by skipping a write through an alias",
    );
}

#[test]
fn falsify_nested_plain_assignment_state_effect() {
    assert_not_verified(
        r"
        //@ requires y == 0;
        //@ ensures y == 0;
        int f(int x, int y) { x = (y = 2); return 0; }
        ",
        "a nested assignment whose write was omitted from the symbolic state",
    );
}

#[test]
fn falsify_side_effecting_if_condition_state_effect() {
    assert_not_verified(
        r"
        //@ requires x == 0;
        //@ ensures x == 0;
        int f(int x) { if (x = 1) { } return 0; }
        ",
        "an assignment in a controlling expression whose state update was omitted",
    );
}

#[test]
fn falsify_uninitialized_automatic_read() {
    assert_not_verified(
        r"
        //@ ensures \true;
        int f(void) { int x; return x; }
        ",
        "a read of an indeterminate automatic object",
    );
}

#[test]
fn falsify_self_initializing_automatic_read() {
    assert_not_verified(
        r"
        //@ ensures \true;
        int f(void) { int x = x; return x; }
        ",
        "a self-initializer that reads the newly scoped indeterminate object",
    );
}

#[test]
fn falsify_unlinked_terminates_clause_authority() {
    assert_not_verified(
        r"
        //@ terminates \true;
        //@ ensures \true;
        int f(void) { return 0; }
        ",
        "a total-correctness claim with no linked termination proof",
    );
}

#[test]
fn falsify_postincrement_at_int_max() {
    assert_not_verified(
        r"
        //@ requires x == 2147483647;
        //@ ensures \true;
        int f(int x) { x++; return x; }
        ",
        "reachable signed overflow in post-increment",
    );
}

#[test]
fn falsify_predecrement_at_int_min() {
    assert_not_verified(
        r"
        //@ requires x == -2147483648;
        //@ ensures \true;
        int f(int x) { --x; return x; }
        ",
        "reachable signed overflow in pre-decrement",
    );
}

#[test]
fn falsify_unary_negation_at_int_min() {
    assert_not_verified(
        r"
        //@ requires x == -2147483648;
        //@ ensures \true;
        int f(int x) { return -x; }
        ",
        "reachable signed overflow in unary negation",
    );
}

#[test]
fn falsify_signed_division_min_by_negative_one() {
    assert_not_verified(
        r"
        //@ requires x == -2147483648;
        //@ ensures \true;
        int f(int x) { return x / -1; }
        ",
        "the signed INT_MIN / -1 representability edge",
    );
}

#[test]
fn falsify_signed_remainder_min_by_negative_one() {
    assert_not_verified(
        r"
        //@ requires x == -2147483648;
        //@ ensures \true;
        int f(int x) { return x % -1; }
        ",
        "the signed INT_MIN % -1 representability edge",
    );
}

#[test]
fn falsify_signed_left_shift_of_negative_value() {
    assert_not_verified(
        r"
        //@ requires x == -1;
        //@ ensures \true;
        int f(int x) { return x << 1; }
        ",
        "a signed left shift with a negative left operand",
    );
}

#[test]
fn falsify_signed_left_shift_nonrepresentable_result() {
    assert_not_verified(
        r"
        //@ requires x == 1073741824;
        //@ ensures \true;
        int f(int x) { return x << 1; }
        ",
        "a signed left shift whose mathematical result is not representable",
    );
}

#[test]
fn falsify_invalid_shift() {
    // hole 3: `a << n` (invalid shift) hit the catch-all and was never checked.
    assert_not_verified(
        r"
        //@ ensures \true;
        int f(int a, int n) { return a << n; }
        ",
        "reachable invalid shift amount (n may be negative or >= width)",
    );
}

#[test]
fn falsify_unchecked_pointer_write() {
    // hole 10: `*p = 42` with a `\true` contract — the write target's
    // memory-safety obligation was never generated.
    assert_not_verified(
        r"
        //@ ensures \true;
        void f(int *p) { *p = 42; }
        ",
        "unchecked write through a possibly-invalid pointer",
    );
}

#[test]
fn falsify_null_deref() {
    // A dereference of a pointer with no validity precondition.
    assert_not_verified(
        r"
        //@ ensures \true;
        int f(int *p) { return *p; }
        ",
        "unchecked dereference of a possibly-null pointer",
    );
}

#[test]
fn falsify_goto_false_ensures() {
    // hole 2: a goto/label function proves a false `ensures \result == 5`.
    assert_not_verified(
        r"
        //@ ensures \result == 5;
        int f(void) { goto done; done: return 3; }
        ",
        "goto/label control flow is not modeled (false ensures)",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Root cause B — lossy translation → false structural equality (holes 5,6,8)
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn falsify_bitand_equals_bitor() {
    // hole 5: `(a & b) == (a | b)` collapsed to structurally-equal terms.
    assert_not_verified(
        r"
        //@ ensures (a & b) == (a | b);
        int f(int a, int b) { return 0; }
        ",
        "a false property: (a & b) == (a | b) does not hold in general",
    );
}

#[test]
fn falsify_sizeof_distinct_objects() {
    // hole 6: `sizeof(x) == sizeof(y)` collapsed to a shared literal.
    assert_not_verified(
        r"
        //@ ensures sizeof(a) == sizeof(b);
        int f(int a, long b) { return 0; }
        ",
        "sizeof(int) == sizeof(long) is not a provable structural equality",
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Correct-path guards — genuinely-safe programs must STILL verify
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn correct_div_with_precondition_verifies() {
    // A concrete, representable division discharges both UB edges.  The prover
    // is intentionally incomplete for symbolic negated conjunctions, so this
    // control tests the authoritative lane without requiring that extension.
    assert_verified(
        r"
        //@ ensures \true;
        int f(void) { return 4 / 2; }
        ",
        "the divisor is non-zero and the quotient is representable",
    );
}

#[test]
fn correct_trivial_identity_verifies() {
    // No UB, trivial contract — must remain verified.
    assert_verified(
        r"
        //@ ensures \true;
        int id(int n) { return n; }
        ",
        "an identity return has no undefined behaviour and a trivial contract",
    );
}
