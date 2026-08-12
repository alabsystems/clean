// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Brick B05 (docs/plans/GAP_SWEEP_2026-07-09.md) — inline multi-discriminant
//! match must honor Lean's FIRST-ROW priority under cross-column ("diagonal")
//! wildcard/literal overlap.
//!
//! Ground truth: Lean 4 compiles `match` alternatives strictly top-down —
//! `src/Lean/Meta/Match/Match.lean` keeps `State.alts` in source order through
//! every specialization step (`processConstructor` / `processValue` /
//! `processVariable` filter-preserve the alternative list), so the first
//! matching row wins and later overlapping rows only cover the residual.
//! The sweep's confirmed wrong value (SILENT_WRONG_SUSPECT-14,
//! `match_variants/p11_first_match_overlap`): clean kernel-certified
//! `f11 0 0 = 2 := rfl` where Lean proves `f11 0 0 = 1`.
//!
//! Every value pin below is a `theorem … := rfl` carrying LEAN's value
//! (cross-checked against Lean 4 v4.30.0-rc2 semantics), so an accept means
//! kernel-certified computation, not merely "no error". All positive pins
//! must have an EMPTY transitive axiom closure (no sorry, no new axioms).

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

fn axiom_closure(env: &Environment, name: &str) -> Vec<String> {
    env.axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"))
        .iter()
        .map(ToString::to_string)
        .collect()
}

fn assert_axiom_free(env: &Environment, names: &[&str]) {
    for name in names {
        assert!(
            axiom_closure(env, name).is_empty(),
            "{name} must have an EMPTY transitive axiom closure (no sorry, no new axioms); got {:?}",
            axiom_closure(env, name)
        );
    }
}

// =========================================================================
// The sweep's exact reproduction (match_variants/p11_first_match_overlap)
// =========================================================================

#[test]
fn test_p11_inline_diagonal_overlap_first_row_wins() {
    // SILENT_WRONG_SUSPECT-14 verbatim. Lean: f11 0 0 = 1 (first row).
    // Pre-B05 clean kernel-certified f11 0 0 = 2.
    let env = elaborate_module(
        r"
def f11 (a b : Nat) : Nat :=
  match a, b with
  | 0, _ => 1
  | _, 0 => 2
  | _, _ => 3
theorem p11a : f11 0 0 = 1 := rfl
theorem p11b : f11 0 9 = 1 := rfl
theorem p11c : f11 9 0 = 2 := rfl
theorem p11d : f11 9 9 = 3 := rfl
",
    )
    .expect("p11 diagonal-overlap inline match must elaborate with Lean's first-row values");
    assert_axiom_free(&env, &["f11", "p11a", "p11b", "p11c", "p11d"]);
}

#[test]
fn test_p11_wrong_value_no_longer_certifiable() {
    // The buggy value must now be REJECTED by the kernel: `f11 0 0 = 2` was
    // the pre-B05 kernel-certified wrong value (iso_p11_pin2).
    let err = elaborate_module(
        r"
def f11 (a b : Nat) : Nat :=
  match a, b with
  | 0, _ => 1
  | _, 0 => 2
  | _, _ => 3
theorem bad : f11 0 0 = 2 := rfl
",
    )
    .expect_err("the pre-B05 wrong value `f11 0 0 = 2` must no longer be provable by rfl");
    assert!(
        err.contains("bad"),
        "failure must be the `bad` theorem, got: {err}"
    );
}

// =========================================================================
// Equation form (iso_p11_eqform): must agree with the inline form
// =========================================================================

#[test]
fn test_p11_equation_form_first_row_wins() {
    let env = elaborate_module(
        r"
def f11b : Nat → Nat → Nat
  | 0, _ => 1
  | _, 0 => 2
  | _, _ => 3
theorem q11a : f11b 0 0 = 1 := rfl
theorem q11b : f11b 0 9 = 1 := rfl
theorem q11c : f11b 9 0 = 2 := rfl
theorem q11d : f11b 9 9 = 3 := rfl
",
    )
    .expect("equation-form diagonal overlap must keep Lean's first-row values");
    assert_axiom_free(&env, &["f11b", "q11a", "q11b", "q11c", "q11d"]);
}

// =========================================================================
// Permuted-row variants: priority is positional, not shape-based
// =========================================================================

#[test]
fn test_permuted_rows_wildcard_literal_diagonal() {
    // Same diagonal, wildcard-first: `| _, 0` before `| 0, _`.
    // Lean: g 0 0 = 1 (first row `_, 0` matches).
    let env = elaborate_module(
        r"
def g (a b : Nat) : Nat :=
  match a, b with
  | _, 0 => 1
  | 0, _ => 2
  | _, _ => 3
theorem g00 : g 0 0 = 1 := rfl
theorem g09 : g 0 9 = 2 := rfl
theorem g90 : g 9 0 = 1 := rfl
theorem g99 : g 9 9 = 3 := rfl
",
    )
    .expect("permuted diagonal (`_, 0` first) must keep first-row priority");
    assert_axiom_free(&env, &["g", "g00", "g09", "g90", "g99"]);
}

#[test]
fn test_wildcard_first_row_dominates() {
    // A leading full-wildcard row shadows everything after it (Lean also
    // reports "redundant alternative" for the later rows — that diagnostic is
    // tracked separately in B05; the VALUE semantics are first-row).
    let env = elaborate_module(
        r"
def h (a b : Nat) : Nat :=
  match a, b with
  | _, _ => 7
  | 0, 0 => 9
theorem h00 : h 0 0 = 7 := rfl
theorem h12 : h 1 2 = 7 := rfl
",
    )
    .expect("leading full-wildcard row must win for every input");
    assert_axiom_free(&env, &["h", "h00", "h12"]);
}

#[test]
fn test_wildcard_row_between_literal_rows() {
    // Wildcard row in the MIDDLE: rows after it are shadowed only where it
    // matches. Lean: m 0 0 = 1; m 5 5 = 2 (row 2 `_, _` shadows row 3).
    let env = elaborate_module(
        r"
def m (a b : Nat) : Nat :=
  match a, b with
  | 0, 0 => 1
  | _, _ => 2
  | 5, 5 => 3
theorem m00 : m 0 0 = 1 := rfl
theorem m55 : m 5 5 = 2 := rfl
theorem m01 : m 0 1 = 2 := rfl
",
    )
    .expect("mid-position wildcard row must shadow all later rows");
    assert_axiom_free(&env, &["m", "m00", "m55", "m01"]);
}

// =========================================================================
// Three-discriminant diagonal
// =========================================================================

#[test]
fn test_three_discriminant_diagonal_first_row_wins() {
    // 3-column diagonal: for (0,0,0) ALL rows match; Lean picks row 1.
    // Pre-B05 the nested specialization re-ordered binder rows behind
    // concrete rows at each depth, certifying t 0 0 0 = 2.
    let env = elaborate_module(
        r"
def t (a b c : Nat) : Nat :=
  match a, b, c with
  | _, 0, _ => 1
  | 0, _, 0 => 2
  | _, _, _ => 3
theorem t000 : t 0 0 0 = 1 := rfl
theorem t101 : t 1 0 1 = 1 := rfl
theorem t090 : t 0 9 0 = 2 := rfl
theorem t999 : t 9 9 9 = 3 := rfl
",
    )
    .expect("3-discriminant diagonal must keep first-row priority at every depth");
    assert_axiom_free(&env, &["t", "t000", "t101", "t090", "t999"]);
}

// =========================================================================
// Literal + constructor mixes
// =========================================================================

#[test]
fn test_ctor_literal_mix_diagonal() {
    // Option ctor column × Nat literal column, diagonal overlap.
    // Lean: c none 0 = 1 (first row `none, _`).
    let env = elaborate_module(
        r"
def c (o : Option Nat) (n : Nat) : Nat :=
  match o, n with
  | none, _ => 1
  | _, 0 => 2
  | _, _ => 3
theorem cn0 : c none 0 = 1 := rfl
theorem cn9 : c none 9 = 1 := rfl
theorem cs0 : c (some 4) 0 = 2 := rfl
theorem cs9 : c (some 4) 9 = 3 := rfl
",
    )
    .expect("Option-ctor × Nat-literal diagonal must keep first-row priority");
    assert_axiom_free(&env, &["c", "cn0", "cn9", "cs0", "cs9"]);
}

#[test]
fn test_bool_ctor_columns_diagonal() {
    // Bool × Bool diagonal (nullary-ctor aliases `true`/`false` in pattern
    // position). Lean: bb true true = 1 (first row).
    let env = elaborate_module(
        r"
def bb (x y : Bool) : Nat :=
  match x, y with
  | true, _ => 1
  | _, true => 2
  | _, _ => 3
theorem bbtt : bb true true = 1 := rfl
theorem bbtf : bb true false = 1 := rfl
theorem bbft : bb false true = 2 := rfl
theorem bbff : bb false false = 3 := rfl
",
    )
    .expect("Bool × Bool diagonal must keep first-row priority");
    assert_axiom_free(&env, &["bb", "bbtt", "bbtf", "bbft", "bbff"]);
}

#[test]
fn test_succ_pattern_diagonal_with_binders() {
    // `n+1` numeral-add patterns with named binders on the diagonal.
    // Lean: s 1 1 = 1+10 = 11 (first row `k+1, _`).
    let env = elaborate_module(
        r"
def s (a b : Nat) : Nat :=
  match a, b with
  | k+1, _ => k + 11
  | _, j+1 => j + 20
  | _, _ => 0
theorem s11 : s 1 1 = 11 := rfl
theorem s10 : s 1 0 = 11 := rfl
theorem s01 : s 0 1 = 20 := rfl
theorem s00 : s 0 0 = 0 := rfl
",
    )
    .expect("succ-pattern diagonal with named binders must keep first-row priority");
    assert_axiom_free(&env, &["s", "s11", "s10", "s01", "s00"]);
}

#[test]
fn test_named_binder_rows_keep_bindings_across_splice() {
    // A named binder column spliced into a constructor group must still bind
    // the variable in the arm body (pending-`let` discipline).
    // Lean: nb 0 5 = 5 (row 1 binds y); nb 3 0 = 3 (row 2 binds x).
    let env = elaborate_module(
        r"
def nb (a b : Nat) : Nat :=
  match a, b with
  | 0, y => y
  | x, 0 => x
  | _, _ => 99
theorem nb05 : nb 0 5 = 5 := rfl
theorem nb30 : nb 3 0 = 3 := rfl
theorem nb00 : nb 0 0 = 0 := rfl
theorem nb77 : nb 7 7 = 99 := rfl
",
    )
    .expect("named binder rows must keep their bindings when spliced into ctor groups");
    assert_axiom_free(&env, &["nb", "nb05", "nb30", "nb00", "nb77"]);
}

// =========================================================================
// Same-column overlap (p19-adjacent regression guard): must stay correct
// =========================================================================

#[test]
fn test_same_column_overlap_stays_first_row() {
    // p19 shape (was already correct pre-B05): overlap within one column
    // only. Guards against the fix regressing the non-diagonal case.
    let env = elaborate_module(
        r"
def f19 (b : Bool) (n : Nat) : Nat :=
  match b, n with
  | true, 0 => 1
  | true, _ => 2
  | false, _ => 3
theorem r19a : f19 true 0 = 1 := rfl
theorem r19b : f19 true 5 = 2 := rfl
theorem r19c : f19 false 0 = 3 := rfl
",
    )
    .expect("same-column overlap (p19) must stay first-row correct");
    assert_axiom_free(&env, &["f19", "r19a", "r19b", "r19c"]);
}

#[test]
fn test_two_discriminants_exhaustive_ctor_cover() {
    // p06 shape (was already correct pre-B05): fully concrete cover, no
    // wildcard rows at all.
    let env = elaborate_module(
        r"
def f6 (a b : Nat) : Nat :=
  match a, b with
  | 0, 0 => 0
  | 0, _+1 => 1
  | _+1, 0 => 2
  | _+1, _+1 => 3
theorem r6a : f6 0 0 = 0 := rfl
theorem r6b : f6 0 3 = 1 := rfl
theorem r6c : f6 3 0 = 2 := rfl
theorem r6d : f6 3 3 = 3 := rfl
",
    )
    .expect("fully-concrete two-discriminant cover (p06) must stay correct");
    assert_axiom_free(&env, &["f6", "r6a", "r6b", "r6c", "r6d"]);
}

// =========================================================================
// Inline `match … with` inside a def body vs `fun` pattern-lambda form
// =========================================================================

#[test]
fn test_fun_match_lambda_diagonal_first_row_wins() {
    // `fun | p, q => …` pattern-lambda routes through the same inline match
    // lowering; the diagonal must be first-row there too.
    let env = elaborate_module(
        r"
def fl : Nat → Nat → Nat := fun a b =>
  match a, b with
  | 0, _ => 1
  | _, 0 => 2
  | _, _ => 3
theorem fl00 : fl 0 0 = 1 := rfl
theorem fl09 : fl 0 9 = 1 := rfl
theorem fl90 : fl 9 0 = 2 := rfl
theorem fl99 : fl 9 9 = 3 := rfl
",
    )
    .expect("fun-wrapped inline diagonal match must keep first-row priority");
    assert_axiom_free(&env, &["fl", "fl00", "fl09", "fl90", "fl99"]);
}
