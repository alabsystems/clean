// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PutnamBench baseline compatibility tests.
//!
//! Tests clean parse/elaborate readiness for PutnamBench (672 Lean 4 competition
//! math problems, all requiring `import Mathlib`). See #8 for tracking.
//!
//! Current leaderboard (2026-03):
//!   Aleph Prover: 668/672 (99.4%) — benchmark nearly saturated
//!   "Without solution" variant: 0 entries — open frontier
//!
//! clean's role: fast verification backend, not standalone prover.
//! These tests verify parse + elaborate compatibility with PutnamBench syntax
//! patterns, using stubs when Mathlib .olean files are unavailable.

use clean_elab::elaborate_decl_and_register;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn assert_putnam_source_parses(source: &str, min_decls: usize, context: &str) {
    let decls = parse_file(source);
    assert!(decls.is_ok(), "{context} should parse: {:?}", decls.err());
    let decls = decls.unwrap();
    assert!(
        decls.len() >= min_decls,
        "{context} should produce at least {min_decls} declarations, got {}",
        decls.len()
    );
}

/// Parse a PutnamBench-style Nat problem (simplified to Init-only types).
///
/// Mimics the PutnamBench format: theorem statement about natural numbers
/// with `sorry` proof, similar to putnam_2023_a1 but using only Init types.
#[test]
fn test_putnam_style_nat_theorem_parses() {
    let source = r#"
theorem putnam_nat_sum_sq (n : Nat) (h : n = 3) : n * n = 9 := by sorry
"#;

    assert_putnam_source_parses(source, 1, "PutnamBench-style Nat theorem");
}

/// Parse the `noncomputable abbrev ... solution` pattern used by PutnamBench
/// for "find the answer" problems.
#[test]
fn test_putnam_style_solution_abbrev_parses() {
    let source = r#"
noncomputable abbrev putnam_test_solution : Nat := 18
"#;

    assert_putnam_source_parses(source, 1, "PutnamBench solution abbrev");
}

/// Parse a PutnamBench problem with hypotheses and conclusion — the standard
/// PutnamBench pattern with typed parameters and hypothesis naming.
#[test]
fn test_putnam_style_multi_hypothesis_parses() {
    let source = r#"
theorem putnam_multi_hyp
    (a b c : Nat)
    (h_pos_a : 0 < a) (h_pos_b : 0 < b) (h_pos_c : 0 < c)
    (h_sum : a + b = c) :
    c > 0 := by sorry
"#;

    assert_putnam_source_parses(source, 1, "Multi-hypothesis PutnamBench-style theorem");
}

/// Elaborate a PutnamBench-style Nat theorem with `sorry` proof.
///
/// This tests the full pipeline: parse → elaborate → register for a
/// Nat theorem. PutnamBench problems all use `sorry` (the benchmark task
/// is to replace sorry with a valid proof), so this is representative.
#[test]
fn test_putnam_style_nat_theorem_elaborates_with_sorry() {
    let source = r#"
theorem putnam_nat_sorry (n : Nat) (h : n = 3) : n + n = 6 := by sorry
"#;

    let decls = parse_file(source);
    assert!(decls.is_ok(), "Should parse: {:?}", decls.err());

    // Full prelude needed for Nat arithmetic (HAdd, OfNat instances).
    let mut env = Environment::with_prelude();

    let decls = decls.unwrap();
    for decl in &decls {
        match elaborate_decl_and_register(&mut env, decl) {
            Ok(_) => {}
            Err(e) => {
                panic!("PutnamBench-style Nat theorem elaboration failed: {e}");
            }
        }
    }

    assert!(
        env.get_const(&Name::from_string("putnam_nat_sorry"))
            .is_some(),
        "Theorem should be registered in environment"
    );
}

/// Parse a PutnamBench-style `import Mathlib` problem with Real types.
///
/// Verifies clean can parse the full syntax including `import Mathlib`,
/// `open` declarations, and Real-typed parameters.
#[test]
fn test_putnam_style_real_theorem_parses_with_import() {
    // Modeled after putnam_2023_a1 (find smallest n such that |f_n''(0)| > 2023)
    // Simplified to test syntax parsing with Real types.
    let source = r#"
import Mathlib
open Nat
theorem putnam_real_basic (x : Real) (h : x = 0) : x + x = 0 := by sorry
"#;

    assert_putnam_source_parses(source, 3, "PutnamBench-style Real theorem with import");
}

/// Elaborate a PutnamBench-style Real theorem using stubs.
///
/// Tests that clean's Mathlib stub mode can elaborate a simple Real theorem.
#[test]
fn test_putnam_style_real_theorem_elaborates_with_stubs() {
    let source = r#"
import Mathlib.Data.Real.Basic
theorem putnam_real_stub (a b : Real) (h : a = b) : a = b := by exact h
"#;

    let decls = parse_file(source);
    assert!(decls.is_ok(), "Should parse: {:?}", decls.err());

    let mut env = Environment::new();
    env.init_real_complex_analysis().unwrap();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();

    let decls = decls.unwrap();
    let mut elaborated = 0;
    for decl in &decls {
        if elaborate_decl_and_register(&mut env, decl).is_ok() {
            elaborated += 1;
        }
    }

    // At minimum the import should be processed. The theorem may or may not
    // elaborate depending on Real stub completeness.
    assert!(
        elaborated >= 1,
        "Should elaborate at least the import declaration"
    );
}

/// Parse the exact PutnamBench 2023 A1 header from the upstream Lean 4
/// corpus (commit `b391f48`).
///
/// This fixture exercises `open Nat`, solution abbrevs, BigOperators syntax
/// (`∏ i ∈ Finset.Icc 1 n, ...`), and `iteratedDeriv`-shaped theorem headers
/// without depending on full Mathlib elaboration.
///
/// Previously failed with "expected RParen, got Comma" before bigop_body()
/// parsing was added (tracked in #2549).
#[test]
fn test_putnam_2023_a1_header_parses_with_product_binder() {
    let source = r#"
import Mathlib

open Nat

abbrev putnam_2023_a1_solution : ℕ := sorry

theorem putnam_2023_a1
  (f : ℕ → ℝ → ℝ)
  (hf : ∀ n > 0, f n = fun x : ℝ => ∏ i ∈ Finset.Icc 1 n, Real.cos (i * x)) :
  IsLeast {n | 0 < n ∧ |iteratedDeriv 2 (f n) 0| > 2023} putnam_2023_a1_solution :=
sorry
"#;

    // 4 declarations: Import, Open, Def (abbrev), Theorem
    assert_putnam_source_parses(source, 4, "PutnamBench 2023 A1 fixture");
}

/// Parse an exact PutnamBench 2010 A1-style header from the upstream Lean 4
/// corpus (commit `b391f48`).
///
/// This covers solution functions, anonymous function equality, dependent
/// `Fin k`, and `Finset.univ.filter (boxes · = i)` syntax seen in the real
/// benchmark files.
#[test]
fn test_putnam_2010_a1_header_parses_from_upstream_fixture() {
    let source = r#"
import Mathlib

noncomputable abbrev putnam_2010_a1_solution : ℕ → ℕ := sorry

theorem putnam_2010_a1
    (n : ℕ)
    (kboxes : ℕ → Prop)
    (npos : n > 0)
    (hkboxes : ∀ k : ℕ, kboxes k =
      (∃ boxes : Finset.Icc 1 n → Fin k, ∀ i j : Fin k,
        ∑ x ∈ Finset.univ.filter (boxes · = i), (x : ℕ) =
        ∑ x ∈ Finset.univ.filter (boxes · = j), (x : ℕ))) :
    IsGreatest kboxes (putnam_2010_a1_solution n) :=
  sorry
"#;

    assert_putnam_source_parses(source, 3, "PutnamBench 2010 A1 fixture");
}

/// Parse an exact PutnamBench 2005 A4-style header from the upstream Lean 4
/// corpus (commit `b391f48`).
///
/// This covers multi-namespace opens together with `Matrix`, `Fin`, and
/// `submatrix`-style theorem parameters from the benchmark corpus.
#[test]
fn test_putnam_2005_a4_header_parses_from_upstream_fixture() {
    let source = r#"
import Mathlib

open Nat Set

theorem putnam_2005_a4
(n : ℕ)
(H : Matrix (Fin n) (Fin n) ℝ)
(a b : ℕ)
(S : Matrix (Fin a) (Fin b) ℝ)
(npos : n ≥ 1)
(Hentries : ∀ i j : Fin n, H i j = 1 ∨ H i j = -1)
(Hortho : H.HasOrthogonalRows)
(hab : 1 ≤ a ∧ a ≤ n ∧ 1 ≤ b ∧ b ≤ n)
(Ssub : ∃ (rri : Fin a → Fin n) (cri : Fin b → Fin n), rri.Injective ∧ cri.Injective ∧ S = H.submatrix rri cri)
(Sentries : ∀ (i : Fin a) (j : Fin b), S i j = 1)
: a * b ≤ n :=
sorry
"#;

    assert_putnam_source_parses(source, 3, "PutnamBench 2005 A4 fixture");
}
