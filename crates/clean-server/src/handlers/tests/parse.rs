// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;

/// Test parsing a simple FATE-style file
#[test]
fn test_parse_lean_file_simple() {
    let content = r#"
-- A simple theorem
theorem simple_thm : 1 + 1 = 2 := by
  sorry
"#;

    let (theorem, sorries) = parse_lean_file(content).unwrap();

    let thm = theorem.expect("expected to find theorem in simple file");
    assert_eq!(thm.name, "simple_thm");
    assert!(thm.goal.contains("1 + 1 = 2"));
    assert_eq!(thm.original_proof, "sorry");

    assert_eq!(sorries.len(), 1, "Expected 1 sorry");
    assert_eq!(sorries[0].context, Some("simple_thm".to_string()));
}

/// Test parsing a FATE-style file with parameters
#[test]
fn test_parse_lean_file_with_params() {
    let content = r#"
import Mathlib

theorem fate_m_001 (n : Nat) (h : n > 0) : n >= 1 := by
  mathverse
"#;

    let (theorem, _sorries) = parse_lean_file(content).unwrap();

    let thm = theorem.expect("expected to find theorem in parameterized file");
    assert_eq!(thm.name, "fate_m_001");
    // Goal should contain the type signature
    assert!(thm.goal.contains("n >= 1") || thm.goal.contains("Nat"));
}

/// Test parsing a file with no theorem
#[test]
fn test_parse_lean_file_no_theorem() {
    let content = r#"
-- Just some definitions
def foo := 42
"#;

    let (theorem, sorries) = parse_lean_file(content).unwrap();

    assert!(
        theorem.is_none(),
        "Should not find theorem in def-only file"
    );
    assert!(sorries.is_empty(), "Should not find sorries");
}

/// Test parsing a full FATE-M style problem (from issue #91)
/// This matches the actual FATE benchmark format with Mathlib imports
#[test]
fn test_parse_lean_file_fate_m_format() {
    let content = r#"
import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

open scoped Polynomial

theorem fate_x_001
  [UniqueFactorizationMonoid R]
  (p q : R)
  (hp : Prime p)
  (hq : Prime q)
  (hneq : ¬Associated p q)
  (hall : ∀ r : R, Prime r → Associated r p ∨ Associated r q) :
  IsPrincipalIdealRing R := by
  sorry
"#;

    let (theorem, sorries) = parse_lean_file(content).unwrap();

    // Should find theorem
    let thm = theorem.expect("expected to find fate_x_001 theorem");
    assert_eq!(thm.name, "fate_x_001");
    // Goal should contain the return type
    assert!(
        thm.goal.contains("IsPrincipalIdealRing"),
        "Goal should contain return type"
    );
    assert_eq!(thm.original_proof, "sorry");

    // Should find sorry
    assert_eq!(sorries.len(), 1, "Expected 1 sorry");
    assert_eq!(sorries[0].context, Some("fate_x_001".to_string()));
}

// =========================================================================
// Edge case tests for parse_lean_file (#1654)
// =========================================================================

/// Test that sorry inside a comment is not detected as a real sorry.
#[test]
fn test_parse_lean_file_sorry_in_comment() {
    let content = r#"
-- This comment mentions sorry but it's not real sorry
theorem comment_test : 1 = 1 := by
  rfl
"#;

    let (theorem, sorries) = parse_lean_file(content).unwrap();

    let thm = theorem.expect("Should find theorem");
    assert_eq!(thm.name, "comment_test");
    // The sorry in the comment should NOT be counted
    assert!(
        sorries.is_empty(),
        "sorry in a comment should not be detected, found {} sorries",
        sorries.len()
    );
}

/// Test parsing a file with a lemma (not just theorem).
#[test]
fn test_parse_lean_file_lemma() {
    let content = r#"
lemma my_lemma (n : Nat) : n = n := by
  sorry
"#;

    let (theorem, sorries) = parse_lean_file(content).unwrap();

    let thm = theorem.expect("Should find lemma as theorem");
    assert_eq!(thm.name, "my_lemma");
    assert_eq!(sorries.len(), 1);
}

/// Test parsing a file with empty content.
#[test]
fn test_parse_lean_file_empty() {
    let content = "";
    let (theorem, sorries) = parse_lean_file(content).unwrap();
    assert!(theorem.is_none(), "Empty file should have no theorem");
    assert!(sorries.is_empty(), "Empty file should have no sorries");
}

/// Test parsing a file with only comments.
#[test]
fn test_parse_lean_file_only_comments() {
    let content = r#"
-- just a comment
-- another comment
/- block comment -/
"#;

    let (theorem, sorries) = parse_lean_file(content).unwrap();
    assert!(
        theorem.is_none(),
        "Comment-only file should have no theorem"
    );
    assert!(sorries.is_empty());
}

/// Test parsing a file where theorem has a multi-line type signature.
#[test]
fn test_parse_lean_file_multiline_signature() {
    let content = r#"
theorem multi_line
  (A : Type)
  (B : Type)
  (f : A -> B)
  (a : A) :
  B := by
  sorry
"#;

    let (theorem, sorries) = parse_lean_file(content).unwrap();

    let thm = theorem.expect("Should find multi-line theorem");
    assert_eq!(thm.name, "multi_line");
    assert_eq!(sorries.len(), 1);
    assert_eq!(sorries[0].context, Some("multi_line".to_string()));
}

#[test]
fn test_parse_lean_file_admit_counts_as_sorry_hole() {
    let content = r#"
theorem admitted_gap : True := by
  admit
"#;

    let (theorem, sorries) = parse_lean_file(content).unwrap();

    let thm = theorem.expect("Should find theorem with admit");
    assert_eq!(thm.name, "admitted_gap");
    assert_eq!(sorries.len(), 1, "admit should count as an explicit hole");
    assert_eq!(sorries[0].context, Some("admitted_gap".to_string()));
}

#[test]
fn test_parse_lean_file_identifier_containing_sorry_is_not_hole() {
    let content = r#"
theorem one_sorry_name : True := by
  exact True.intro
"#;

    let (theorem, sorries) = parse_lean_file(content).unwrap();

    let thm = theorem.expect("Should find theorem");
    assert_eq!(thm.name, "one_sorry_name");
    assert!(
        sorries.is_empty(),
        "identifier substrings should not count as explicit holes: {sorries:?}"
    );
}

// =========================================================================
// Block-comment regression tests (P1346 handoff)
// =========================================================================

#[test]
fn test_parse_lean_file_admit_after_inline_block_comment_counts_as_sorry_hole() {
    let content = r#"
theorem block_admit : True := by
  /- some note -/ admit
"#;

    let (_theorem, sorries) = parse_lean_file(content).unwrap();
    assert_eq!(
        sorries.len(),
        1,
        "admit after a closed inline block comment must be detected as a hole"
    );
}

#[test]
fn test_parse_lean_file_multiline_block_comment_hides_sorry_and_theorem() {
    let content = "/- \ntheorem hidden : True := by\n  sorry\n-/\ntheorem real : True := by\n  exact True.intro";

    let (theorem, sorries) = parse_lean_file(content).unwrap();
    assert!(
        sorries.is_empty(),
        "sorry inside a multiline block comment must not be reported: {sorries:?}"
    );
    let thm = theorem.expect("Should find the real theorem outside the block comment");
    assert_eq!(
        thm.name, "real",
        "theorem inside block comment must not be detected"
    );
}

#[test]
fn test_parse_lean_file_string_literal_block_comment_marker_does_not_hide_sorry() {
    let content = r#"
theorem string_comment_marker : True := by
  let marker := "/-"
  sorry
"#;

    let (theorem, sorries) = parse_lean_file(content).unwrap();
    let thm = theorem.expect("Should find theorem");
    assert_eq!(thm.name, "string_comment_marker");
    assert_eq!(
        sorries.len(),
        1,
        "string-literal block-comment markers must not hide later holes"
    );
    assert_eq!(
        sorries[0].context,
        Some("string_comment_marker".to_string())
    );
}
