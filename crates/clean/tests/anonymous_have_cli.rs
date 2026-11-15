// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! G68: anonymous tactic binders must reach kernel checking without recovery.

use std::process::Command;

fn check(source: &str) -> (bool, String) {
    let dir = tempfile::tempdir().expect("temporary project");
    let file = dir.path().join("Main.lean");
    std::fs::write(&file, source).expect("write source");
    let output = Command::new(env!("CARGO_BIN_EXE_clean"))
        .arg("check")
        .arg(&file)
        .output()
        .expect("run clean check");
    (
        output.status.success(),
        format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        ),
    )
}

fn check_without_axioms(source: &str) -> (bool, String) {
    check(&format!(
        "{source}\n/-- info: 'probe' does not depend on any axioms -/\n#guard_msgs in\n#print axioms probe\n",
    ))
}

#[test]
fn anonymous_have_reaches_kernel_and_retains_inaccessible_hypotheses() {
    for (goal, body) in [
        ("a = b", "have _ := h.symm\n  exact h"),
        ("b = a", "have _ : b = a := h.symm\n  assumption"),
        (
            "b = a",
            "have _ : b = a := by\n    exact h.symm\n  assumption",
        ),
        ("b = a", "have _ := by\n    exact h.symm\n  assumption"),
        (
            "b = a",
            "have _ : Nat → b = a\n    | _ => h.symm\n  rename_i reverse\n  exact reverse 0",
        ),
        (
            "b = a",
            "have _ (n : Nat) : b = a := h.symm\n  rename_i reverse\n  exact reverse 0",
        ),
        (
            "b = a",
            "have _ (n : Nat) := by\n    exact h.symm\n  rename_i reverse\n  exact reverse 0",
        ),
        ("b = a", "have first : b = a := h.symm\n  exact first"),
    ] {
        let source = format!("theorem probe (a b : Nat) (h : a = b) : {goal} := by\n  {body}\n");
        let (ok, text) = check_without_axioms(&source);
        assert!(ok, "{source}\n{text}");
        assert!(!text.contains("sorry"), "{text}");
    }
}

#[test]
fn anonymous_have_does_not_hide_an_invalid_proof() {
    let (ok, text) =
        check("theorem probe : False := by\n  have _ : False := True.intro\n  assumption\n");
    assert!(!ok, "{text}");
    assert!(text.to_lowercase().contains("mismatch"), "{text}");
    assert!(!text.contains("synthetic sorry"), "{text}");
}

#[test]
fn underscore_have_cannot_be_referenced_by_a_user_name() {
    for (reference, identifier) in [("this", "this"), ("«h✝»", "h✝")] {
        let source = format!(
            "theorem probe (a b : Nat) (h : a = b) : b = a := by\n  have _ := h.symm\n  exact {reference}\n",
        );
        let (ok, text) = check(&source);
        assert!(!ok, "{text}");
        assert!(text.contains(identifier), "{text}");
        assert!(!text.contains("synthetic sorry"), "{text}");
    }
}

#[test]
fn anonymous_haves_remain_distinct_and_can_be_renamed() {
    let (ok, text) = check_without_axioms(
        "theorem probe (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  have _ := hp\n  have _ := hq\n  rename_i first second\n  exact And.intro first second\n",
    );
    assert!(ok, "{text}");
    assert!(!text.contains("sorry"), "{text}");
}

#[test]
fn have_declarations_require_a_lean_value_separator() {
    for binder in ["_", "h"] {
        for suffix in [
            "by\n    exact True.intro",
            ": True by\n    exact True.intro",
            "True.intro",
            "from True.intro",
            ": True from True.intro",
            ": True",
        ] {
            let source = format!(
                "theorem probe : True := by\n  have {binder} {suffix}\n  exact True.intro\n",
            );
            let (ok, text) = check(&source);
            assert!(!ok, "Lean refuses this declaration: {source}\n{text}");
            assert!(text.contains("expected ':=' or '|'"), "{source}\n{text}");
        }
    }
}

#[test]
fn equation_right_hand_side_respects_its_pipe_column() {
    for source in [
        "theorem probe : True := by\n  have _ : Nat → True\n    | _ =>\n  True.intro\n  exact True.intro\n",
        "def bad : Nat → True\n  | _ =>\nTrue.intro\n",
    ] {
        let (ok, text) = check(source);
        assert!(!ok, "Lean refuses a dedented equation body: {source}\n{text}");
        assert!(text.contains("right-hand-side"), "{text}");
    }
    let (ok, text) = check_without_axioms(
        "theorem probe : True := by\n  have _ : Nat → True\n    | _ =>\n    True.intro\n  exact True.intro\n",
    );
    assert!(ok, "{text}");
}
