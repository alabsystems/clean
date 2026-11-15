// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `simp` against pinned Lean 4.8.0, one block per round-4 lane-T gap.
//!
//! Every positive row was accepted by the pinned oracle
//! (`~/.elan/toolchains/leanprover--lean4---v4.8.0/bin/lean`) and every
//! negative row was refused by it, with the message quoted beside the row.
//! A negative row asserts the refusal AND what it is about, so it fails the
//! day the refusal changes reason as loudly as the day it disappears.
//!
//! * G48 (ledger (118)) — `simp [<name nothing declares>]` is an unknown
//!   identifier, not a warning.
//! * G49 (ledger (119)) — a bare `simp` has no `assumption` closer.
//! * G41 (ledger (111)) — numeral comparisons over `Nat`/`Int` reduce to
//!   `True`/`False` with constant-size proofs.
//! * G40 (ledger (110)) — `simpCtorEq` runs under the default simprocs.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::{elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext};

/// Elaborate `code` into one fresh prelude environment and return the outcome
/// of every declaration, in order: `Ok(())` or the rendered error.
fn elab_each(code: &str) -> Vec<Result<(), String>> {
    let mut env = Environment::with_prelude();
    clean_olean::declare_environment_world(&mut env, "v4.8.0").expect("fixture source world");
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    assert!(!decls.is_empty(), "nothing parsed from:\n{code}");
    decls
        .iter()
        .map(|decl| {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
                .map(|_| ())
                .map_err(|e| e.to_string())
        })
        .collect()
}

#[track_caller]
fn assert_all_ok(code: &str) {
    for (i, r) in elab_each(code).into_iter().enumerate() {
        if let Err(e) = r {
            panic!("declaration {i} failed: {e}\n--- source ---\n{code}");
        }
    }
}

/// The LAST declaration of `code` fails, and its error contains every needle.
#[track_caller]
fn assert_last_err(code: &str, needles: &[&str]) {
    let results = elab_each(code);
    let last = results.last().expect("at least one declaration");
    let err = match last {
        Err(e) => e,
        Ok(()) => panic!("expected a refusal, got acceptance\n--- source ---\n{code}"),
    };
    for needle in needles {
        assert!(
            err.contains(needle),
            "refusal does not mention `{needle}`: {err}\n--- source ---\n{code}"
        );
    }
}

// ---------------------------------------------------------------- G48 ----

/// Lean: `unknown identifier 'totally_bogus_name_xyz'` (S/c4.lean).
#[test]
fn test_simp_unknown_lemma_name_is_an_unknown_identifier() {
    assert_last_err(
        "theorem c4 (n : Nat) (h : n = 0) : n = 0 := by\n  simp [totally_bogus_name_xyz]\n",
        &["unknown identifier", "totally_bogus_name_xyz"],
    );
}

/// Every front end that resolves a simp list shares the refusal: `simp only`,
/// `simpa`, and an erasure (`-x`: Lean "unknown constant 'bogus_xyz'").
#[test]
fn test_simp_unknown_lemma_name_refused_by_only_simpa_and_erase() {
    for tactic in [
        "simp only [bogus_xyz, h]",
        "simpa [bogus_xyz] using h",
        "simp [-bogus_xyz, h]",
    ] {
        assert_last_err(
            &format!("theorem t (n : Nat) (h : n = 0) : n = 0 := by {tactic}\n"),
            &["unknown identifier", "bogus_xyz"],
        );
    }
}

/// Positive controls: a declared lemma, a local, and the same list without the
/// bogus element all still work.
#[test]
fn test_simp_known_names_and_locals_still_resolve() {
    assert_all_ok(
        "theorem k1 (n : Nat) (h : n = 0) : n = 0 := by simp [h]\n\
         theorem k2 (n : Nat) (h : n = 0) : n + 0 = 0 := by simp only [Nat.add_zero, h]\n\
         theorem k3 (n : Nat) (h : n = 0) : n = 0 := by simpa using h\n",
    );
}

/// A name Lean 4.8.0's `Init` declares (`List.map_nil`) or exports
/// (`bind_assoc`) and Clean's builtin prelude lacks is NOT an unknown
/// identifier — Lean accepts this — and is skipped with a warning (the
/// everyday battery's `data_sum-append` writes `List.nil_append`).
#[test]
fn test_simp_lean_core_name_missing_from_the_prelude_is_skipped() {
    assert_all_ok(
        "theorem k4 (n : Nat) : n + 0 = n := by simp [List.map_nil, bind_assoc]\n\
         theorem k5 (xs ys : List Nat) : xs ++ ys = xs ++ ys := by simp only [List.nil_append]\n",
    );
}

/// STILL OPEN, pinned as a refusal: Lean realizes reserved equation names
/// (`f.eq_1`, `f.eq_def`) on demand and closes this; Clean does not mint them,
/// so the element is skipped (with a warning, not an unknown identifier) and
/// simp makes no progress. The day Clean mints them this row flips.
#[test]
fn test_simp_reserved_equation_name_is_skipped_not_unknown() {
    let code = "def f (n : Nat) : Nat := n + 1\n\
                theorem t1 : f 1 = 2 := by simp [f.eq_1]\n";
    assert_last_err(code, &["no progress"]);
    let results = elab_each(code);
    let err = results[1].as_ref().expect_err("still open");
    assert!(!err.contains("unknown identifier"), "{err}");
}

// ---------------------------------------------------------------- G49 ----

/// Lean: `simp made no progress` (S/c5.lean) — simp has no `assumption` step.
#[test]
fn test_bare_simp_does_not_close_a_goal_by_assumption() {
    assert_last_err(
        "theorem c5 (n : Nat) (h : n = 0) : n = 0 := by\n  simp\n",
        &["no progress"],
    );
    assert_last_err(
        "theorem n2 (p : Prop) (h : p) : p := by simp\n",
        &["no progress"],
    );
    // `simp at *` is no different (Lean: "simp made no progress").
    assert_last_err(
        "theorem n5 (n : Nat) (h : n = 0) : n = 0 := by simp at *\n",
        &["no progress"],
    );
}

/// After a real rewrite the goal that matches a hypothesis stays OPEN (Lean:
/// "unsolved goals … ⊢ n = 0").
#[test]
fn test_simp_progress_then_matching_hypothesis_leaves_the_goal_open() {
    assert_last_err(
        "theorem n3 (n : Nat) (h : n = 0) : n + 0 = 0 := by simp\n",
        &["unsolved goals"],
    );
}

/// The tactics that DO use hypotheses in Lean keep closing these goals.
#[test]
fn test_hypothesis_using_simp_forms_still_close() {
    assert_all_ok(
        "theorem p1 (n : Nat) (h : n = 0) : n = 0 := by simp [h]\n\
         theorem p2 (n : Nat) (h : n = 0) : n = 0 := by simp [*]\n\
         theorem p3 (n : Nat) (h : n = 0) : n = 0 := by simp_all\n\
         theorem p4 (n : Nat) (h : n = 0) : n = 0 := by simpa using h\n\
         theorem p5 (n : Nat) (h : n = 0) : n = 0 := by simpa\n\
         theorem p6 (p : Prop) (h : p) : p := by simp [h]\n",
    );
}

// ---------------------------------------------------------------- G41 ----

/// G/repro.lean's residue and v.lean's literal rows, all accepted by Lean.
#[test]
fn test_simp_decides_numeral_comparisons() {
    assert_all_ok(
        "theorem a1 : (1024 : Nat) > 0 := by simp\n\
         theorem a3 : (0 : Nat) < 1024 := by simp\n\
         theorem a5 : (2 : Nat) > 1 := by simp\n\
         theorem v1 : (3 : Nat) ≤ 5 := by simp\n\
         theorem v2 : (5 : Nat) ≥ 3 := by simp\n\
         theorem v3 : ¬ ((5 : Nat) < 3) := by simp\n\
         theorem v6 : (1024 : Int) > 0 := by simp\n\
         theorem v6b : (-3 : Int) ≤ 5 := by simp\n\
         theorem big1 : (4294967296 : Nat) > 4294967295 := by simp\n\
         theorem big3 : (4294967296 : Int) > -4294967295 := by simp\n\
         theorem big4 : ¬ ((4294967295 : Int) ≥ 4294967296) := by simp\n",
    );
}

/// The trust-ir shape (`MemoryProps.lean:128`): unfold, then decide.
#[test]
fn test_simp_decides_the_alloc_nonzero_shape() {
    assert_all_ok(
        "abbrev Addr := Nat\n\
         structure Mem where\n  nextAddr : Addr\n  nextId : Nat\n\
         def Mem.empty : Mem := { nextAddr := 1024, nextId := 0 }\n\
         def Mem.alloc (m : Mem) (size : Nat) : Addr × Mem :=\n  let base := m.nextAddr\n  \
         (base, { m with nextAddr := base + size, nextId := m.nextId + 1 })\n\
         theorem alloc_on_empty_is_nonzero (size : Nat) :\n    \
         (Mem.empty.alloc size).fst > 0 := by\n  simp [Mem.alloc, Mem.empty]\n",
    );
}

/// G/negative_twin.lean: a FALSE comparison reduces to `False` and stays open
/// (Lean: "unsolved goals ⊢ False"), at every size and over both types.
#[test]
fn test_simp_false_numeral_comparison_reduces_to_false_never_closes() {
    for stmt in [
        "(0 : Nat) > 1024",
        "(5 : Nat) < 3",
        "(3 : Int) ≥ 5",
        "(4294967295 : Nat) ≥ 4294967296",
    ] {
        assert_last_err(
            &format!("theorem bad : {stmt} := by simp\n"),
            &["unsolved goals", "False"],
        );
    }
}

/// Lean 4.8's `simp only` runs NO default simproc: "simp made no progress".
#[test]
fn test_simp_only_does_not_decide_numeral_comparisons() {
    assert_last_err(
        "theorem g1 : (1024 : Nat) > 0 := by simp only []\n",
        &["no progress"],
    );
}

// ---------------------------------------------------------------- G40 ----

/// I/gapB.lean and its constructor-disequality neighbours, accepted by Lean.
#[test]
fn test_default_simp_refutes_constructor_equations() {
    assert_all_ok(
        "inductive P where\n  | a : P\n  | b : P\n\
         theorem b1 : (true = true ∧ true = false) ↔ P.a = P.b := by simp\n\
         theorem e1 : ¬ (false = true) := by simp\n\
         theorem e2 : (P.b = P.a) = False := by simp\n\
         theorem e3 : (P.b = P.a) ↔ False := by simp\n",
    );
}

/// I/gapB_twin.lean: the false claim reduces to `False` and stays open (Lean:
/// "unsolved goals ⊢ False").
#[test]
fn test_default_simp_constructor_twin_stays_refused() {
    assert_last_err(
        "inductive P where\n  | a : P\n  | b : P\n\
         theorem b1 : (true = true ∧ true = false) ↔ P.a = P.a := by simp\n",
        &["unsolved goals", "False"],
    );
}

// ---------------------------------------------------------------- G39 ----

/// S/repro_eq.lean: `ite_eq_left_iff` turns the equation into `¬p → .error
/// "m" = .ok ()`, `simpCtorEq` (G40) makes the consequent `False`, `imp_false`
/// gives `¬¬p` and `Decidable.not_not` gives `p`, closed by `exact h`. Every
/// step under the arrow is carried by the prelude's `forall_congr`.
#[test]
fn test_simp_ite_eq_left_iff_chain_reaches_the_condition() {
    assert_all_ok(
        "theorem t (p : Prop) [Decidable p] (h : p) :\n    \
         (if p then (Except.ok () : Except String Unit) else .error \"m\") = .ok () := by\n  \
         simp\n  exact h\n",
    );
}

/// S/twin_eq.lean: the wrong branch value leaves `¬p`, and `exact h : p` is
/// refused (Lean: "type mismatch").
#[test]
fn test_simp_ite_eq_right_iff_twin_leaves_the_negation() {
    assert_last_err(
        "theorem t (p : Prop) [Decidable p] (h : p) :\n    \
         (if p then (Except.error \"m\" : Except String Unit) else .ok ()) = .ok () := by\n  \
         simp\n  exact h\n",
        &["type mismatch"],
    );
}

/// The lemmas are Lean's constants with Lean's telescopes: usable by name.
#[test]
fn test_logic_iff_lemmas_usable_by_name_with_leans_telescope() {
    assert_all_ok(
        "theorem r1 {α : Type} (a b : α) (p : Prop) [Decidable p] :\n    \
         ((if p then a else b) = b) ↔ (p → a = b) := ite_eq_right_iff\n\
         theorem r4 (p : Prop) [Decidable p] : ¬¬p ↔ p := Decidable.not_not\n\
         theorem r6 (q : Prop) : (q → False) ↔ ¬q := imp_false\n",
    );
}

/// `simp at h` reaches `Decidable.not_not` with the goal's local instance.
#[test]
fn test_simp_at_double_negation_with_a_local_instance() {
    assert_all_ok("theorem r2 (p : Prop) [Decidable p] (h : ¬¬p) : p := by simp at h; exact h\n");
}
