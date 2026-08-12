// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression lock: `simp` must normalize the LEMMA PATTERN the same way it
//! normalizes the MATCH TARGET.
//!
//! ## The gap this guards
//!
//! Before matching, `simp` rewrites the goal subterm into a canonical form
//! (`tactic/simp/expr.rs`): it peels the heterogeneous-operator typeclass
//! projection off the head (`@HAppend.hAppend … inst l []` → `List.append α l []`)
//! and collapses `@OfNat.ofNat Nat k (instOfNatNat k)` leaves to the raw literal.
//! The lemma's stated LHS got **neither**. So the moment a lemma is itself stated
//! in NOTATION — which every imported Lean lemma over `+ - * / % ^ ++ …` is —
//! its `HAdd.hAdd`-headed pattern was matched against a `Nat.add`-headed target
//! and unification failed on the head shape alone.
//!
//! Measured on real `import Init` with a trace on the matcher, the pattern and
//! the goal subterm were **byte-identical** and the match still failed:
//!
//! ```text
//! node    = HDiv.hDiv {0,0,0} Nat Nat Nat (instHDiv {0} Nat Nat.instDiv) n (OfNat.ofNat {0} Nat 1 (instOfNatNat 1))
//! pattern = HDiv.hDiv {0,0,0} Nat Nat Nat (instHDiv {0} Nat Nat.instDiv) ?n (OfNat.ofNat {0} Nat 1 (instOfNatNat 1))
//! target  = Nat.div n 1                     <-- peeled + OfNat-collapsed
//! unify   = Failure("different shape: Discriminant(9) vs Discriminant(4)")
//! ```
//!
//! That is why `simp only [Nat.sub_add_cancel]` reported `NoProgress` while
//! `exact Nat.sub_add_cancel h` — which goes through def-eq, not head-keyed
//! matching — closed the same goal. `rw` was unaffected because its
//! `keyed_head_unify` (`tactic/equality/rewrite.rs`) already has a pattern-side
//! arm; `simp` did not.
//!
//! ## Why these fixtures need no `.olean`
//!
//! The bug is about *which side gets normalized*, not about Lean's instances.
//! An in-file lemma stated through Clean's own prelude instance reproduces it
//! exactly, in 0.2 s: `notation_lemma`'s LHS is projection-headed, the goal is
//! the same projection-headed term, and the match still failed because only the
//! goal was peeled. `two_layer_*` additionally varies the instance encoding, so
//! the pattern peel is exercised against a *different* instance term.
//!
//! ## Soundness backstop
//!
//! Normalizing the pattern only decides which candidate is *selected*: the
//! reconstructed `lhs_inst` is still built from the ORIGINAL `lemma.lhs`, still
//! checked def-eq to the goal subterm, and the assembled proof is still
//! kernel-rechecked by `add_decl`. The false gates below must therefore keep
//! failing, and they are asserted alongside the passing ones.

use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

/// Two lemmas stated in NOTATION form (projection-headed LHS), one through
/// Clean's fused prelude instance and one through a Lean-shaped two-layer stack.
/// Clean's prelude has no homogeneous `Append` class, so the second layer is
/// built from `Inhabited`, whose projection has the same shape.
const PREAMBLE: &str = r"
def myInh : Inhabited (List Nat -> List Nat -> List Nat) :=
  Inhabited.mk (List Nat -> List Nat -> List Nat) (fun a b => List.append Nat a b)

def hAppendTwoLayer : HAppend (List Nat) (List Nat) (List Nat) :=
  HAppend.mk (List Nat) (List Nat) (List Nat)
    (fun a b => Inhabited.default (List Nat -> List Nat -> List Nat) myInh a b)

theorem notation_lemma (l : List Nat) :
    @HAppend.hAppend (List Nat) (List Nat) (List Nat) (instHAppendListList Nat) l
      (List.nil Nat) = l := by
  rw [List.append_nil]

theorem two_layer_lemma (l : List Nat) :
    @HAppend.hAppend (List Nat) (List Nat) (List Nat) hAppendTwoLayer l
      (List.nil Nat) = l := by
  rw [List.append_nil]
";

/// Drive the real file pipeline for a (possibly multi-declaration) source.
fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// Elaborate `PREAMBLE ++ source` and assert the theorem `name` kernel-checks,
/// infers a def-eq type, and is axiom-free.
fn assert_tactic_theorem(name: &str, source: &str) {
    let mut env = Environment::with_prelude();
    let full = format!("{PREAMBLE}\n{source}");
    try_elaborate_into(&mut env, &full)
        .unwrap_or_else(|e| panic!("`{name}` must elaborate and kernel-check: {e}"));

    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered after elaboration"));
    let proof = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("`{name}` theorem must carry a proof value"));

    // SOUNDNESS 1 — the kernel re-derives the proof's type and it is def-eq to
    // the stated proposition.
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(proof)
        .unwrap_or_else(|e| panic!("`{name}` proof must infer a type: {e}"));
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "`{name}` proof type must be def-eq to its stated proposition"
    );

    // SOUNDNESS 2 — empty axiom_deps closure: no sorry/axiom underneath.
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom_deps closure"));
    assert!(
        deps.is_empty(),
        "`{name}` must be axiom-free (genuine tactic proof); got {deps:?}"
    );
}

/// Assert the FALSE theorem `source` does NOT elaborate-and-register a proof.
fn assert_false_theorem_rejected(name: &str, source: &str) {
    let mut env = Environment::with_prelude();
    let full = format!("{PREAMBLE}\n{source}");
    match try_elaborate_into(&mut env, &full) {
        Err(_) => {} // expected: the tactic could not (soundly) close the false goal.
        Ok(()) => {
            if let Some(info) = env.get_const(&Name::from_string(name)) {
                assert!(
                    info.value.is_none(),
                    "FALSE goal `{name}` must NOT be closed, but a proof was registered"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// PASS gates
// ---------------------------------------------------------------------------

/// The exact `Nat.div_one` shape, hermetically: pattern and goal subterm are the
/// SAME projection-headed term, and the match failed anyway because only the
/// goal was peeled. RED before the pattern-side normalization (`NoProgress`).
#[test]
fn simp_only_notation_lemma_matches_identical_notation_goal() {
    assert_tactic_theorem(
        "same_surface",
        "theorem same_surface (l : List Nat) : \
         @HAppend.hAppend (List Nat) (List Nat) (List Nat) hAppendTwoLayer l (List.nil Nat) = l := by \
         simp only [two_layer_lemma]",
    );
}

/// The `Nat.sub_add_cancel` shape: the lemma is stated through one instance
/// encoding and the goal through another. Both peel to `List.append`, so the
/// differing instance terms never have to be reconciled. RED before.
#[test]
fn simp_only_notation_lemma_matches_across_instance_encodings() {
    assert_tactic_theorem(
        "cross_encoding",
        "theorem cross_encoding (l : List Nat) : \
         @HAppend.hAppend (List Nat) (List Nat) (List Nat) (instHAppendListList Nat) l (List.nil Nat) = l := by \
         simp only [two_layer_lemma]",
    );
}

/// Mirror direction: a projection-headed pattern against a BARE-op goal, where
/// the target peel does not fire at all. RED before.
#[test]
fn simp_only_notation_lemma_matches_bare_op_goal() {
    assert_tactic_theorem(
        "bare_goal",
        "theorem bare_goal (l : List Nat) : \
         List.append Nat l (List.nil Nat) = l := by \
         simp only [two_layer_lemma]",
    );
}

/// Control that must stay green: a BARE-op pattern against a projection-headed
/// goal is the direction that already worked (the target-side peel), and the
/// pattern-side normalization must not disturb it.
#[test]
fn simp_only_bare_lemma_still_matches_notation_goal() {
    assert_tactic_theorem(
        "bare_lemma_control",
        "theorem bare_lemma_control (l : List Nat) : \
         @HAppend.hAppend (List Nat) (List Nat) (List Nat) (instHAppendListList Nat) l (List.nil Nat) = l := by \
         simp only [List.append_nil]",
    );
}

// ---------------------------------------------------------------------------
// FAIL-CLOSED gates — normalizing both sides must not admit anything false
// ---------------------------------------------------------------------------

#[test]
fn simp_only_notation_lemma_rejects_false_goal_same_surface() {
    assert_false_theorem_rejected(
        "same_surface_false",
        "theorem same_surface_false (l m : List Nat) : \
         @HAppend.hAppend (List Nat) (List Nat) (List Nat) (instHAppendListList Nat) l m = l := by \
         simp only [two_layer_lemma]",
    );
}

#[test]
fn simp_only_notation_lemma_rejects_false_goal_cross_encoding() {
    assert_false_theorem_rejected(
        "cross_encoding_false",
        "theorem cross_encoding_false (l m : List Nat) : \
         @HAppend.hAppend (List Nat) (List Nat) (List Nat) hAppendTwoLayer l m = l := by \
         simp only [two_layer_lemma]",
    );
}

#[test]
fn simp_only_notation_lemma_rejects_false_bare_op_goal() {
    assert_false_theorem_rejected(
        "bare_goal_false",
        "theorem bare_goal_false (l m : List Nat) : \
         List.append Nat l m = l := by \
         simp only [two_layer_lemma]",
    );
}
