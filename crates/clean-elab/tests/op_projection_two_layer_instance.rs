// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression lock for **multi-layer typeclass-instance stacks** in `rw` / `simp`.
//!
//! ## The gap this guards
//!
//! `rw`'s keyed matcher bridges a bare-op lemma (`@List.append ?α ?as (@List.nil ?α)`)
//! against a projection-headed goal (`@HAppend.hAppend … inst as []`) by peeling
//! exactly the projection layer — `tactic::op_projection::reduce_op_projection_head`.
//!
//! That peel used to assume the instance's field holds the op **const** directly,
//! which is true only of Clean's own *fused* prelude instances:
//!
//! ```text
//! instHAppendListList α = HAppend.mk … (List.append α)          -- Clean, one layer
//! ```
//!
//! Real Lean instances are two layers, and the H-class field is an **eta-expanded
//! lambda** over a second (homogeneous) class projection:
//!
//! ```text
//! instance [Append α] : HAppend α α α where hAppend a b := Append.append a b
//! instance : Append (List α) := ⟨List.append⟩                   -- Lean, two layers
//! ```
//!
//! Re-applying the operands to that field yields a beta-redex whose head is a
//! `Lam`, so the head-key comparison found no const and the whole bridge gave up:
//! `rw [List.append_nil]` on `as ++ []` failed with `RewriteNoMatch` and
//! `simp only [List.append_nil]` with `NoProgress` — but only *after* `import Init`
//! put Lean's genuine instances in scope, which is why no in-repo test caught it.
//! See `docs/plans/CLASS_PROJECTION_SURFACE_2026-07-29.md`.
//!
//! ## Why these fixtures need no `.olean`
//!
//! `Inhabited` is a single-field structure in Clean's own prelude, so
//! `fun a b => Inhabited.default T inst a b` reproduces *exactly* the two
//! structural features of a Lean instance stack — lambda field, nested structure
//! projection — in 0.2 s with the builtin prelude. `two_layer_*` are the RED
//! fixtures; `fused_*` is the control that was already green and must stay green.
//!
//! ## Soundness backstop
//!
//! `l ++ m = l` (symbolic `m`) is FALSE through the very same instance stack.
//! Matching up to a projection peel only chooses *which* subterm is rewritten —
//! the resulting `Eq.subst` term is still kernel-rechecked — so the false gate
//! must keep failing, and it is asserted here alongside the passing ones.

use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

/// Clean's prelude has no homogeneous `Append`/`Div`/`Mod` class, so the second
/// layer is built from `Inhabited`, whose projection has the same shape.
const TWO_LAYER_PREAMBLE: &str = r"
def myInh : Inhabited (List Nat → List Nat → List Nat) :=
  Inhabited.mk (List Nat → List Nat → List Nat) (fun a b => List.append Nat a b)

def hAppendTwoLayer : HAppend (List Nat) (List Nat) (List Nat) :=
  HAppend.mk (List Nat) (List Nat) (List Nat)
    (fun a b => Inhabited.default (List Nat → List Nat → List Nat) myInh a b)
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

/// Elaborate `TWO_LAYER_PREAMBLE ++ source` and assert the theorem `name` in it
/// kernel-checks, infers a def-eq type, and is axiom-free.
fn assert_tactic_theorem(name: &str, source: &str) {
    let mut env = Environment::with_prelude();
    let full = format!("{TWO_LAYER_PREAMBLE}\n{source}");
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

/// Assert the FALSE theorem `source` does NOT elaborate-and-register.
fn assert_false_theorem_rejected(name: &str, source: &str) {
    let mut env = Environment::with_prelude();
    let full = format!("{TWO_LAYER_PREAMBLE}\n{source}");
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

/// Control: Clean's own FUSED single-layer instance. Green before and after.
#[test]
fn rw_through_fused_single_layer_instance_still_matches() {
    assert_tactic_theorem(
        "fused_rw",
        "theorem fused_rw (l : List Nat) : \
         @HAppend.hAppend (List Nat) (List Nat) (List Nat) (instHAppendListList Nat) l (List.nil Nat) = l := by \
         rw [List.append_nil]",
    );
}

/// RED before the multi-layer peel: `RewriteNoMatch`, `searched_for` still the
/// uninstantiated `List.append {u_0} fvar#… (List.nil {u_0} fvar#…)` pattern.
#[test]
fn rw_through_two_layer_instance_matches() {
    assert_tactic_theorem(
        "two_layer_rw",
        "theorem two_layer_rw (l : List Nat) : \
         @HAppend.hAppend (List Nat) (List Nat) (List Nat) hAppendTwoLayer l (List.nil Nat) = l := by \
         rw [List.append_nil]",
    );
}

/// RED before the multi-layer peel: `NoProgress`. simp consumes the same peel.
#[test]
fn simp_only_through_two_layer_instance_matches() {
    assert_tactic_theorem(
        "two_layer_simp",
        "theorem two_layer_simp (l : List Nat) : \
         @HAppend.hAppend (List Nat) (List Nat) (List Nat) hAppendTwoLayer l (List.nil Nat) = l := by \
         simp only [List.append_nil]",
    );
}

// ---------------------------------------------------------------------------
// FAIL-CLOSED gates — a wider peel must not admit anything false
// ---------------------------------------------------------------------------

#[test]
fn rw_through_two_layer_instance_rejects_false_goal() {
    assert_false_theorem_rejected(
        "two_layer_false",
        "theorem two_layer_false (l m : List Nat) : \
         @HAppend.hAppend (List Nat) (List Nat) (List Nat) hAppendTwoLayer l m = l := by \
         rw [List.append_nil]",
    );
}

#[test]
fn simp_only_through_two_layer_instance_rejects_false_goal() {
    assert_false_theorem_rejected(
        "two_layer_false_simp",
        "theorem two_layer_false_simp (l m : List Nat) : \
         @HAppend.hAppend (List Nat) (List Nat) (List Nat) hAppendTwoLayer l m = l := by \
         simp only [List.append_nil]",
    );
}
