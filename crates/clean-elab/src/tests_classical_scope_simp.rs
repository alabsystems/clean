// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A `classical` block must make `Classical.propDecidable` visible to SIMP's
//! instance-slot synthesis, not only to term-level `exact`/`have`.
//!
//! `Lean.Elab.Tactic.classical` (`Lean/Elab/Tactic/Classical.lean:22-29`)
//! pushes an instance-extension scope and adds `Classical.propDecidable` at
//! priority 10 for the block, so every consumer sees it uniformly — simp's
//! `synthesizeArgs` / `synthesizeInstance`
//! (`Lean/Meta/Tactic/Simp/Rewrite.lean:64,89-99`) just calls
//! `trySynthInstance` in the ambient `MetaM`.
//!
//! Clean's classical scope was an `ElabCtx` counter
//! (`ElabCtx::classical_tactic_scope`), and `synthesize_in_tactic_scope`
//! builds a FRESH `ElabCtx` per query — the counter was 0 there, so
//! `instance_visible` hid every `Classical`-scoped instance from simp.
//! `Function.extend_def`, whose `[Decidable (∃ a, f a = b)]` binder appears
//! only in the right-hand side and so must be SYNTHESIZED after matching,
//! was therefore never applied and simp reported "no progress made"
//! (`Function.extend_apply'` / `Function.extend_apply`,
//! Mathlib/Logic/Function/Basic).
//!
//! The fixture's `propDecidable'` mirrors the imported declaration's shape:
//! `noncomputable scoped instance (priority := low)`.

use clean_kernel::Environment;

/// Elaborate `src` as one FILE, so the `scoped instance` gating the query
/// depends on is actually installed, and the tactic patterns the fixtures use
/// are registered. Returns one message per failing declaration.
fn elab_in_file(src: &str) -> Vec<String> {
    use crate::tactic::builtins::builtin_tactic_patterns;
    use crate::{preprocess_decl_with_context, FileContext};
    use clean_parser::parse_file_with_tactics;
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file_with_tactics(src, &builtin_tactic_patterns())
        .unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    let mut errors = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        if let Err(e) =
            crate::elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
        {
            errors.push(format!("{e:?}"));
        }
    }
    errors
}

/// `Classical.propDecidable`'s shape, plus a lemma whose instance binder the
/// left-hand side does NOT determine — `Function.extend_def`'s shape.
const CLASSICAL_SIMP_PRELUDE: &str = "namespace Classical\n\
    noncomputable scoped instance (priority := low) propDecidable' (p : Prop) : Decidable p :=\n\
    \x20 Classical.choice (match Classical.em p with\n\
    \x20   | Or.inl h => ⟨Decidable.isTrue h⟩\n\
    \x20   | Or.inr h => ⟨Decidable.isFalse h⟩)\n\
    end Classical\n\
    axiom Q : Nat → Prop\n\
    axiom g : Nat → Nat\n\
    axiom gdef (n : Nat) [inst : Decidable (Q n)] : g n = 1\n";

/// The row's shape: `classical` then `simp only [lemma]`, where the lemma's
/// `[Decidable …]` slot can only be answered by the classical instance.
#[test]
fn test_classical_scope_reaches_simp_instance_slot() {
    let src = format!(
        "{CLASSICAL_SIMP_PRELUDE}theorem viaSimp (n : Nat) : g n = 1 := by\n\
         \x20 classical\n\
         \x20 simp only [gdef]\n"
    );
    let errors = elab_in_file(&src);
    assert!(
        errors.is_empty(),
        "`classical` must scope propDecidable' for simp's instance slot: {errors:?}"
    );
}

/// The control that passed before the fix: the TERM path already saw the
/// scope. It must keep passing — the fix may not move a path that worked.
#[test]
fn test_classical_scope_still_reaches_exact() {
    let src = format!(
        "{CLASSICAL_SIMP_PRELUDE}theorem viaExact (n : Nat) : g n = 1 := by\n\
         \x20 classical\n\
         \x20 exact gdef n\n"
    );
    let errors = elab_in_file(&src);
    assert!(
        errors.is_empty(),
        "`classical` must keep scoping propDecidable' for `exact`: {errors:?}"
    );
}

/// WITHOUT `classical` the same simp must still fail, exactly as the pinned
/// `lean` v4.30.0-rc2 rejects it: the flag may not make a scoped instance
/// visible everywhere, which is the silent-acceptance face of class (8).
#[test]
fn test_without_classical_the_simp_slot_stays_unsynthesizable() {
    let src = format!(
        "{CLASSICAL_SIMP_PRELUDE}theorem noClassical (n : Nat) : g n = 1 := by\n\
         \x20 simp only [gdef]\n"
    );
    let errors = elab_in_file(&src);
    assert_eq!(
        errors.len(),
        1,
        "without `classical` the scoped instance must stay hidden: {errors:?}"
    );
}

/// A `classical` opened MID-sequence covers the tactics after it and nothing
/// before it. `set_instance_visibility` runs once, before any tactic, so this
/// is the arm that the re-publish in `enter_classical_if_opener` exists for.
#[test]
fn test_classical_opened_mid_sequence_reaches_a_later_simp() {
    let src = format!(
        "{CLASSICAL_SIMP_PRELUDE}theorem midBlock (n : Nat) : g n = 1 := by\n\
         \x20 skip\n\
         \x20 classical\n\
         \x20 simp only [gdef]\n"
    );
    let errors = elab_in_file(&src);
    assert!(
        errors.is_empty(),
        "a mid-sequence `classical` must reach the simp after it: {errors:?}"
    );
}
