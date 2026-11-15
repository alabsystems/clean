// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Anonymous-constructor patterns over a dependent `∃` (lane BVAR, 2026-08-21).
//!
//! Fixture-driven from `tests/fixtures/pattern_lambda/`. The dependent fixture
//! carries SEVEN `Mathlib/Logic/Basic.lean` declarations, every one of them
//! byte-identical to Mathlib's own text (verified against
//! `Mathlib/Logic/Basic.lean` lines 597 and 752-780, `Sort*` section variable
//! included). Five are the ones the 2026-08-21 source-frontier run
//! (`docs/issues/2026-08-21-mathlib-source-frontier-logic-basic.md`) recorded
//! failing with the kernel's verbatim `Unbound variable index: 0`; the
//! non-dependent fixture is the control that was never affected.
//!
//! MEASURED BLAST RADIUS (2026-08-22, release profile, HEAD with the
//! `nested_ctor.rs` repair reverted as a negative control): **6 of these 7 are
//! rejected pre-repair, not 5.** The five above fail with `KernelCheckFailed
//! … "Unbound variable index: 0"`, and `BEx.elim` — added here — fails with a
//! DIFFERENT symptom from the same cause:
//!
//!     TypeMismatch { expected: "App(App(FVar(3), FVar(11)), FVar(13))",
//!                    actual: "cannot unify expressions of different shape:
//!                             Discriminant(0) vs Discriminant(1)" }
//!
//! `BEx.elim`'s arm is MULTI-DISCRIMINANT (`| ⟨a, h₁, h₂⟩, h' => …`), so the
//! loose sibling `BVar` lands in the arm's expected type and the failure
//! surfaces as an unsolvable discriminant unification rather than as a kernel
//! rejection. It is the same defect wearing a different error, and without
//! this pin it would be triaged as an unrelated gap. `BEx.intro` is the
//! seventh: a pure anonymous-constructor CONSTRUCTION over the same dependent
//! `∃ (x : _) (h : p x), P x h`, green before the repair and after it — the
//! in-family control that fixes the boundary at "destructure", not "dependent
//! `∃`".
//!
//! Root cause (fixed in `elab_match/nested_ctor.rs`,
//! `bind_nested_pattern_plan_inner`): `compute_ctor_field_types` returns each
//! constructor field's domain telescope-relative — field `i` sees field `i-1`
//! as the loose `BVar(0)` — and the top-level arm path opens that with
//! `open_field_type_with_fvars` before binding the local, but the NESTED
//! constructor path did not. A three-leaf `⟨x, px, qx⟩` over
//! `∃ x, ∃ _ : p x, q x` lowers the inner `Exists.intro` as a nested pattern,
//! so its second field `(fun _ => q x) (BVar 0)` reached the kernel loose.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

const FIXTURE_DIR: &str = "../../tests/fixtures/pattern_lambda";

fn read_fixture(file: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(FIXTURE_DIR)
        .join(file);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture must exist at {}: {e}", path.display()))
}

/// Elaborate every declaration of a fixture against the kernel prelude and
/// return `(declaration name, verdict)` per leaf, in source order. A verdict
/// is `Ok(())` only when the declaration registered — i.e. the kernel accepted
/// the elaborated term; otherwise it is the verbatim error rendering.
fn elab_fixture(file: &str) -> Vec<(String, Result<(), String>)> {
    let src = read_fixture(file);
    let decls = parse_file(&src).unwrap_or_else(|e| panic!("{file} must parse: {e}"));
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let mut verdicts = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx) {
            Ok(result) => {
                let mut leaves = Vec::new();
                result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    match leaf {
                        ElabResult::Failed { name, error, .. } => {
                            verdicts.push((name.to_string(), Err(format!("{error:?}"))));
                        }
                        ElabResult::Theorem { name, .. } | ElabResult::Definition { name, .. } => {
                            verdicts.push((name.to_string(), Ok(())));
                        }
                        other => panic!("{file}: unexpected leaf {other:?}"),
                    }
                }
            }
            Err(error) => {
                let name = crate::preprocess_ext::decl_name(decl)
                    .map_or_else(|| format!("<decl {}>", verdicts.len()), ToString::to_string);
                verdicts.push((name, Err(format!("{error:?}"))));
            }
        }
    }
    verdicts
}

fn assert_fixture_all_accepted(file: &str, expected_names: &[&str]) {
    let verdicts = elab_fixture(file);
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names, expected_names,
        "{file}: declaration set moved — update the expected list deliberately"
    );
    let failures: Vec<String> = verdicts
        .iter()
        .filter_map(|(name, v)| v.as_ref().err().map(|e| format!("  {name}: {e}")))
        .collect();
    assert!(
        failures.is_empty(),
        "{file}: {} of {} declarations rejected:\n{}",
        failures.len(),
        verdicts.len(),
        failures.join("\n")
    );
}

/// The seven Mathlib declarations, in source order. Six of them are rejected
/// before the nested-field repair (five `Unbound variable index: 0`, one
/// `TypeMismatch` on the multi-discriminant `BEx.elim`); all seven are
/// kernel-accepted after it.
#[test]
fn test_anon_ctor_dependent_exists_fixture_kernel_accepts_all_seven() {
    assert_fixture_all_accepted(
        "anon_ctor_dependent_exists.lean",
        &[
            "And.exists",
            "bex_def",
            "BEx.elim",
            "BEx.intro",
            "BEx.imp_right",
            "BEx.imp_left",
            "exists_of_exists_mem",
        ],
    );
}

/// The DECLARED-universe spelling of the same six declarations. Lane BVAR
/// recorded this as blocked in the `Sort*` fixture's header: rewriting the
/// section variable to `universe u` / `{α : Sort u}` made all six fail with
/// `cannot assign rigid universe parameter u := 1`, because `elab_hole` minted
/// the `_` holes in `H _ hp` / `H _ _ h'` with a hardcoded `Sort 1` type and
/// that forced `u := 1` against a genuinely rigid parameter. The rigidity was
/// always correct; the hardcode was the bug (U2, 2026-08-22). The refusal
/// itself is still pinned by `tests/fixtures/universes/p39_*_MUST_FAIL.lean`.
#[test]
fn test_anon_ctor_dependent_exists_declared_universe_kernel_accepts_all_six() {
    assert_fixture_all_accepted(
        "anon_ctor_dependent_exists_universe_u.lean",
        &[
            "bex_def",
            "BEx.elim",
            "BEx.intro",
            "BEx.imp_right",
            "BEx.imp_left",
            "exists_of_exists_mem",
        ],
    );
}

/// Control: the shapes whose lowering never reached the defective nested
/// dependent field — these passed before the repair and must keep passing.
#[test]
fn test_anon_ctor_nondependent_fixture_was_never_affected() {
    assert_fixture_all_accepted(
        "anon_ctor_nondependent_exists.lean",
        &[
            "exists_mem_of_exists",
            "exists_of_exists_and",
            "and_swap_pattern",
            "exists_const_witness",
        ],
    );
}
