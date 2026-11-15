// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! simp must not bind a `Prop`-declared lemma binder to a `Sort u` term
//! (lane UNIV, 2026-08-31).
//!
//! Fixture-driven from `tests/fixtures/universes/p52_simp_binder_domain.lean`,
//! elaborated through the same production entry (`preprocess_decl_with_context`
//! + `elaborate_decl_and_register_with_context`) as every other universes
//! fixture, so a verdict here is the kernel's verdict on a real elaborated
//! term — not a unit assertion over a hand-built `SimpLemma`.
//!
//! # The defect
//!
//! `simp/pattern.rs` mints one metavariable per lemma binder with the
//! PLACEHOLDER type `Expr::type_()`, discarding the binder's declared domain,
//! and `MetaState::assign` does an occurs check and an undo record but no type
//! check. So `capRhs : ∀ (p : Prop), (p → True) = p` captured `γ : Sort v`.
//!
//! Nothing downstream objected. `lhs_inst ≡ expr` holds (it IS the same term);
//! `proof_matches_rewrite` runs `ProofState::infer_type`, the kernel's
//! `infer_only` fast path, which never checks an application argument against
//! its binder domain. The first thing to object was `close_goal`'s
//! `infer_type_strict`, by which point the ill-typed `@capRhs γ` was already
//! the tactic's output — so the whole declaration died with
//! `TypeMismatch { expected: Sort(Zero), inferred: Sort(Param v) }`.
//!
//! # Why the third declaration is the one that matters
//!
//! Measured on the release binary at `4c4e2d22b` (pre-fix) against this
//! fixture's shapes: with BOTH lemmas offered, the `Prop`-binder one is tried
//! first, matches, and kills the declaration — the correct
//! universe-polymorphic `capU` never gets its turn. So this is not merely a
//! bad error message on a goal that was doomed anyway: refusing the ill-typed
//! match is what makes the honest lemma reachable. Post-fix the same input
//! rewrites through `capU` and closes.
//!
//! The two controls pin the guard as purely restrictive: a genuine `Prop`
//! still matches the `Prop` binder, and `capU` alone still solves its own
//! universe from the matched argument (the `expr.rs` telescope walk).

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

const FIXTURE: &str = "p52_simp_binder_domain.lean";

fn read_fixture(file: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/universes")
        .join(file);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture must exist at {}: {e}", path.display()))
}

/// `(declaration name, verdict)` per leaf, in source order. `Ok(())` only when
/// the declaration registered — i.e. the kernel accepted the elaborated term.
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
                        ElabResult::Theorem { name, .. }
                        | ElabResult::Definition { name, .. }
                        | ElabResult::Axiom { name, .. } => {
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

/// All five declarations register: the two axioms, both controls, and — the
/// point of the fixture — the hijack probe.
///
/// MUTATION PROOF (both directions, run 2026-08-31): making
/// `binding_violates_declared_domain` return a constant `false` — the
/// "convenient approximation" of trusting the unifier — puts
/// `prop_binder_must_not_hijack` back to a kernel `TypeMismatch { expected:
/// Sort(Zero), inferred: Sort(Param v) }` and this test fails. Restricting the
/// guard to refuse EVERY binder it cannot judge (fail-closed instead of
/// fail-open) breaks `sort_binder_control` instead, because `capU`'s domain
/// `Sort u` mentions its own still-unsolved parameter. Both halves are load
/// bearing.
#[test]
fn test_simp_prop_binder_does_not_capture_sort_typed_term() {
    let verdicts = elab_fixture(FIXTURE);
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        [
            "capRhs",
            "capU",
            "prop_binder_control",
            "sort_binder_control",
            "prop_binder_must_not_hijack",
        ],
        "p52: declaration set moved — update the expected list deliberately"
    );
    let failures: Vec<String> = verdicts
        .iter()
        .filter_map(|(name, v)| v.as_ref().err().map(|e| format!("  {name}: {e}")))
        .collect();
    assert!(
        failures.is_empty(),
        "p52: {} of {} declarations rejected:\n{}",
        failures.len(),
        verdicts.len(),
        failures.join("\n")
    );
}
