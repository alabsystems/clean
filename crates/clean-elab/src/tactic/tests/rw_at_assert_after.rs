// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! G38 (ledger (108)): `rw … at h` whose rewritten type mentions a local
//! declared AFTER `h` places the new `h` after that local, as Lean's
//! `replaceLocalDecl` does (`findMaxFVar` + `assertAfter`). Clean refused it
//! with "replace_local_decl: cannot replace local 'h' with a type that depends
//! on later local 'b'", which masked 37–94 trust-ir declarations (round-4
//! triage M). Rows reproduce `r4-triage/M/`; pinned Lean 4.8.0 accepted the
//! positives and refused the negatives with the quoted message.

use clean_kernel::Environment;
use clean_parser::parse_file;

use crate::{elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext};

fn elab_last(code: &str) -> Result<(), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(code).expect("parse_file should succeed");
    let mut last = Err("nothing parsed".to_string());
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        last = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .map(|_| ())
            .map_err(|e| e.to_string());
    }
    last
}

/// M/min.lean.
#[test]
fn test_rw_at_hypothesis_declared_before_the_rewrite_target_local() {
    elab_last(
        "theorem min_repro (a : Nat) (h : a + 0 = 5) (b : Nat) (hab : a = b) : b = 5 := by\n  \
         rw [hab] at h\n  exact h\n",
    )
    .expect("Lean 4.8 accepts; the new `h` follows `b`");
}

/// M/min_negative.lean — Lean: "type mismatch … h has type b + 0 = 5".
/// The rewrite now succeeds, so the refusal must come from `exact`, never
/// from the placement.
#[test]
fn test_rw_at_later_local_negative_twin_is_refused_by_exact() {
    let err = elab_last(
        "theorem min_negative (a : Nat) (h : a + 0 = 5) (b : Nat) (hab : a = b) : b = 6 := by\n  \
         rw [hab] at h\n  exact h\n",
    )
    .expect_err("Lean refuses: `b + 0 = 5` is not `b = 6`");
    assert!(
        !err.contains("depends on later local"),
        "the placement no longer refuses: {err}"
    );
    assert!(
        err.to_lowercase().contains("type mismatch"),
        "refused at `exact`, as Lean refuses it: {err}"
    );
}

/// M/repro.lean: the `cases hg : g x` shape, where the case equation `hg`
/// (and the field `e`) come after `h`. The placement now succeeds; the row
/// still fails one step LATER, at `exact Except.noConfusion h` ("universe
/// level conflict: 0 vs ?u + 1"), which pinned Lean 4.8.0 accepts. That is a
/// separate `noConfusion` elaboration gap, pinned here as a refusal so it
/// fails loudly the day it closes (then: assert acceptance).
#[test]
fn test_rw_at_after_cases_with_equation_name_reaches_no_confusion() {
    let err = elab_last(
        "theorem repro (g : Nat → Except String Nat) (x : Nat)\n    \
         (h : (g x).bind (fun n => Except.ok (n + 1)) = Except.ok 5) : ∃ n, g x = Except.ok n := by\n  \
         cases hg : g x with\n  \
         | error e => rw [hg] at h; exact Except.noConfusion h\n  \
         | ok n => exact ⟨n, rfl⟩\n",
    )
    .expect_err("still open: Except.noConfusion's universe");
    assert!(
        !err.contains("depends on later local") && err.contains("universe level conflict"),
        "the rewrite is placed; the refusal is the later noConfusion step: {err}"
    );
}

/// M/negative.lean — Lean refuses `Except.noConfusion h` in the `ok` arm
/// ("type mismatch Except.noConfusion h … expected ∃ e, …"). Clean refuses it
/// one step earlier for the SAME open reason as the positive above (the
/// `noConfusion` universe), so this row cannot show Lean's reason yet: it is
/// pinned on that open reason, and flips to "type mismatch" the day the
/// `noConfusion` gap closes. The right-reason twin of the placement itself is
/// `simp_lean48_fidelity_review::test_rw_at_after_cases_twin_is_refused_by_exact`
/// (k2: Lean and Clean both "type mismatch" at `exact h`).
#[test]
fn test_rw_at_after_cases_negative_twin_is_refused() {
    let err = elab_last(
        "theorem negative (g : Nat → Except String Nat) (x : Nat)\n    \
         (h : (g x).bind (fun n => Except.ok (n + 1)) = Except.ok 5) : ∃ e, g x = Except.error e := by\n  \
         cases hg : g x with\n  \
         | error e => exact ⟨e, rfl⟩\n  \
         | ok n => rw [hg] at h; exact Except.noConfusion h\n",
    )
    .expect_err("Lean refuses");
    assert!(
        !err.contains("depends on later local") && err.contains("universe level conflict"),
        "refused at the open `noConfusion` step, not at the placement: {err}"
    );
}
