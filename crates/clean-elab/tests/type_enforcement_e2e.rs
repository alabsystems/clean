// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end z-probes for **B18 — elaborator-side type enforcement +
//! no-silent-sorryAx policy** (`docs/plans/GAP_SWEEP_2026-07-09.md`).
//!
//! Policy: in `clean check` a FAILED (non-explicit-`sorry`) elaboration must
//! NEVER register anything and NEVER inject `sorryAx`. A type mismatch at an
//! ascription `(e : T)` or a def-/theorem-body boundary is a LOUD typed
//! `ElabError` raised AT ELABORATION — not deferred to the kernel's `add_decl`
//! re-check (`KernelCheckFailed`), and not laundered into a synthetic
//! `sorryAx`. An EXPLICIT `sorry` still registers with the sorry axiom and
//! counts as a sorry (the one legitimate path).
//!
//! Lean ground truth: `src/Lean/Elab/Term.lean` (`ensureHasType` at every
//! ascription / expected-type boundary; `sorryAx` only on an explicit `sorry`).
//!
//! These tests drive the SAME pipeline as `clean check`
//! (`parse_file → preprocess_decl_with_context → elaborate_decl_and_register`),
//! so a pass/fail here matches the observable `clean check` verdict.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Parse + elaborate + kernel-check + register every decl in `source` on top of
/// the default prelude, short-circuiting on the first parse/elab/kernel/inner
/// failure. `Err` carries the first failure's rendered message.
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "inner declaration(s) failed:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
}

/// Like [`elaborate_module`] but registers EVERY decl (never short-circuits),
/// returning the resulting environment so a caller can inspect the transitive
/// axiom closure of a specific declaration (e.g. an explicit-`sorry` theorem
/// that legitimately registers with the sorry axiom).
fn elaborate_all(source: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).unwrap_or_else(|e| panic!("parse error: {e:?}"));
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let _ = elaborate_decl_and_register(&mut env, &processed);
    }
    env
}

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

/// Transitive axiom closure of a registered declaration.
fn axiom_closure(env: &Environment, name: &str) -> Option<Vec<String>> {
    env.axiom_deps(&Name::from_string(name))
        .map(|deps| deps.iter().map(ToString::to_string).collect())
}

fn assert_empty_closure(env: &Environment, name: &str) {
    let closure = axiom_closure(env, name)
        .unwrap_or_else(|| panic!("{name} should be registered with a computable value"));
    assert!(
        closure.is_empty(),
        "{name} must have an EMPTY axiom closure (no sorryAx), got {closure:?}"
    );
}

/// Assert `source` fails loud; return the rendered failure text.
fn expect_rejected(source: &str, what: &str) -> String {
    match elaborate_module(source) {
        Ok(_) => panic!("{what} must be REJECTED (fail-closed), but it fully elaborated"),
        Err(e) => e,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// 1. Ascription boundary — `(5 : Int)` against a `Nat` expected type
//    (term_sugar/p19). Loud `Type mismatch` at ELABORATION, NOT a kernel-
//    deferred `KernelCheckFailed`.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn b18_bad_ascription_is_loud_not_kernel_deferred() {
    let err = expect_rejected(
        "def badA : Nat := (5 : Int)",
        "`(5 : Int)` where `Nat` expected",
    );
    assert!(
        err.contains("Type mismatch"),
        "must be a typed TypeMismatch, got: {err}"
    );
    assert!(
        !err.contains("KernelCheckFailed"),
        "the mismatch must be caught at ELABORATION, never deferred to the kernel: {err}"
    );
    assert!(
        !err.to_lowercase().contains("sorryax"),
        "a failed ascription must not inject sorryAx: {err}"
    );
}

/// A plain literal against a mismatched declared type is equally loud (no
/// ascription wrapper needed): the def-body boundary enforces it too.
#[test]
fn b18_bad_def_body_type_is_loud() {
    let err = expect_rejected(
        "def bad2 : Bool := (5 : Nat)",
        "`(5 : Nat)` where `Bool` expected",
    );
    assert!(
        err.contains("Type mismatch"),
        "must be TypeMismatch, got: {err}"
    );
    assert!(
        !err.contains("KernelCheckFailed"),
        "must be loud at elab: {err}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 2. Def-body boundary — an under-applied `casesOn`/partial match
//    (match_variants/p13). Loud at elaboration, not kernel-deferred.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn b18_partial_match_def_is_loud() {
    let err = expect_rejected("def f13 : Nat → Nat\n  | 0 => 1\n", "partial-match `f13`");
    assert!(
        err.contains("Type mismatch"),
        "under-applied match body must be a loud TypeMismatch, got: {err}"
    );
    assert!(
        !err.contains("KernelCheckFailed"),
        "must be caught at elaboration, not deferred to the kernel: {err}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 3. No synthetic sorryAx on unresolvable dot-notation. Dot notation on a bare
//    (namespace-less) variable — `G.Adj` for `G : Type` — previously fell back
//    to a synthetic `sorryAx` placeholder "so the rest of the file can
//    elaborate", bumping the sorry-axiom counter on an unresolvable field.
//    (#3139 / elab_proj). It is now a LOUD `UnknownIdent`.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn b18_dot_notation_on_bare_var_is_loud_not_sorry() {
    let err = expect_rejected(
        "def usesAdj (G : Type) : Type := G.Adj",
        "`G.Adj` on a bare var",
    );
    assert!(
        !err.to_lowercase().contains("sorryax"),
        "unresolvable dot notation must be loud, never a synthetic sorryAx placeholder: {err}"
    );
    // A file whose only decl fails this way must register NOTHING as a sorry.
    let env = elaborate_all("def usesAdj (G : Type) : Type := G.Adj");
    assert!(
        axiom_closure(&env, "usesAdj").is_none(),
        "a failed dot-notation decl must not register (least of all as a sorry axiom)"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 4. Failed (non-sorry) theorem — LOUD, and NEVER registered as a sorry axiom.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn b18_failed_theorem_not_registered_as_sorry() {
    let src = "theorem bogus : (1 : Nat) = 2 := rfl";
    let err = expect_rejected(src, "`rfl : 1 = 2`");
    assert!(
        !err.to_lowercase().contains("sorryax"),
        "a failed proof must not become a sorry axiom: {err}"
    );
    // The bogus theorem must not be registered at all (elaboration failed
    // before kernel registration), so it has NO axiom closure.
    let env = elaborate_all(src);
    assert!(
        axiom_closure(&env, "bogus").is_none(),
        "a FAILED theorem must never be registered (least of all as a sorry axiom)"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 5. Explicit `sorry` — STILL the legitimate path: registers with the sorry
//    axiom and counts as a sorry.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn b18_explicit_sorry_still_registers_with_sorry_axiom() {
    let env = elaborate_all("theorem needs_proof : (1 : Nat) = 1 := sorry");
    let closure = axiom_closure(&env, "needs_proof")
        .expect("explicit-sorry theorem must still REGISTER (the legitimate sorry path)");
    assert!(
        closure.iter().any(|d| d.contains("sorry")),
        "explicit `sorry` must register WITH the sorry axiom in its closure, got {closure:?}"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// 6. Positives — valid ascriptions still elaborate to computable, sorry-free
//    values (empty-closure asserts). Regression guard for the new enforcement.
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn b18_valid_ascriptions_still_check_clean() {
    // `(3 : Int)` with no outer expected type (asB), and `(2 + 3 : Nat)`
    // against a `Nat` declared type (asA) — both value-pin by rfl.
    let env = elaborate_module(
        "def asB := (3 : Int)\n\
         theorem asB_pin : asB = 3 := rfl\n\
         def asA : Nat := (2 + 3 : Nat)\n\
         theorem asA_pin : asA = 5 := rfl\n",
    )
    .expect("valid ascriptions must still elaborate and kernel-check");
    assert_empty_closure(&env, "asB");
    assert_empty_closure(&env, "asB_pin");
    assert_empty_closure(&env, "asA");
    assert_empty_closure(&env, "asA_pin");
}
