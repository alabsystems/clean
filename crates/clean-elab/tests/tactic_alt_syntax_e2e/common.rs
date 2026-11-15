// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Shared harness for the trust-ir surface battery: parse -> elaborate ->
//! kernel re-check over the default prelude, the axiom-closure assertion
//! every positive row uses, and the refusal assertion every twin uses.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::{parse_file, SurfaceDecl};

/// The name a refusal is reported under: the declaration's own name for a
/// `def`/`theorem`, its span otherwise.
fn decl_label(decl: &SurfaceDecl) -> String {
    match decl {
        SurfaceDecl::Theorem { name, .. } | SurfaceDecl::Def { name, .. } => name.to_string(),
        other => format!("<declaration at {:?}>", other.span()),
    }
}

/// Parse + elaborate + kernel-check + register every decl in `source` on top
/// of the default prelude. Err carries the first failure, a parser-recovery
/// placeholder included, prefixed by the failing declaration's name and `: `.
pub(crate) fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("<parse>: parse error: {e:?}"))?;
    for decl in &decls {
        let label = decl_label(decl);
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .map_err(|e| format!("{label}: elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(format!(
                "{label}: inner declaration(s) failed:\n{}",
                failures.join("\n")
            ));
        }
    }
    Ok(env)
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

pub(crate) fn expect_accepted(source: &str, what: &str) -> Environment {
    elaborate_module(source).unwrap_or_else(|e| panic!("{what} must elaborate: {e}"))
}

/// The declaration is registered and depends on no DOMAIN-SPECIFIC axiom.
///
/// `Environment::axiom_deps` leaves out the foundational axioms (`propext`,
/// `Quot.sound`, `Classical.choice`; `axiom_audit.rs`), so this does not see
/// a `Classical` dependency — a row whose claim is "no axiom at all" uses
/// [`assert_no_axioms`].
pub(crate) fn assert_axiom_free(env: &Environment, name: &str) {
    let deps = env
        .axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert!(
        deps.is_empty(),
        "{name} must depend on no domain-specific axiom, depends on {deps:?}"
    );
}

/// The declaration depends on no axiom at all, foundational ones included —
/// Lean's "'name' does not depend on any axioms".
pub(crate) fn assert_no_axioms(env: &Environment, name: &str) {
    assert_axiom_free(env, name);
    let foundational = env
        .foundational_axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert!(
        foundational.is_empty(),
        "{name} must depend on no axiom at all, depends on {foundational:?}"
    );
}

/// `source` elaborates, and each of `names` is registered depending on no
/// domain-specific axiom ([`assert_axiom_free`]).
pub(crate) fn expect_axiom_free(source: &str, what: &str, names: &[&str]) {
    let env = expect_accepted(source, what);
    for name in names {
        assert_axiom_free(&env, name);
    }
}

/// `source` is refused; returns the refusal. Prefer [`expect_refused_at`].
pub(crate) fn expect_refused(source: &str, what: &str) -> String {
    match elaborate_module(source) {
        Ok(_) => panic!("{what} must be rejected (Lean 4.8 rejects it), but it kernel-checked"),
        Err(e) => e,
    }
}

/// `source` is refused AT the declaration `decl` — not at an earlier one the
/// row only sets up — and, when `reasons` is non-empty, for one of them
/// (compared case-insensitively). Returns the refusal.
///
/// Every twin names the declaration Lean refuses, so a twin cannot pass
/// because its scaffolding broke; the reasons pin the class of failure
/// where Clean's wording is fixed by its error type.
pub(crate) fn expect_refused_at(source: &str, what: &str, decl: &str, reasons: &[&str]) -> String {
    let err = expect_refused(source, what);
    let label = format!("{decl}: ");
    let Some(reason_text) = err.strip_prefix(&label) else {
        panic!("{what}: the refusal must be at `{decl}`, got: {err}");
    };
    // The reason is matched AFTER the label: the label spells the
    // declaration's own name, which a reason word could otherwise match.
    let lower = reason_text.to_lowercase();
    assert!(
        reasons.is_empty()
            || reasons
                .iter()
                .any(|reason| lower.contains(&reason.to_lowercase())),
        "{what}: the refusal must be one of {reasons:?}, got: {err}"
    );
    err
}

/// `rw` found no instance of the rule's left-hand side.
pub(crate) const NO_MATCH: &[&str] = &["did not match", "RewriteNoMatch"];
/// `simp` rewrote nothing.
pub(crate) const NO_PROGRESS: &[&str] = &["no progress", "NoProgress"];
/// A term, or a closing proof, has the wrong type.
pub(crate) const MISMATCH: &[&str] = &[
    "mismatch",
    "unif",
    "definitionally equal",
    "defeq",
    "kernel check failed",
];

pub(crate) const OPT_FN: &str = "def f : Nat → Option Nat\n  | 0 => none\n  | n+1 => some n\n\n";
