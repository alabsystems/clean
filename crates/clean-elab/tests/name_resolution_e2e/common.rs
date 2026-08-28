// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Shared harness for the B03 name-resolution battery: parse -> elaborate ->
//! kernel re-check over the default prelude, plus the axiom-closure
//! assertions every positive row uses. Split out of `name_resolution_e2e.rs`
//! for file size.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

/// Parse + elaborate + kernel-check + register every decl in `source` on top
/// of the default prelude. Err carries the first failure.
pub(crate) fn elaborate_module(source: &str) -> Result<Environment, String> {
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

pub(crate) fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
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

/// Assert `source` fails somewhere in parse/elab/kernel (fail-closed), and
/// return the failure text for shape assertions.
pub(crate) fn expect_rejected(source: &str, what: &str) -> String {
    match elaborate_module(source) {
        Ok(_) => {
            panic!("{what} must be rejected (fail-closed), but it elaborated and kernel-checked")
        }
        Err(e) => e,
    }
}

pub(crate) fn axiom_closure(env: &Environment, name: &str) -> Vec<String> {
    env.axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"))
        .iter()
        .map(ToString::to_string)
        .collect()
}

pub(crate) fn assert_axiom_free(env: &Environment, names: &[&str]) {
    for name in names {
        assert!(
            axiom_closure(env, name).is_empty(),
            "{name} must have an EMPTY transitive axiom closure (no sorry, no new axioms)"
        );
    }
}
