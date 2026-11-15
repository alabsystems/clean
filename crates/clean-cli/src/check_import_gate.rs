// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean check`'s use of [`clean_olean::ImportedConeGate`]: before a
//! declaration is counted as passed, its cited closure is re-admitted by the
//! kernel over the environment `clean check` built before any import, and a
//! closure that reaches `sorry` or an axiom from outside that base is not
//! credited. See `crates/clean-olean/src/recheck_closed/imported.rs` for what
//! was wrong and what the gate proves.

use clean_elab::ElabResult;
use clean_kernel::Environment;

/// Run the gate over `result`'s cone. `Ok(())` when the declaration may be
/// credited; otherwise the one-line reason it may not.
pub(crate) fn gate_declaration(
    gate: &mut clean_olean::ImportedConeGate,
    env: &Environment,
    result: &ElabResult,
    allow_sorry: bool,
) -> Result<(), String> {
    let roots = result.cited_roots(env);
    if roots.is_empty() {
        return Ok(());
    }
    let verdict = gate.check(env, &roots);
    if verdict.passed(allow_sorry) {
        Ok(())
    } else {
        Err(verdict.refusal_summary(allow_sorry))
    }
}

#[cfg(test)]
#[path = "check_import_gate_tests.rs"]
pub(crate) mod tests;
