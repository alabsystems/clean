// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Test-only quantifier and trigger-formatting helpers for AyProofBackend.

use super::AyProofBackend;
use crate::bridge::ay_backend::triggers::SmtlibTriggerPattern;
use ay_core::quote_symbol;

impl AyProofBackend {
    /// Build a `forall` SMT-LIB formula with explicit trigger patterns.
    ///
    /// Returns a fully-formed SMT-LIB expression that can be passed to
    /// [`Self::assert_formula`].
    pub(crate) fn forall_with_triggers(
        &self,
        vars: &[(&str, &str)],
        body: &str,
        triggers: &[SmtlibTriggerPattern],
    ) -> String {
        self.format_quantifier_with_triggers("forall", vars, body, triggers)
    }

    /// Build an `exists` SMT-LIB formula with explicit trigger patterns.
    ///
    /// Returns a fully-formed SMT-LIB expression that can be passed to
    /// [`Self::assert_formula`].
    pub(crate) fn exists_with_triggers(
        &self,
        vars: &[(&str, &str)],
        body: &str,
        triggers: &[SmtlibTriggerPattern],
    ) -> String {
        self.format_quantifier_with_triggers("exists", vars, body, triggers)
    }

    fn format_quantifier_with_triggers(
        &self,
        quantifier: &str,
        vars: &[(&str, &str)],
        body: &str,
        triggers: &[SmtlibTriggerPattern],
    ) -> String {
        let vars_smt = vars
            .iter()
            .map(|(name, sort)| format!("({} {})", quote_symbol(name), sort))
            .collect::<Vec<_>>()
            .join(" ");

        let non_empty_triggers: Vec<&SmtlibTriggerPattern> = triggers
            .iter()
            .filter(|pattern| !pattern.is_empty())
            .collect();
        let body_smt = if non_empty_triggers.is_empty() {
            body.to_string()
        } else {
            let trigger_smt = non_empty_triggers
                .iter()
                .map(|pattern| format!(" :pattern ({})", pattern.to_smtlib_terms()))
                .collect::<String>();
            format!("(! {}{})", body, trigger_smt)
        };

        format!("({} ({}) {})", quantifier, vars_smt, body_smt)
    }
}
