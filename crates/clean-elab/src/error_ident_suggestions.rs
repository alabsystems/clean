// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The reporting-boundary "did you mean" step of [`ElabError`]: deferred
//! unknown-identifier errors get their nearest theorem names. Split out of
//! `error.rs` at the round-6 integration to keep that file under the paragon
//! ratchet's 1000-line bound.

use super::ElabError;
use crate::tactic::TacticError;

impl ElabError {
    /// Compute the "nearest theorem names" of every
    /// [`ElabError::UnknownIdentDeferred`] this error carries, against `env`.
    ///
    /// Called where an error is REPORTED (the elaborator's per-declaration
    /// boundary and its public entry points), never on a path that may still
    /// catch the error and try something else. Looks through the typed
    /// wrappers an elaboration error travels in (`InTactic`, a tactic's
    /// `UpstreamElabError`, `AutomationBudgetExhausted`); an error some layer
    /// already rendered to a string keeps the plain `Unknown identifier: …`
    /// text it was rendered with.
    #[must_use]
    pub(crate) fn with_ident_suggestions(self, env: &clean_kernel::Environment) -> Self {
        match self {
            Self::UnknownIdentDeferred {
                name,
                namespace_prefix,
                fallback,
            } => {
                let suggestions =
                    crate::infer::nearest_theorem_names(env, &namespace_prefix, &name, 5);
                if suggestions.is_empty() {
                    match fallback {
                        Some(fallback) => fallback.with_ident_suggestions(env),
                        None => Self::UnknownIdent(name),
                    }
                } else {
                    Self::UnknownIdentWithSuggestions { name, suggestions }
                }
            }
            Self::InTactic {
                tactic,
                chain,
                span_start,
                span_end,
                source,
            } => Self::InTactic {
                tactic,
                chain,
                span_start,
                span_end,
                source: Box::new(source.with_ident_suggestions(env)),
            },
            Self::TacticFailed(TacticError::UpstreamElabError { source }) => {
                Self::TacticFailed(TacticError::UpstreamElabError {
                    source: Box::new(source.with_ident_suggestions(env)),
                })
            }
            Self::AutomationBudgetExhausted {
                limit,
                site,
                underlying,
            } => Self::AutomationBudgetExhausted {
                limit,
                site,
                underlying: Box::new(underlying.with_ident_suggestions(env)),
            },
            Self::DerivingHandlerFailed {
                class,
                type_name,
                error,
            } => Self::DerivingHandlerFailed {
                class,
                type_name,
                error: Box::new(error.with_ident_suggestions(env)),
            },
            other => other,
        }
    }
}
