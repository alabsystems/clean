// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! [`RecheckLevel`]: the vocabulary a re-check report may use, one level per
//! re-check the tree runs.

use serde::Serialize;

/// How much of a target's dependency cone a re-check actually re-derived.
///
/// Every level here exists in the tree today. The point of naming them is that
/// a report may only use the vocabulary of the level it ran: the strings in
/// [`Self::proves`] and [`Self::does_not_prove`] are the sanctioned wording.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum RecheckLevel {
    /// [`crate::verify_batch_full::typecheck_constants_full`]: `infer_sort` on
    /// each named constant's type and `check_type` on its value, in the
    /// environment that already holds every other imported declaration.
    LocalAssumedEnv,
    /// [`Environment::audit_certification`](clean_kernel::env::Environment::audit_certification): walks the type/value closure and
    /// re-runs the strict read-only declaration check on each reachable
    /// declaration — still in the assumed environment, and still without
    /// re-deriving any inductive computation rule.
    ClosureAssumedEnv,
    /// [`super::recheck_closed`]: fresh `add_decl` / `add_inductive_core` replay of the
    /// whole cone in dependency order into an initially empty environment.
    ClosedReplay,
    /// [`super::ImportedConeGate`]: the same replay, but over the CONSUMER'S OWN
    /// kernel base (the environment it built before loading any import)
    /// instead of an empty one. Every cone member outside that base is
    /// re-admitted through `add_decl` / `add_inductive_core`.
    ImportedOverBase,
}

impl RecheckLevel {
    /// Stable machine token for logs, JSON and CLI output.
    ///
    /// Deliberately not the word "full": the weaker two levels used to be
    /// reported as `kernel-verified-full`, which is what let a lane print
    /// "re-checked" for a check that re-derived one declaration in an assumed
    /// environment.
    #[must_use]
    pub fn token(self) -> &'static str {
        match self {
            Self::LocalAssumedEnv => "local-assumed-env",
            Self::ClosureAssumedEnv => "closure-assumed-env",
            Self::ClosedReplay => "dependency-closed-replay",
            Self::ImportedOverBase => "imported-cone-over-base",
        }
    }

    /// One sentence naming exactly what a PASS at this level establishes.
    #[must_use]
    pub fn proves(self) -> &'static str {
        match self {
            Self::LocalAssumedEnv => {
                "each named declaration's type inhabits a Sort and its value has that type, \
                 ASSUMING every other declaration already in the environment is correct"
            }
            Self::ClosureAssumedEnv => {
                "every declaration reachable from the goal and term passes the strict \
                 read-only declaration check, ASSUMING the environment's inductive \
                 computation rules are correct"
            }
            Self::ClosedReplay => {
                "every constant in the target's transitive cone was re-admitted by the kernel \
                 in dependency order against only previously re-admitted constants, with every \
                 inductive family re-validated and its recursor rules regenerated rather than \
                 imported"
            }
            Self::ImportedOverBase => {
                "every constant in the cone that the consumer did not build itself (every \
                 imported declaration, and every declaration that cites one) was re-admitted \
                 by the kernel in dependency order against only the consumer's own base and \
                 previously re-admitted constants, with every imported inductive family \
                 re-validated and its recursor rules regenerated rather than imported"
            }
        }
    }

    /// One sentence naming what a PASS at this level does NOT establish.
    #[must_use]
    pub fn does_not_prove(self) -> &'static str {
        match self {
            Self::LocalAssumedEnv => {
                "it does not re-derive anything the declaration REFERENCES, does not visit the \
                 dependency cone, does not validate inductive rules, and grants no import \
                 authority: a pass here is not a re-check of the cone"
            }
            Self::ClosureAssumedEnv => {
                "it does not re-derive any inductive computation rule: a tampered recursor \
                 ι-rule right-hand side is admitted structurally and never re-checked, and \
                 every declaration is checked against an environment that still contains the \
                 unchecked ones"
            }
            Self::ClosedReplay => {
                "it does not authenticate the bytes it replayed beyond the names the kernel \
                 reduces by name (those must match the pinned extension-binding table), it \
                 re-derives nothing about the axioms it admitted — a PASS is conditional on \
                 every one of them — and it trusts the kernel's built-in by-name reductions \
                 for the bound names to compute what the pinned declarations compute"
            }
            Self::ImportedOverBase => {
                "it re-derives nothing in the consumer's own base (the prelude it built \
                 before loading any import): that base is trusted exactly as a same-session \
                 check trusts it, native reducers included; it re-derives nothing about the \
                 axioms it admitted; and it trusts the kernel's by-name reductions for the \
                 names bound by the pinned table"
            }
        }
    }

    /// Whether a pass at this level may be cited as the re-check behind a
    /// `Certified`-class claim. True for [`Self::ClosedReplay`] only.
    #[must_use]
    pub(crate) fn may_ground_certified_class(self) -> bool {
        matches!(self, Self::ClosedReplay)
    }
}
