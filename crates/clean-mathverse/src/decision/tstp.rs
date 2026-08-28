// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! TSTP — first-order ATP certificates.
//!
//! The second of the two certificate lanes this module imports (the other,
//! DRAT/LRAT SAT refutations, stays in [`super`]). A TSTP proof is a stream of
//! `fof(…)` / `cnf(…)` / `thf(…)` formula lines plus an SZS status line; the
//! whole lane is the four data types that shape it and the one parser that
//! reads it, so they are factored out together. Nothing here re-checks
//! anything — parsing a certificate is import, not verification; the trust and
//! axiom-profile verdicts stay with the provenance helpers in [`super`].

use super::CertError;

/// A step in a TSTP proof.
#[derive(Clone, Debug)]
pub struct TstpStep {
    pub name: String,
    pub role: TstpRole,
    pub formula: String,
    pub source: String,
}

/// Role of a TSTP formula.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TstpRole {
    Axiom,
    Hypothesis,
    Conjecture,
    NegatedConjecture,
    Lemma,
    Theorem,
    Plain,
}

/// Parsed TSTP proof.
#[derive(Clone, Debug)]
pub struct TstpProof {
    pub steps: Vec<TstpStep>,
    pub status: TstpStatus,
}

/// TSTP SZS status.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TstpStatus {
    Theorem,
    Unsatisfiable,
    CounterSatisfiable,
    Satisfiable,
    Unknown,
}

/// Parse a TSTP proof output.
pub fn parse_tstp(text: &str) -> Result<TstpProof, CertError> {
    let mut steps = Vec::new();
    let mut status = TstpStatus::Unknown;

    for line in text.lines() {
        let trimmed = line.trim();

        // SZS status line
        if trimmed.contains("SZS status") {
            if trimmed.contains("Theorem") {
                status = TstpStatus::Theorem;
            } else if trimmed.contains("Unsatisfiable") {
                status = TstpStatus::Unsatisfiable;
            } else if trimmed.contains("CounterSatisfiable") {
                status = TstpStatus::CounterSatisfiable;
            } else if trimmed.contains("Satisfiable") {
                status = TstpStatus::Satisfiable;
            }
            continue;
        }

        // TSTP formula: fof(name,role,formula,source).
        if trimmed.starts_with("fof(") || trimmed.starts_with("cnf(") || trimmed.starts_with("thf(")
        {
            if let Some(inner) = trimmed
                .strip_prefix("fof(")
                .or_else(|| trimmed.strip_prefix("cnf("))
                .or_else(|| trimmed.strip_prefix("thf("))
            {
                let inner = inner.trim_end_matches(").");
                let parts: Vec<&str> = inner.splitn(4, ',').collect();
                if parts.len() >= 3 {
                    let name = parts[0].trim().to_owned();
                    let role_str = parts[1].trim();
                    let formula = parts[2].trim().to_owned();
                    let source = parts.get(3).map_or("", |s| s.trim()).to_owned();

                    let role = match role_str {
                        "axiom" => TstpRole::Axiom,
                        "hypothesis" => TstpRole::Hypothesis,
                        "conjecture" => TstpRole::Conjecture,
                        "negated_conjecture" => TstpRole::NegatedConjecture,
                        "lemma" => TstpRole::Lemma,
                        "theorem" => TstpRole::Theorem,
                        _ => TstpRole::Plain,
                    };

                    steps.push(TstpStep {
                        name,
                        role,
                        formula,
                        source,
                    });
                }
            }
        }
    }

    Ok(TstpProof { steps, status })
}
