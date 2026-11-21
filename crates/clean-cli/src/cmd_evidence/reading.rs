// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The common shape every figure adapter reads its record into.
//!
//! A reading carries the fields of the `clean.evidence/v1` envelope that an
//! existing record can supply: value, denominator with its digest, labels,
//! non-claims, commit and freshness. Freshness is decided only by comparing a
//! recorded input digest with the current inputs; a record without one reads
//! `unknown`, never fresh.

use crate::EvidenceCheckError;
use clean_evidence::envelope::FreshnessState;
use serde::Serialize;
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::BTreeSet;
use std::fmt::Write as _;

/// What a figure adapter found: a measured reading, or a figure that has no
/// record that could back it, with the reason.
pub(super) enum Outcome {
    Measured(Box<Reading>),
    Absent { reason: String },
}

#[derive(Serialize)]
pub(super) struct Reading {
    pub(super) value: Value,
    /// One sentence for the text and Markdown renderings.
    #[serde(skip)]
    pub(super) summary: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) denominator: Option<DenominatorReading>,
    pub(super) labels: Vec<String>,
    pub(super) non_claims: Vec<String>,
    /// The Clean commit the record names as measured, when it names one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) commit: Option<String>,
    /// The date or timestamp the record names as its measurement time.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(super) recorded_at: Option<String>,
    pub(super) freshness: FreshnessReading,
}

impl Reading {
    /// A reading with no labels, no denominator and unknown freshness.
    #[must_use]
    pub(super) fn new(value: Value, summary: String, freshness: FreshnessReading) -> Self {
        Self {
            value,
            summary,
            denominator: None,
            labels: Vec::new(),
            non_claims: Vec::new(),
            commit: None,
            recorded_at: None,
            freshness,
        }
    }
}

#[derive(Debug, Serialize, PartialEq, Eq)]
pub(super) struct DenominatorReading {
    pub(super) count: u64,
    /// `sha256:` over the sorted, length-framed members, so a denominator that
    /// grows or changes membership never reads as the same denominator.
    pub(super) digest: String,
    pub(super) scope: String,
}

impl DenominatorReading {
    /// Digest a set of members. Blank or duplicate members are refused,
    /// because a denominator must name each counted item once.
    pub(super) fn of_members<I, S>(
        scope: &str,
        count: u64,
        members: I,
    ) -> Result<Self, EvidenceCheckError>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let mut seen = BTreeSet::new();
        for member in members {
            let member = member.into();
            if member.trim().is_empty() {
                return Err(EvidenceCheckError::Invalid(format!(
                    "{scope}: blank denominator member"
                )));
            }
            if let Some(duplicate) = seen.replace(member) {
                return Err(EvidenceCheckError::Invalid(format!(
                    "{scope}: duplicate denominator member {duplicate:?}"
                )));
            }
        }
        let mut hasher = Sha256::new();
        for member in &seen {
            hasher.update((member.len() as u64).to_le_bytes());
            hasher.update(member.as_bytes());
        }
        let mut digest = String::from("sha256:");
        for byte in hasher.finalize() {
            let _ = write!(digest, "{byte:02x}");
        }
        Ok(Self {
            count,
            digest,
            scope: scope.to_owned(),
        })
    }

    /// A denominator whose count is the number of distinct members.
    pub(super) fn counting<I, S>(scope: &str, members: I) -> Result<Self, EvidenceCheckError>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let mut counted = 0u64;
        let mut reading =
            Self::of_members(scope, 0, members.into_iter().inspect(|_| counted += 1))?;
        reading.count = counted;
        Ok(reading)
    }
}

#[derive(Debug, Serialize, PartialEq, Eq)]
pub(super) struct FreshnessReading {
    pub(super) state: FreshnessState,
    pub(super) reason: String,
}

impl FreshnessReading {
    #[must_use]
    pub(super) fn unknown(reason: &str) -> Self {
        Self {
            state: FreshnessState::Unknown,
            reason: reason.to_owned(),
        }
    }

    #[must_use]
    pub(super) fn fresh(reason: &str) -> Self {
        Self {
            state: FreshnessState::Fresh,
            reason: reason.to_owned(),
        }
    }

    #[must_use]
    pub(super) fn stale(reason: String) -> Self {
        Self {
            state: FreshnessState::Stale,
            reason,
        }
    }

    #[must_use]
    pub(super) fn label(&self) -> &'static str {
        match self.state {
            FreshnessState::Fresh => "fresh",
            FreshnessState::Stale => "stale",
            _ => "unknown",
        }
    }
}

/// The freshness every record without an input digest reports.
pub(super) const NO_INPUT_DIGEST: &str =
    "the record carries no digest of its measured inputs, so freshness is not decidable offline";

/// Strings from a static table, for labels and non-claims.
pub(super) fn owned(lines: &[&str]) -> Vec<String> {
    lines.iter().map(|line| (*line).to_owned()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_denominator_digest_ignores_member_order() {
        let one = DenominatorReading::counting("scope", ["b", "a"]).unwrap();
        let two = DenominatorReading::counting("scope", ["a", "b"]).unwrap();
        assert_eq!(one, two);
        assert_eq!(one.count, 2);
        assert!(one.digest.starts_with("sha256:"));
    }

    #[test]
    fn test_denominator_digest_growth_changes_digest() {
        let before = DenominatorReading::counting("scope", ["a", "b"]).unwrap();
        let after = DenominatorReading::counting("scope", ["a", "b", "c"]).unwrap();
        assert_ne!(before.digest, after.digest);
        let framed = DenominatorReading::counting("scope", ["ab", "c"]).unwrap();
        let split = DenominatorReading::counting("scope", ["a", "bc"]).unwrap();
        assert_ne!(framed.digest, split.digest);
    }

    #[test]
    fn test_denominator_duplicate_or_blank_member_is_refused() {
        for members in [vec!["a", "a"], vec!["a", " "]] {
            let error = DenominatorReading::counting("scope", members).unwrap_err();
            assert!(matches!(error, EvidenceCheckError::Invalid(_)));
        }
    }
}
