// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only accounting over the loader's ordered base/server/private summaries.
//! Stored unsafe/partial metadata is evidence of exclusion from Lean replay,
//! never evidence that the skipped declaration was checked or proved.

use clean_olean::LoadSummary;
use std::collections::{BTreeMap, BTreeSet};

const COMPILER_ARTIFACT: &str = "compiler/code-generator artifact (not kernel-checkable)";

pub(super) struct SkippedRow<'a> {
    pub summary_ordinal: usize,
    pub row_ordinal: usize,
    pub module: Option<&'a str>,
    artifact: Option<&'a str>,
    pub name: &'a str,
    pub reason: &'a str,
    pub excluded_from_replay: bool,
}

pub(super) struct SkippedAudit<'a> {
    // Keep every raw occurrence, including repetitions across artifact parts.
    pub rows: Vec<SkippedRow<'a>>,
    pub accounting_errors: Vec<String>,
}

impl SkippedAudit<'_> {
    pub fn excluded_count(&self) -> usize {
        self.rows
            .iter()
            .filter(|row| row.excluded_from_replay)
            .count()
    }

    pub fn failure_count(&self) -> usize {
        self.rows.len() - self.excluded_count()
    }
}

pub(super) fn audit_skipped_constants(summaries: &[LoadSummary]) -> SkippedAudit<'_> {
    let mut audit = SkippedAudit {
        rows: Vec::new(),
        accounting_errors: Vec::new(),
    };
    let mut last_eligibility: BTreeMap<&str, BTreeMap<&str, bool>> = BTreeMap::new();
    let mut owners: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    let mut last_part = BTreeMap::new();

    for (summary_ordinal, summary) in summaries.iter().enumerate() {
        let label = summary
            .module_name
            .as_deref()
            .filter(|name| !name.is_empty());
        // Exact labels emitted by load_artifact_parts and accepted together by
        // replay_module::part_labels, not suffixes of declaration names.
        let identity = label.map(|label| {
            if let Some(module) = label.strip_suffix("._private") {
                (module, 2)
            } else if let Some(module) = label.strip_suffix("._server") {
                (module, 1)
            } else {
                (label, 0)
            }
        });
        let module = identity
            .map(|(module, _)| module)
            .filter(|name| !name.is_empty());
        if let Some((module, part)) = identity {
            let previous = last_part.insert(module, part);
            if (part == 0 && previous.is_some())
                || (part != 0 && previous.is_none_or(|previous| previous >= part))
            {
                audit.accounting_errors.push(format!(
                    "summary {summary_ordinal} {label:?}: missing, repeated or out-of-order artifact part"
                ));
            }
        }
        let mut raw_names = BTreeMap::<&str, usize>::new();
        for row in &summary.skipped_constants {
            *raw_names.entry(&row.name).or_default() += 1;
        }
        let mut eligible_names = BTreeSet::new();
        for name in &summary.skipped_not_replayable {
            if !eligible_names.insert(name.as_str()) || raw_names.get(name.as_str()) != Some(&1) {
                audit.accounting_errors.push(format!(
                    "summary {summary_ordinal} {module:?}: orphan/ambiguous eligibility for {name}"
                ));
            }
        }
        for (name, count) in &raw_names {
            if *count != 1 {
                audit.accounting_errors.push(format!(
                    "summary {summary_ordinal} {module:?}: {count} raw occurrences of {name}"
                ));
            }
        }
        if module.is_none() && (!raw_names.is_empty() || !eligible_names.is_empty()) {
            audit.accounting_errors.push(format!(
                "summary {summary_ordinal}: missing module identity"
            ));
        }
        // Later resident, shadowed or restated declarations cannot inherit an
        // earlier skipped part's eligibility. These rows do not supply their
        // safety; fail closed rather than treating an older mark as current.
        for name in summary
            .added_names
            .iter()
            .chain(summary.shadowed_declarations.iter().map(|(name, _)| name))
            .chain(
                summary
                    .restated_declarations
                    .iter()
                    .map(|(name, _, _)| name),
            )
        {
            let label = name.to_string();
            if let Some(module) = module {
                if let Some(eligible) = last_eligibility
                    .get_mut(module)
                    .and_then(|names| names.get_mut(label.as_str()))
                {
                    *eligible = false;
                }
            }
        }
        for (row_ordinal, row) in summary.skipped_constants.iter().enumerate() {
            if let Some(module) = module {
                owners.entry(&row.name).or_default().insert(module);
                // Like replay_module::declared: the LAST stored skipped part
                // determines safety, not any earlier part or a name heuristic.
                last_eligibility.entry(module).or_default().insert(
                    row.name.as_str(),
                    eligible_names.contains(row.name.as_str())
                        && raw_names[&row.name.as_str()] == 1,
                );
            }
            audit.rows.push(SkippedRow {
                summary_ordinal,
                row_ordinal,
                module: label,
                artifact: module,
                name: &row.name,
                reason: &row.reason,
                excluded_from_replay: false,
            });
        }
        for (name, reason) in &summary.refused_completions {
            audit.accounting_errors.push(format!(
                "summary {summary_ordinal} {module:?}: kernel refused completion {name}: {reason}"
            ));
        }
    }
    for (name, modules) in &owners {
        if modules.len() != 1 {
            audit
                .accounting_errors
                .push(format!("ambiguous skipped identity {name}: {modules:?}"));
        }
    }
    for row in &mut audit.rows {
        // An unsafe label must never excuse a conversion or kernel refusal.
        // The exact reason identifies the loader branch, not eligibility; that
        // independently requires final stored unsafe/partial classification.
        row.excluded_from_replay = row.reason == COMPILER_ARTIFACT
            && owners
                .get(row.name)
                .is_some_and(|modules| modules.len() == 1)
            && row.artifact.is_some_and(|module| {
                last_eligibility
                    .get(module)
                    .and_then(|names| names.get(row.name))
                    == Some(&true)
            });
    }
    audit
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_olean::SkippedConstant;

    fn part(module: Option<&str>, rows: &[(&str, &str)], eligible: &[&str]) -> LoadSummary {
        let mut summary = LoadSummary::default();
        summary.module_name = module.map(str::to_owned);
        summary.skipped_constants = rows
            .iter()
            .map(|(name, reason)| SkippedConstant {
                name: (*name).to_owned(),
                reason: (*reason).to_owned(),
            })
            .collect();
        summary.skipped_not_replayable = eligible.iter().map(|name| (*name).to_owned()).collect();
        summary
    }

    #[test]
    fn final_private_safety_preserves_all_raw_parts_without_name_heuristics() {
        let summaries = [
            part(Some("Init.A"), &[("plain_name", COMPILER_ARTIFACT)], &[]),
            part(
                Some("Init.A._server"),
                &[("plain_name", COMPILER_ARTIFACT)],
                &["plain_name"],
            ),
            part(
                Some("Init.A._private"),
                &[("plain_name", COMPILER_ARTIFACT)],
                &["plain_name"],
            ),
        ];
        let audit = audit_skipped_constants(&summaries);
        assert_eq!(audit.rows.len(), 3);
        assert_eq!(audit.excluded_count(), 3);
        assert_eq!(audit.failure_count(), 0);
        assert!(audit.accounting_errors.is_empty());
        assert_eq!(
            audit.rows.iter().map(|row| row.module).collect::<Vec<_>>(),
            vec![
                Some("Init.A"),
                Some("Init.A._server"),
                Some("Init.A._private")
            ]
        );
        assert_eq!(
            audit
                .rows
                .iter()
                .map(|row| (row.summary_ordinal, row.row_ordinal))
                .collect::<Vec<_>>(),
            vec![(0, 0), (1, 0), (2, 0)]
        );
    }

    #[test]
    fn conversion_and_kernel_refusals_cannot_borrow_unsafe_eligibility() {
        for reason in [
            "type conversion failed",
            "axiom stub upgrade refused (kernel check): mismatch",
        ] {
            let summaries = [part(
                Some("Init.A"),
                &[("f._unsafe_rec", reason)],
                &["f._unsafe_rec"],
            )];
            let audit = audit_skipped_constants(&summaries);
            assert_eq!(audit.failure_count(), 1);
            assert_eq!(audit.excluded_count(), 0);
        }
        let mut summary = part(Some("Init.A"), &[("f", COMPILER_ARTIFACT)], &["f"]);
        summary
            .refused_completions
            .push((clean_kernel::name::Name::from_string("f"), "refused".into()));
        assert_eq!(
            audit_skipped_constants(&[summary]).accounting_errors.len(),
            1
        );
    }

    #[test]
    fn missing_or_orphan_or_duplicate_eligibility_never_passes() {
        let summaries = [part(
            Some("Init.A"),
            &[("f._unsafe_rec", COMPILER_ARTIFACT)],
            &[],
        )];
        assert_eq!(audit_skipped_constants(&summaries).failure_count(), 1);
        for summary in [
            part(Some("Init.A"), &[("f", COMPILER_ARTIFACT)], &["unrelated"]),
            part(Some("Init.A"), &[("f", COMPILER_ARTIFACT)], &["f", "f"]),
            part(None, &[("f", COMPILER_ARTIFACT)], &["f"]),
            part(Some(""), &[("f", COMPILER_ARTIFACT)], &["f"]),
            part(
                Some("Init.A"),
                &[("f", COMPILER_ARTIFACT), ("f", COMPILER_ARTIFACT)],
                &["f"],
            ),
        ] {
            let audit = audit_skipped_constants(std::slice::from_ref(&summary));
            assert!(!audit.accounting_errors.is_empty());
            assert_eq!(audit.rows.len(), summary.skipped_constants.len());
        }
    }

    #[test]
    fn later_safe_part_revokes_earlier_unsafe_status() {
        let summaries = [
            part(Some("Init.A"), &[("f", COMPILER_ARTIFACT)], &["f"]),
            part(Some("Init.A._private"), &[("f", COMPILER_ARTIFACT)], &[]),
        ];
        let audit = audit_skipped_constants(&summaries);
        assert_eq!(audit.rows.len(), 2);
        assert_eq!(audit.failure_count(), 2);
        assert!(audit.accounting_errors.is_empty());
        let mut resident = part(Some("Init.A._private"), &[], &[]);
        resident
            .added_names
            .push(clean_kernel::name::Name::from_string("f"));
        let summaries = [summaries[0].clone(), resident];
        assert_eq!(audit_skipped_constants(&summaries).failure_count(), 1);
    }

    #[test]
    fn later_shadow_or_restatement_cannot_reuse_an_old_safety_mark() {
        let unsafe_part = part(Some("Init.A"), &[("f", COMPILER_ARTIFACT)], &["f"]);
        let mut shadow = part(Some("Init.A._private"), &[], &[]);
        shadow
            .shadowed_declarations
            .push((clean_kernel::name::Name::from_string("f"), "other".into()));
        let mut restated = part(Some("Init.A._private"), &[], &[]);
        restated.restated_declarations.push((
            clean_kernel::name::Name::from_string("f"),
            "Init.A".into(),
            true,
        ));
        for later in [shadow, restated] {
            let summaries = [unsafe_part.clone(), later];
            let audit = audit_skipped_constants(&summaries);
            assert_eq!(audit.rows.len(), 1);
            assert_eq!(audit.failure_count(), 1);
            assert!(audit.accounting_errors.is_empty());
        }
    }

    #[test]
    fn companion_identity_requires_base_and_forward_part_order() {
        let base = part(Some("Init.A"), &[("f", COMPILER_ARTIFACT)], &["f"]);
        let server = part(Some("Init.A._server"), &[("f", COMPILER_ARTIFACT)], &["f"]);
        let private = part(Some("Init.A._private"), &[("f", COMPILER_ARTIFACT)], &["f"]);
        for summaries in [
            vec![private.clone()],
            vec![base.clone(), base.clone()],
            vec![base, private, server],
        ] {
            let audit = audit_skipped_constants(&summaries);
            assert_eq!(audit.rows.len(), summaries.len());
            assert!(!audit.accounting_errors.is_empty());
        }
    }

    #[test]
    fn another_module_cannot_supply_or_override_eligibility() {
        let summaries = [
            part(Some("Init.A"), &[("f", COMPILER_ARTIFACT)], &[]),
            part(Some("Init.B"), &[], &["f"]),
        ];
        let audit = audit_skipped_constants(&summaries);
        assert_eq!(audit.failure_count(), 1);
        assert!(!audit.accounting_errors.is_empty());
        let summaries = [
            summaries[0].clone(),
            part(Some("Init.B"), &[("f", COMPILER_ARTIFACT)], &["f"]),
        ];
        let audit = audit_skipped_constants(&summaries);
        assert_eq!(audit.failure_count(), 2);
        assert!(!audit.accounting_errors.is_empty());
    }
}
