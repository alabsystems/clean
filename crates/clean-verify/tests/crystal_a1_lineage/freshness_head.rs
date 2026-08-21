// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Freshness gate for chains newer than the last cross-producer revalidation.

use super::*;

/// **The gate for a chain that landed after the last revalidation.**
///
/// It replaces nothing: the two tests in the parent module still require both
/// pointer blocks of every other chain. What it adds is the requirement a row
/// in [`HEAD_MEASURED`] has to meet instead — and the requirement is not
/// weaker, because it is checked against a committed report that covers EVERY
/// fixture in the tree, on ONE dump. A report that only covered the new body
/// would be a file comparing itself.
#[test]
fn every_head_measured_chain_names_its_own_live_dump_record() {
    for stem in HEAD_MEASURED {
        let file = EVIDENCE
            .iter()
            .find(|(s, _)| s == stem)
            .map(|(_, f)| *f)
            .unwrap_or_else(|| panic!("{stem} is in HEAD_MEASURED but not in EVIDENCE"));
        let ev = evidence(file);
        let hm = &ev["head_measurement"];
        assert!(
            hm.is_object(),
            "{file} is in HEAD_MEASURED and carries no `head_measurement` block. A fixture with \
             neither that nor `superseded_at_head` is a pin nothing re-derives."
        );
        let rel = hm["record"]
            .as_str()
            .unwrap_or_else(|| panic!("{file}: head_measurement.record must be a path"));
        let report = read_json(rel);
        let bodies = report["bodies"]
            .as_object()
            .unwrap_or_else(|| panic!("{rel} carries no `bodies` object"));

        // The report must cover every fixture THAT EXISTED when it was taken:
        // the whole revalidated set, plus every HEAD_MEASURED stem that names
        // THIS record (its own cohort). It cannot cover a chain that landed
        // after it — that chain's own record covers it, under this same gate.
        // What the rule still forbids is the degenerate case: a report covering
        // only the new body would be one file compared against itself.
        for (other, other_file) in EVIDENCE {
            let later_cohort = HEAD_MEASURED.contains(other)
                && evidence(other_file)["head_measurement"]["record"].as_str() != Some(rel);
            if later_cohort {
                continue;
            }
            assert!(
                bodies.contains_key(*other),
                "{rel} does not cover `{other}`. A freshness report must re-derive every \
                 fixture that existed when it was taken; only a chain whose own \
                 `head_measurement.record` names a different report is exempt, and `{other}` \
                 does not."
            );
        }

        let row = &bodies[*stem];
        assert_eq!(
            row["verdict"].as_str(),
            Some("IDENTICAL"),
            "{rel}: `{stem}` must be IDENTICAL against the live dump, not merely NUMBERING-ONLY \
             — its fixture was cut from that dump, so anything else means the fixture was edited"
        );
        assert_eq!(
            row["classes"].as_array().map(Vec::is_empty),
            Some(true),
            "{rel}: `{stem}`'s drift-class list must be EMPTY for the same reason"
        );
        assert_eq!(
            row["at_head"]["lineage"].as_str(),
            ev["lineage"].as_str(),
            "{file}: the fixture's lineage and the live dump's disagree. A digest names WHICH \
             artifact a theorem is about, so two answers is worse than a stale one."
        );
        assert_eq!(
            hm["at_head_lineage"].as_str(),
            ev["lineage"].as_str(),
            "{file}: head_measurement.at_head_lineage must restate the fixture's own lineage"
        );
        assert_eq!(
            ev["reproduction"]["coverage_json_byte_identical_across_all_three"].as_bool(),
            Some(true),
            "{file}: a head measurement must be REPRODUCED — three clean non-incremental builds \
             with a byte-identical coverage.json — or `lineage` is one observation, not a \
             measurement, and there is no later record to catch that"
        );
    }
}
