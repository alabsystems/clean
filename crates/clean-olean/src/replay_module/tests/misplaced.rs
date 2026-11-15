// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean olean replay` on hole B1 (`docs/DECISIONS.md` R113): a declaration
//! placed where `lean` never reads it. `ReplayMisplacedServer` keeps
//! `SO`/`SO.mk`/`SO.rec` in its `.olean.server` alone, and
//! `ReplayMisplacedServerPlain` keeps `SOP`… in a non-module artifact's
//! companion; both use a theorem in the part `lean` reads. Pinned `leanchecker`
//! refuses each (`unknown constant 'SO'` / `'SOP'`). The loader refuses the
//! whole artifact (`ImportError::MisplacedDeclaration`), so the replay reports
//! it as a load error naming the misplaced family. `ReplayHonestServerParts`
//! (every part holds `SH`) is admitted in full.

use super::*;

#[test]
fn test_replay_module_refuses_a_misplaced_declaration_by_name() {
    for (module, needle) in [
        ("ReplayMisplacedServer", "SO"),
        ("ReplayMisplacedServerPlain", "SOP"),
        ("ReplayMisplacedOlean", "SX"),
    ] {
        let record = replay(module, ReplayMode::ImportsTrusted);
        assert!(!record.ok, "{module}: must be refused: {record:?}");
        let error = record.load_error.as_deref().unwrap_or_else(|| {
            panic!("{module}: a misplaced declaration is a load refusal: {record:?}")
        });
        assert!(
            error.contains("does not") && error.contains("consumer that is not a `module` reads"),
            "{module}: {error}"
        );
        assert!(
            error.contains(needle),
            "{module}: must name `{needle}`: {error}"
        );
    }
}

#[test]
fn test_replay_module_admits_the_honest_server_parts_control() {
    let record = replay("ReplayHonestServerParts", ReplayMode::ImportsTrusted);
    assert!(
        record.ok && record.load_error.is_none() && record.refusals.is_empty(),
        "the honest control must be admitted in full: {record:?}"
    );
    assert!(record.admitted >= 1, "{record:?}");
}

/// Review findings P1-P3 through `clean olean replay`: parts that disagree on a value or an
/// import list, and a misplaced family in a dependency, are a load refusal naming what the rule
/// refuses; the honest dependency pair is admitted in full.
#[test]
fn test_replay_module_refuses_parts_that_disagree_and_misplaced_dependencies() {
    for (module, needle) in [
        ("ReplayPartsValDis", "state `pv_X` differently"),
        ("ReplayPartsValDepUser", "state `pd_X` differently"),
        ("ReplayPartsImpT", "state its imports differently"),
        ("ReplayMisplacedDepUser", "declares `MD`"),
    ] {
        let record = replay(module, ReplayMode::ImportsTrusted);
        assert!(!record.ok, "{module}: must be refused: {record:?}");
        let error = record
            .load_error
            .as_deref()
            .unwrap_or_else(|| panic!("{module}: a load refusal: {record:?}"));
        assert!(
            error.contains(needle),
            "{module}: must name `{needle}`: {error}"
        );
    }
    let record = replay("ReplayHonestDepUser", ReplayMode::ImportsTrusted);
    assert!(
        record.ok && record.load_error.is_none() && record.refusals.is_empty(),
        "{record:?}"
    );
    assert_eq!(record.admitted, 1, "{record:?}");
}
