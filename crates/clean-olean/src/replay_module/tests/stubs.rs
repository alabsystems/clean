// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean olean replay` on R131 (`docs/DECISIONS.md`): value-free stubs that a
//! later part completes, against pinned `leanchecker` (family README).
//!
//! `ReplayStubRefused` is `writeModule`'s public-theorem layout over a value the
//! kernel refuses (`sr_t`): rc 1 in both modes. `ReplayStubRefusedDepUser`'s
//! dependency carries the same (`srd_t`): the default mode trusts the import
//! (rc 0), `--fresh` replays it (rc 1). A non-module artifact whose companion
//! completes its `.olean`'s stub (`ReplayStubPlainDep`, under the user
//! `ReplayStubPlainDepUser`, rc 1) or is the module checked
//! (`ReplayStubPlainTgt`, default rc 1) is refused at load since R131. The
//! controls are admitted in full.

use super::*;

#[test]
fn test_replay_module_refuses_a_stub_completion_the_kernel_refuses() {
    for mode in [ReplayMode::ImportsTrusted, ReplayMode::Fresh] {
        let record = replay("ReplayStubRefused", mode);
        assert_refused(&record, "sr_t", "Type check error in declaration sr_t");
        assert!(
            record.refusals.iter().any(|r| r.constant == "sr_u"),
            "{mode:?}: `sr_u` uses the refused `sr_t`: {:?}",
            record.refusals
        );
        if mode == ReplayMode::ImportsTrusted {
            assert_eq!(record.admitted, 0, "{record:?}");
        }
    }
    // The dependency form: trusted by the default mode, as `leanchecker`'s
    // default mode trusts it (rc 0); replayed and refused under `--fresh`.
    let record = replay("ReplayStubRefusedDepUser", ReplayMode::ImportsTrusted);
    assert_admitted(&record, 1);
    let record = replay("ReplayStubRefusedDepUser", ReplayMode::Fresh);
    assert_refused(&record, "srd_t", "Type check error in declaration srd_t");
    assert_admitted(&replay("ReplayStubHonest", ReplayMode::ImportsTrusted), 2);
    let fresh = replay("ReplayStubHonest", ReplayMode::Fresh);
    assert!(fresh.ok, "{:?}", fresh.first_refusal);
    assert_eq!(fresh.admitted, fresh.constants_checked, "{fresh:?}");
}

#[test]
fn test_replay_module_refuses_a_non_module_companion_that_completes_a_stub() {
    for (module, needle) in [
        (
            "ReplayStubPlainDepUser",
            "the parts of `ReplayStubPlainDep` state `spd_X` differently",
        ),
        (
            "ReplayStubPlainPrivDepUser",
            "the parts of `ReplayStubPlainPrivDep` state `sppd_X` differently",
        ),
        (
            "ReplayStubPlainTgt",
            "the parts of `ReplayStubPlainTgt` state `spt_f` differently",
        ),
        (
            "ReplayMisplacedOleanOnlyDepUser",
            "`ReplayMisplacedOleanOnlyDep`'s `.olean` declares `MO`",
        ),
        (
            "ReplayMisplacedPrivPlainDepUser",
            "`ReplayMisplacedPrivPlainDep`'s `.olean.private` declares `MP`",
        ),
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
    assert_admitted(
        &replay("ReplayStubPlainHonestUser", ReplayMode::ImportsTrusted),
        1,
    );
}

/// R142: a declaration the authoritative part states with a value that the
/// load did not make resident — a private value Clean's converter cannot read
/// (`ReplayStubMv`, `ReplayStubFv`) or a stub whose name an import holds as an
/// axiom (`ReplayShadowStub`, and `ReplayShadowThm` without the module system).
/// Pinned `leanchecker` refuses each in both modes; the shadowed import's user
/// is trusted by the default mode (rc 0) and refused under `--fresh`.
#[test]
fn test_replay_module_refuses_a_value_the_load_did_not_make_resident() {
    for (module, name) in [
        ("ReplayStubMv", "smv_f"),
        ("ReplayStubFv", "sfv_f"),
        ("ReplayShadowStub", "sha_n"),
        ("ReplayShadowThm", "sha_n"),
    ] {
        for mode in [ReplayMode::ImportsTrusted, ReplayMode::Fresh] {
            let record = replay(module, mode);
            assert!(!record.ok, "{module} {mode:?}: must be refused: {record:?}");
            assert!(
                record.refusals.iter().any(|r| r.constant == name),
                "{module} {mode:?}: `{name}` must be refused: {:?}",
                record.refusals
            );
        }
    }
    assert_admitted(
        &replay("ReplayShadowStubUser", ReplayMode::ImportsTrusted),
        1,
    );
    let fresh = replay("ReplayShadowStubUser", ReplayMode::Fresh);
    assert!(
        !fresh.ok && fresh.refusals.iter().any(|r| r.constant == "sha_n"),
        "{fresh:?}"
    );
}
