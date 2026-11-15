// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean olean replay` on universe-level equalities, against the
//! `replay_forged` fixtures pinned Lean minted (`forgedLevelSubsumption`,
//! `honestLevelEquiv`, `levelSharing`, `ReplayHonestWfLevels`,
//! `forgedLevelReach`, `honestLevelReach`, `ReplayHonestLevelProj`;
//! per-constant verdicts in the family README, DECISIONS R150).

use super::*;

/// The seven level equalities pinned Lean's kernel refuses, each true at every
/// assignment of its parameters.
const FORGED_LEVEL_EQUALITIES: [&str; 7] = [
    "fls_join",
    "fls_join_wf",
    "fls_imax_reflatten",
    "fls_decode_max",
    "fls_decode_imax",
    "fls_subst",
    "fls_infer_pi",
];

/// Every forged equality is refused as a declaration type mismatch, as
/// `leanchecker` refuses it; the honest axioms they use are admitted.
#[test]
fn test_replay_module_refuses_forged_level_equalities_as_lean_does() {
    let r = replay("ReplayForgedLevelSubsumption", ReplayMode::ImportsTrusted);
    for name in FORGED_LEVEL_EQUALITIES {
        assert_refused(&r, name, "TypeMismatch");
    }
    for axiom in ["fls_K", "fls_A", "fls_B"] {
        assert!(
            r.refusals.iter().all(|refusal| refusal.constant != axiom),
            "the honest axiom `{axiom}` must be admitted: {:?}",
            r.refusals
        );
    }
    assert_eq!(
        r.refusals.len(),
        FORGED_LEVEL_EQUALITIES.len(),
        "exactly the seven equalities are refused: {:?}",
        r.refusals
    );
}

/// The twins pinned Lean admits, `hle_subst` and `hle_infer_pi` among them,
/// which only Lean's construction (substitution, Π sort) admits.
#[test]
fn test_replay_module_admits_honest_level_equalities() {
    for mode in [ReplayMode::ImportsTrusted, ReplayMode::Fresh] {
        let r = replay("ReplayHonestLevelEquiv", mode);
        assert!(r.ok, "{mode:?}: {:?}", r.refusals);
        assert_eq!(r.admitted, r.constants_checked, "{mode:?}: {r:?}");
        if mode == ReplayMode::ImportsTrusted {
            // `Fresh` replays the whole `Init.Prelude` closure too.
            assert_eq!(r.constants_checked, 9, "{mode:?}: {r:?}");
        }
    }
}

/// A WF definition whose `._unary` universe packs an `imax` tower, compiled by
/// pinned Lean: admitted, because the stored level is read verbatim. Release
/// only: the module imports all of `Init`, whose closure a debug build does
/// not load in a test's time (the `is_prop_sort` note).
#[cfg(not(debug_assertions))]
#[test]
fn test_replay_module_admits_honest_wf_universe_levels() {
    let r = replay("ReplayHonestWfLevels", ReplayMode::ImportsTrusted);
    assert!(r.ok, "{:?}", r.refusals);
    assert_eq!(r.admitted, r.constants_checked, "{r:?}");
    assert!(r.constants_checked > 0, "{r:?}");
}

/// `ls_cS.{u,v} : Sort (imax v (u+1))` instantiated by the identity: pinned
/// Lean admits `ls_same` and refuses `ls_sorted`, a verdict that depends on
/// the `.olean`'s object sharing. Clean refuses both by name (fail-closed:
/// `ls_same` is a recorded Clean-refuses-Lean-admits row), and nothing else:
/// `--fresh` replays the `Init.Prelude` closure through the same lane, where
/// a checker that kept refusing after the first sharing refusal refused the
/// Init constants checked after it (measured 2026-10-20 on the `Eqp` probes).
#[test]
fn test_replay_module_refuses_sharing_dependent_instantiation_by_name() {
    for mode in [ReplayMode::ImportsTrusted, ReplayMode::Fresh] {
        let r = replay("ReplayLevelSharing", mode);
        for name in ["ls_same", "ls_sorted"] {
            assert_refused(&r, name, "LevelSharingDependent");
        }
        assert_eq!(
            r.refusals.len(),
            2,
            "{mode:?}: only the two uses are refused, the axiom and every Init \
             constant admitted: {:?}",
            r.refusals
        );
        assert_eq!(r.admitted + 2, r.constants_checked, "{mode:?}: {r:?}");
    }
}

/// t4 and t9 across a module boundary: the users see `hli_t4`/`hli_t9` only
/// through the import's decode. Pinned Lean refuses `fli_t4`/`fli_t9` and
/// admits `hliu_t4`/`hliu_t9`; a collapsing decoder admits the first pair and
/// refuses the second.
#[test]
fn test_replay_module_imported_levels_are_read_as_stored() {
    for mode in [ReplayMode::ImportsTrusted, ReplayMode::Fresh] {
        let forged = replay("ReplayForgedLevelImport", mode);
        for name in ["fli_t4", "fli_t9"] {
            assert_refused(&forged, name, "TypeMismatch");
        }
        let honest = replay("ReplayHonestLevelImportUse", mode);
        assert!(honest.ok, "{mode:?}: {:?}", honest.refusals);
        assert_eq!(
            honest.admitted, honest.constants_checked,
            "{mode:?}: {honest:?}"
        );
    }
}

/// `fls_proj` and `fls_delta`: a projection and a δ-unfolding at
/// `w := imax u v`, declared at the level a collapsing substitution builds.
/// Pinned Lean instantiates both with `instantiate_lparams` and refuses each
/// as a declaration type mismatch. And three inductive blocks pinned Lean's
/// `inductive.cpp` refuses: `flr_MA`/`flr_MB` (mutual levels not
/// `is_equivalent`), `flr_Fb` (a field bound `is_geq` does not prove) and
/// `flr_Z` (`Sort (max 0 0)`, not structurally `0`). The structure, the
/// definition and the axiom they use are admitted.
#[test]
fn test_replay_module_reach_levels_follow_pinned_lean() {
    let r = replay("ReplayForgedLevelReach", ReplayMode::ImportsTrusted);
    for name in ["fls_proj", "fls_delta"] {
        assert_refused(&r, name, "TypeMismatch");
    }
    for block in ["flr_MA", "flr_Fb", "flr_Z"] {
        assert!(
            r.refusals
                .iter()
                .any(|x| x.constant == block || x.constant.starts_with(&format!("{block}."))),
            "block `{block}` must be refused: {:?}",
            r.refusals
        );
    }
    let honest: Vec<&str> = r
        .refusals
        .iter()
        .map(|x| x.constant.as_str())
        .filter(|c| {
            ["flr_S", "flr_D", "flr_Av"]
                .iter()
                .any(|h| c == h || c.starts_with(&format!("{h}.")))
        })
        .collect();
    assert!(
        honest.is_empty(),
        "refused honest {honest:?}: {:?}",
        r.refusals
    );
}

/// The twins at Lean's spelling, the ι-reduct `hle_iota`, and the two
/// recursors pinned Lean builds from a STRUCTURAL `is_zero`: `hlr_P0.rec`
/// with no universe parameter (its field's sort is `max 0 0`) and
/// `hlr_Q0.rec` with `k = false` (`Sort (max 0 0)`). The replay regenerates
/// each recursor and compares it with the stored one, so a semantic `is_zero`
/// refuses both families. And the elaborated `rhp_c5`, whose proof keeps a raw
/// projection.
#[test]
fn test_replay_module_admits_honest_level_reach() {
    for mode in [ReplayMode::ImportsTrusted, ReplayMode::Fresh] {
        let r = replay("ReplayHonestLevelReach", mode);
        assert!(r.ok, "{mode:?}: {:?}", r.refusals);
        assert_eq!(r.admitted, r.constants_checked, "{mode:?}: {r:?}");
    }
    let r = replay("ReplayHonestLevelProj", ReplayMode::ImportsTrusted);
    assert!(r.ok, "{:?}", r.refusals);
    assert_eq!(r.admitted, r.constants_checked, "{r:?}");
}
