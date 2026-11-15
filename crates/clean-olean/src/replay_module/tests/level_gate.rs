// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean olean replay` on the large-elimination gate's two level rules,
//! against the `replay_forged` fixtures pinned Lean minted with `addDeclCore`:
//! the result level is found up to whnf (`ReplayHonestDeltaProp` /
//! `ReplayForgedDeltaPropLargeElim`), and only a PROVABLY nonzero level skips
//! the restriction analysis (`ReplayHonestSortU` / `ReplayForgedSortULargeElim`).

use super::*;

/// A family that is a `Prop` only up to whnf (`kernel-result-sort-whnf-elim`,
/// P0, 2026-10-16): `def hdp_prop : Type := Prop; inductive HDP : hdp_prop |
/// t | f`, which Lean's kernel admits with a `Prop`-only `HDP.rec`. The honest
/// module is admitted in full; the forgery that stores a LARGE `FDP.rec` (the
/// recursor Clean generated while it read the syntactic head) is refused at
/// the recursor, its block with it, and the proof of `False` through it.
/// Before the fix the verdicts were reversed: the loader's regeneration was
/// large, so the honest `HDP.rec` was refused and the forged one admitted.
#[test]
fn test_replay_module_delta_prop_family_follows_leans_result_level() {
    let honest = replay("ReplayHonestDeltaProp", ReplayMode::ImportsTrusted);
    assert!(honest.ok, "{:?}", honest.refusals);
    assert_eq!(honest.admitted, honest.constants_checked, "{honest:?}");
    let forged = replay("ReplayForgedDeltaPropLargeElim", ReplayMode::ImportsTrusted);
    assert_refused(&forged, "FDP.rec", "imported family record FDP.rec refused");
    assert_refused(&forged, "FDP.rec", "elimination universe differs");
    for member in ["FDP", "FDP.t", "FDP.f"] {
        assert_refused(&forged, member, "Invalid recursor FDP.rec");
    }
    assert!(
        forged
            .refusals
            .iter()
            .any(|r| r.constant == "forged_dp_false"),
        "`forged_dp_false : False` must be refused: {:?}",
        forged.refusals
    );
}

/// The same gate's other half: `inductive HSU.{u} : Sort u | t | f` has a
/// result level that may be zero, so Lean's kernel gives `HSU.rec` no motive
/// universe (only a PROVABLY nonzero level is exempt). The honest module is
/// admitted in full; the forgery storing a LARGE `FSU.rec` (`[u_1, u]`) is
/// refused at the recursor, its block with it, and `forged_su_false : False`.
#[test]
fn test_replay_module_sort_u_family_follows_leans_nonzero_rule() {
    let honest = replay("ReplayHonestSortU", ReplayMode::ImportsTrusted);
    assert!(honest.ok, "{:?}", honest.refusals);
    assert_eq!(honest.admitted, honest.constants_checked, "{honest:?}");
    let forged = replay("ReplayForgedSortULargeElim", ReplayMode::ImportsTrusted);
    assert_refused(&forged, "FSU.rec", "imported family record FSU.rec refused");
    assert_refused(&forged, "FSU.rec", "elimination universe differs");
    for member in ["FSU", "FSU.t", "FSU.f"] {
        assert_refused(&forged, member, "Invalid recursor FSU.rec");
    }
    assert!(
        forged
            .refusals
            .iter()
            .any(|r| r.constant == "forged_su_false"),
        "`forged_su_false : False` must be refused: {:?}",
        forged.refusals
    );
}
