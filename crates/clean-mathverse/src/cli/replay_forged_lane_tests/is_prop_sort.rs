// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The kernel's `is_prop`-requires-a-sort rule (leanprover/lean4#14807,
//! shipped in v4.33.1) through the mathverse re-check lanes; split from the
//! parent module to keep it under the size ratchet.
//!
//! `ReplayIsPropStuck` projects a data field (`IPK.observe`) out of a value
//! whose type's type does not reduce to a sort, and proves `False` with it
//! (`isprop_stuck_false`, a live Clean hole for leanprover/lean4#14807 before the fix).
//! Lean's fixed kernel refuses the projection at `ensure_sort`; the fix is
//! Clean's `is_prop` erroring there instead of answering `Ok(false)`.
//!
//! `stamp-verified` (every mode), the sharded worker and `per-constant-verify`
//! admit the `False` before the fix and refuse the projection after it: the
//! guard's RED→GREEN witnesses. `per-constant-verify` became one with decision
//! R147, which removed two over-refusals of honest content that stopped it
//! short of the guard. Its demand walk registered the `IPK.Owner` family
//! before `IPK.gate`, the definition `Owner`'s type former reduces through,
//! was resident, so the stored `IPK.Owner.rec` was refused ("Invalid
//! recursor"; fixed in `per_constant_family_deps.rs`, honest control
//! `ReplayHonestSortDef`). And it loaded an import's theorems without their
//! values, so `IPK.proposition`, whose check reduces `Acc.rec` on imported
//! `Acc` proofs, was refused (fixed in `per_constant_wf_proofs.rs`).
//!
//! Release-only: the fixture imports `Init.WF`, whose closure a debug build did
//! not finish loading in 17 min (release: ~24 s), so a debug build compiles
//! nothing here rather than passing it.

use super::*;

/// The two declarations the sort requirement refuses: the data-field
/// projection out of the stuck carrier, and the `False` built on it.
const REFUSED: [&str; 2] = ["IPK.observe", "isprop_stuck_false"];

/// The forged module's value-bearing declarations the sort requirement does
/// not touch (no projection out of a stuck carrier).
fn untouched() -> BTreeSet<String> {
    let mut names = value_bearing("ReplayIsPropStuck");
    for name in REFUSED {
        assert!(names.remove(name), "the fixture must declare `{name}`");
    }
    names
}

/// `stamp-verified`, every mode: the guard's RED→GREEN witness. Before the fix
/// every mode stamped `IPK.observe` and `isprop_stuck_false` (measured
/// 2026-10-18, base release binary); after it, neither is stamped, while the
/// declarations the guard does not touch, and the honest base, stay stamped.
#[test]
fn test_stamp_verified_all_modes_projection_needs_a_sort_typed_type() {
    let untouched = untouched();
    let honest = value_bearing("ReplayIsPropStuckBase");
    for mode in STAMP_MODES {
        let stamped = stamp(&["ReplayIsPropStuck"], mode);
        for forged in REFUSED {
            assert!(
                !stamped.contains(forged),
                "stamp-verified {mode:?} stamped `{forged}`: {stamped:?}"
            );
        }
        let missing: Vec<&String> = untouched.difference(&stamped).collect();
        assert!(
            missing.is_empty(),
            "stamp-verified {mode:?}: the refusal reached past the projection; not stamped {missing:?}"
        );
        let stamped = stamp(&["ReplayIsPropStuckBase"], mode);
        let missing: Vec<&String> = honest.difference(&stamped).collect();
        assert!(
            missing.is_empty(),
            "stamp-verified {mode:?}: not stamped {missing:?}"
        );
    }
}

/// The sharded worker: the guard's RED→GREEN witness. Its module loads with the
/// loader's module-trust rules left to its replay
/// (`load_module_with_deps_replaying_module`), which admits the forged family,
/// so before the fix it admitted the `False` too; after it, the projection and
/// the `False` are refused at the sort requirement, and the honest base
/// verifies in full.
#[test]
fn test_sharded_verify_module_projection_needs_a_sort_typed_type() {
    let r = sharded("ReplayIsPropStuck", 16);
    let reason = |n: &str| {
        r.failures
            .iter()
            .find(|(name, _)| name == n)
            .map(|(_, why)| why.clone())
            .unwrap_or_else(|| panic!("sharded: `{n}` must be refused: {:?}", r.failures))
    };
    assert!(
        reason("IPK.observe").contains("ExpectedSort"),
        "{:?}",
        r.failures
    );
    assert!(
        reason("isprop_stuck_false").contains("IPK.observe"),
        "{:?}",
        r.failures
    );
    let r = sharded("ReplayIsPropStuckBase", 16);
    assert_eq!(r.counts.failed, 0, "{:?}", r.failures);
}

/// `per-constant-verify`: the guard's RED→GREEN witness since decision R147.
/// `IPK.proposition := asProp witness` needs `Q` (`witness`'s type) to be `P`
/// (`asProp`'s domain), and `P ≡ Q` reduces `run` through `Acc.rec` on the
/// IMPORTED theorems `IPK.b._proof_1` and `IPK.c._proof_1`, which Lean's kernel
/// δ-unfolds to fire the iota rule. Until R147 the demand walk loaded every
/// imported theorem without its value, so that check was stuck and the lane
/// refused `IPK.proposition` (`TypeMismatch`, `P` against `Q`) and the four
/// declarations built on it, one declaration before the guard (measured 2026-10-19 with
/// `CLEAN_DUMP_CONSTS`: both proofs resident value-less). The walk now loads
/// the value of an imported theorem that concludes in `Acc` or `WellFounded`
/// (`per_constant_wf_proofs.rs`), so `IPK.proposition` verifies, as it does in
/// pinned Lean, `clean olean replay` and every `stamp-verified` mode, and the
/// refusal is the guard's: `IPK.observe` at `ExpectedSort`, and the `False`
/// built on it. `IPK.falseProof` and `IPK.trueProof` do not use the projection
/// and verify, as in every `stamp-verified` mode.
#[test]
fn test_per_constant_verify_projection_needs_a_sort_typed_type() {
    let r = per_constant("ReplayIsPropStuck", &[]);
    let errs = |n: &str| r.errors.get(n).cloned();
    assert!(
        !r.errors.contains_key("IPK.proposition"),
        "pcv: `IPK.proposition` must verify (its check unfolds imported Acc proofs): {:?}",
        r.errors.get("IPK.proposition")
    );
    assert_refused("pcv", &errs, "IPK.observe", "ExpectedSort");
    assert_refused("pcv", &errs, "isprop_stuck_false", "IPK.observe");
    for (name, why) in &r.errors {
        assert!(
            !why.contains("Invalid recursor"),
            "pcv: `{name}` refused through the family's recursor: {why}"
        );
    }
    assert_eq!(
        (r.kernel_verified, r.failed),
        (untouched().len(), REFUSED.len()),
        "{:?}",
        r.errors
    );
    let r = per_constant("ReplayIsPropStuckBase", &[]);
    assert_eq!(r.failed, 0, "{:?}", r.errors);
    assert_eq!(
        r.kernel_verified,
        value_bearing("ReplayIsPropStuckBase").len()
    );
}
