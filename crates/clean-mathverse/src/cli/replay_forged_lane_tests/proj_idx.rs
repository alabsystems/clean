// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A projection index Lean's kernel refuses (`ReplayForgedProjIdx`:
//! `forged_proj_idx : Nat := .proj Prod (2^64) (1, 1)`) through the mathverse
//! re-check lanes (decision R147, leanprover/lean4#14632's `to_proj_idx`).
//!
//! Pinned `leanchecker` refuses it: rc 1, `(kernel) invalid projection`, and
//! `--fresh` the same. Measured 2026-10-20 with the release binary of
//! 33ce84e20: `per-constant-verify` returned `kernel_verified=1`, and every
//! `stamp-verified` mode stamped `forged_proj_idx`. Those lanes read the
//! `.olean` through the two-phase decoder, which kept the heap index's low
//! limb and checked `.proj Prod 0 (1, 1)` instead. `clean olean replay`,
//! which reads through the direct decoder, refused it at load.

use super::*;

const MODULE: &str = "ReplayForgedProjIdx";
const FORGED: &str = "forged_proj_idx";

fn try_per_constant(module: &str) -> Result<PerConstantResult, String> {
    let dir = fixtures();
    per_constant_verify(
        &dir.join(format!("{module}.olean")),
        &dir,
        &[],
        DEFAULT_HEARTBEAT_LIMIT,
        None,
        FingerprintMode::Metadata,
        false,
        false,
        true,
        ProofValueElision::None,
        64,
        None,
    )
    .map_err(|e| e.to_string())
}

/// A lane that refuses the whole module names the index: the decoder's
/// refusal of the heap Nat 2^64, whose two-limb MPZ object is not the
/// single-limb shape a kernel index may take (measured 2026-10-21: `clean olean
/// replay --fresh` refuses it with this message).
const INDEX_REFUSAL: &str = "invalid compacted Nat MPZ header";

/// `per-constant-verify` verifies nothing out of the module: either the run
/// is refused or the declaration is. The control is `ReplayHonestInd`, whose
/// projection functions carry small indices and verify in full.
#[test]
fn test_per_constant_verify_refuses_a_heap_projection_index() {
    match try_per_constant(MODULE) {
        Ok(r) => {
            assert_eq!(r.kernel_verified, 0, "{:?}", r.errors);
            assert!(
                r.errors.contains_key(FORGED),
                "`{FORGED}` must be refused: targets {:?}, errors {:?}",
                r.targets,
                r.errors
            );
        }
        Err(message) => assert!(
            message.contains(INDEX_REFUSAL),
            "per-constant-verify: the refusal must be the projection index's Nat: {message}"
        ),
    }
    let r = per_constant("ReplayHonestInd", &[]);
    assert_eq!(r.failed, 0, "{:?}", r.errors);
    assert_eq!(r.kernel_verified, value_bearing("ReplayHonestInd").len());
}

/// `--parallel`'s eager base since R142 (`docs/DECISIONS.md`; the loader's
/// resident-value invariant, `clean_olean::import::authoritative_values`): the
/// decoder refuses the heap index, so the value `ReplayForgedProjIdx` states
/// for `forged_proj_idx` never becomes resident, and the import is refused
/// naming that declaration before the index's own message reaches the run
/// (measured 2026-10-27 on the merge of origin/main 1cd64b4c9 into round 5).
/// The wording is `values.rs`'s needle for R142, with this module's reason.
fn not_resident_refusal() -> String {
    format!(
        "`{MODULE}` states `{FORGED}` with a value the environment does not hold \
         (it is not resident)"
    )
}

/// No `stamp-verified` mode stamps the forgery. A mode that refuses the run
/// names the index, except `--parallel`, whose base refuses the same forgery
/// one step earlier through R142 ([`not_resident_refusal`]).
#[test]
fn test_stamp_verified_all_modes_refuse_a_heap_projection_index() {
    for mode in STAMP_MODES {
        match try_stamp(&[MODULE], mode) {
            Ok(stamped) => assert!(
                !stamped.contains(FORGED),
                "stamp-verified {mode:?} stamped `{FORGED}`: {stamped:?}"
            ),
            Err(e) => {
                let e = e.to_string();
                let r142 = mode == Some("--parallel") && e.contains(&not_resident_refusal());
                assert!(
                    e.contains(INDEX_REFUSAL) || r142,
                    "stamp-verified {mode:?}: the refusal must be the projection index's Nat \
                     (or, under --parallel, R142's refusal of `{FORGED}`): {e}"
                );
            }
        }
    }
}

/// The sharded worker, which reads the module through the same two-phase
/// decoder, verifies nothing out of it either.
#[test]
fn test_sharded_verify_module_refuses_a_heap_projection_index() {
    let mut search = vec![fixtures()];
    search.extend(clean_olean::default_search_paths());
    match crate::verify::sharded::verify_module(MODULE, &search, 16) {
        Ok(r) => {
            assert!(
                !r.kernel_verified_names.iter().any(|n| n == FORGED),
                "the sharded worker verified `{FORGED}`: {:?}",
                r.kernel_verified_names
            );
            assert_eq!(r.counts.kernel_verified, 0, "{:?}", r.failures);
        }
        Err(e) => assert!(
            e.to_string().contains(INDEX_REFUSAL),
            "sharded: the refusal must be the projection index's Nat: {e}"
        ),
    }
}
