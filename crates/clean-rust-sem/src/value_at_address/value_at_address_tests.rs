// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the M2 value-at-address small-step relation.
//!
//! Two legs of the ck2 §8 staging are exercised here (NOT the `clean_kernel`
//! mechanized proofs, which are milestone M2.4 / M3 and deferred):
//!
//! - **Differential harness** ([`run_step`] vs [`run_reference`]): a corpus of
//!   op sequences is run in lockstep through `step` and through a hand-rolled
//!   driver that calls the executable `Memory` / `StackedBorrows` operations
//!   directly. A divergence in observable result (value read / error-as-stuck)
//!   is a test failure (spec §3.3, M2.2).
//! - **Property tests** for the two metatheory lemmas establishable here as
//!   *executable properties*: (1) determinism of `step` on the non-opaque
//!   fragment, and (2) allocation freshness / disjointness. The `clean_kernel`
//!   mechanized versions are M2.4 / M3 (deferred).

use super::{step, stuck_from_borrow, Config, MemOp, Observation, StepOutcome, StuckReason};
use crate::memory::{Address, Memory};
use crate::ownership::Place;
use crate::stacked_borrows::{AccessKind, BorrowPermission, BorrowTag, StackedBorrows};

use std::collections::HashMap;

/// Comparable observable result of one op: a successful observation or a stuck
/// reason. Both the `step` runner and the reference runner produce this so the
/// differential comparison is exact.
type StepResult = Result<Observation, StuckReason>;

/// Run an op sequence through `step`, collecting the observable result of each
/// op. Stops after the first stuck op (a stuck configuration has no successor).
fn run_step(ops: &[MemOp]) -> Vec<StepResult> {
    let mut cfg = Config::new();
    let mut results = Vec::new();
    for op in ops {
        match step(cfg, op.clone()) {
            StepOutcome::Stepped {
                config,
                observation,
            } => {
                cfg = config;
                results.push(Ok(observation));
            }
            StepOutcome::Stuck(reason) => {
                results.push(Err(reason));
                break;
            }
        }
    }
    results
}

/// Reference state mirroring `Config`, driven directly through the executable
/// `Memory` / `StackedBorrows` operations (no `step`). This is the independent
/// side of the differential harness.
struct Reference {
    memory: Memory,
    borrows: StackedBorrows<Place>,
    place_to_alloc: HashMap<Place, crate::memory::AllocId>,
    current_tag: HashMap<Place, BorrowTag>,
}

impl Reference {
    fn new() -> Self {
        Self {
            memory: Memory::new(),
            borrows: StackedBorrows::new(),
            place_to_alloc: HashMap::new(),
            current_tag: HashMap::new(),
        }
    }

    fn apply(&mut self, op: &MemOp) -> StepResult {
        match op {
            MemOp::Alloc { place, size, align } => {
                if self.place_to_alloc.contains_key(place) {
                    return Err(StuckReason::PlaceAlreadyBound);
                }
                let addr = self
                    .memory
                    .allocate_aligned(*size, *align)
                    .map_err(StuckReason::from)?;
                let tag = self.borrows.ensure_base(place.clone());
                self.place_to_alloc.insert(place.clone(), addr.alloc_id);
                self.current_tag.insert(place.clone(), tag);
                Ok(Observation::Allocated(addr.alloc_id))
            }
            MemOp::Dealloc { place } => {
                let id = self
                    .place_to_alloc
                    .get(place)
                    .copied()
                    .ok_or(StuckReason::UnboundPlace)?;
                self.memory
                    .deallocate(Address::new(id, 0))
                    .map_err(StuckReason::from)?;
                Ok(Observation::Deallocated)
            }
            MemOp::Read {
                place,
                offset,
                size,
            } => {
                let id = self
                    .place_to_alloc
                    .get(place)
                    .copied()
                    .ok_or(StuckReason::UnboundPlace)?;
                let tag = self
                    .current_tag
                    .get(place)
                    .copied()
                    .ok_or(StuckReason::UnboundPlace)?;
                self.borrows
                    .access(place, tag, AccessKind::Read)
                    .map_err(stuck_from_borrow)?;
                let bytes = self
                    .memory
                    .read_bytes(Address::new(id, *offset), *size)
                    .map_err(StuckReason::from)?;
                Ok(Observation::Read(bytes.to_vec()))
            }
            MemOp::Write {
                place,
                offset,
                data,
            } => {
                let id = self
                    .place_to_alloc
                    .get(place)
                    .copied()
                    .ok_or(StuckReason::UnboundPlace)?;
                let tag = self
                    .current_tag
                    .get(place)
                    .copied()
                    .ok_or(StuckReason::UnboundPlace)?;
                self.borrows
                    .access(place, tag, AccessKind::Write)
                    .map_err(stuck_from_borrow)?;
                self.memory
                    .write_bytes(Address::new(id, *offset), data)
                    .map_err(StuckReason::from)?;
                Ok(Observation::Wrote)
            }
            MemOp::Retag {
                place,
                permission,
                protector,
            } => {
                if !self.place_to_alloc.contains_key(place) {
                    return Err(StuckReason::UnboundPlace);
                }
                let parent = self
                    .current_tag
                    .get(place)
                    .copied()
                    .ok_or(StuckReason::UnboundPlace)?;
                let tag = self
                    .borrows
                    .retag(place, parent, *permission, *protector)
                    .map_err(stuck_from_borrow)?;
                self.current_tag.insert(place.clone(), tag);
                Ok(Observation::Retagged(tag))
            }
        }
    }
}

/// Run an op sequence through the reference driver, collecting per-op results
/// and stopping at the first rejection (matching `run_step`).
fn run_reference(ops: &[MemOp]) -> Vec<StepResult> {
    let mut state = Reference::new();
    let mut results = Vec::new();
    for op in ops {
        let result = state.apply(op);
        let stop = result.is_err();
        results.push(result);
        if stop {
            break;
        }
    }
    results
}

/// Assert `step` and the reference driver agree on a sequence (differential).
fn assert_differential(ops: &[MemOp]) {
    let stepped = run_step(ops);
    let reference = run_reference(ops);
    assert_eq!(
        stepped, reference,
        "step diverged from the executable models on {ops:?}"
    );
}

fn local(n: u32) -> Place {
    Place::local(n)
}

// --------------------------------------------------------------------------
// Differential harness — explicit boundary corpus
// --------------------------------------------------------------------------

#[test]
fn test_diff_alloc_write_read_roundtrip() {
    let p = local(0);
    assert_differential(&[
        MemOp::Alloc {
            place: p.clone(),
            size: 4,
            align: 1,
        },
        MemOp::Write {
            place: p.clone(),
            offset: 0,
            data: vec![1, 2, 3, 4],
        },
        MemOp::Read {
            place: p,
            offset: 0,
            size: 4,
        },
    ]);
}

#[test]
fn test_diff_use_after_free_is_stuck() {
    let p = local(0);
    let ops = [
        MemOp::Alloc {
            place: p.clone(),
            size: 2,
            align: 1,
        },
        MemOp::Dealloc { place: p.clone() },
        MemOp::Read {
            place: p,
            offset: 0,
            size: 1,
        },
    ];
    assert_differential(&ops);
    let results = run_step(&ops);
    assert!(matches!(
        results.last(),
        Some(Err(StuckReason::UseAfterFree(_)))
    ));
}

#[test]
fn test_diff_double_free_is_stuck() {
    let p = local(0);
    let ops = [
        MemOp::Alloc {
            place: p.clone(),
            size: 2,
            align: 1,
        },
        MemOp::Dealloc { place: p.clone() },
        MemOp::Dealloc { place: p },
    ];
    assert_differential(&ops);
    assert!(matches!(
        run_step(&ops).last(),
        Some(Err(StuckReason::DoubleFree(_)))
    ));
}

#[test]
fn test_diff_out_of_bounds_write_is_stuck() {
    let p = local(0);
    let ops = [
        MemOp::Alloc {
            place: p.clone(),
            size: 2,
            align: 1,
        },
        MemOp::Write {
            place: p,
            offset: 0,
            data: vec![1, 2, 3, 4],
        },
    ];
    assert_differential(&ops);
    assert!(matches!(
        run_step(&ops).last(),
        Some(Err(StuckReason::OutOfBounds { .. }))
    ));
}

#[test]
fn test_diff_zero_align_alloc_is_stuck() {
    let p = local(0);
    let ops = [MemOp::Alloc {
        place: p,
        size: 4,
        align: 0,
    }];
    assert_differential(&ops);
    assert!(matches!(
        run_step(&ops).last(),
        Some(Err(StuckReason::AllocationFailed { .. }))
    ));
}

#[test]
fn test_diff_non_power_of_two_align_is_stuck() {
    let p = local(0);
    assert_differential(&[MemOp::Alloc {
        place: p,
        size: 4,
        align: 3,
    }]);
}

#[test]
fn test_diff_read_unbound_place_is_stuck() {
    let ops = [MemOp::Read {
        place: local(7),
        offset: 0,
        size: 1,
    }];
    assert_differential(&ops);
    assert!(matches!(
        run_step(&ops).last(),
        Some(Err(StuckReason::UnboundPlace))
    ));
}

#[test]
fn test_diff_retag_then_access() {
    let p = local(0);
    assert_differential(&[
        MemOp::Alloc {
            place: p.clone(),
            size: 4,
            align: 1,
        },
        MemOp::Retag {
            place: p.clone(),
            permission: BorrowPermission::Unique,
            protector: None,
        },
        MemOp::Write {
            place: p.clone(),
            offset: 0,
            data: vec![9, 9, 9, 9],
        },
        MemOp::Read {
            place: p,
            offset: 0,
            size: 4,
        },
    ]);
}

#[test]
fn test_diff_alloc_same_place_twice_is_stuck() {
    let p = local(0);
    let ops = [
        MemOp::Alloc {
            place: p.clone(),
            size: 1,
            align: 1,
        },
        MemOp::Alloc {
            place: p,
            size: 1,
            align: 1,
        },
    ];
    assert_differential(&ops);
    assert!(matches!(
        run_step(&ops).last(),
        Some(Err(StuckReason::PlaceAlreadyBound))
    ));
}

#[test]
fn test_full_write_clears_taint_then_read_succeeds() {
    // A havoc'd block is TaintedRead until a full-allocation write clears it.
    // We exercise the model directly (no Havoc op in the first batch) and then
    // confirm `step`'s read agrees once taint is cleared.
    let p = local(0);
    let mut cfg = Config::new();
    let StepOutcome::Stepped { config, .. } = step(
        cfg,
        MemOp::Alloc {
            place: p.clone(),
            size: 2,
            align: 1,
        },
    ) else {
        panic!("alloc should step");
    };
    cfg = config;
    // A full-allocation write returns Wrote and (per Memory) clears taint.
    let outcome = step(
        cfg,
        MemOp::Write {
            place: p.clone(),
            offset: 0,
            data: vec![7, 8],
        },
    );
    let StepOutcome::Stepped {
        config,
        observation,
    } = outcome
    else {
        panic!("full write should step");
    };
    assert_eq!(observation, Observation::Wrote);
    let read = step(
        config,
        MemOp::Read {
            place: p,
            offset: 0,
            size: 2,
        },
    );
    assert_eq!(read.observation(), Some(&Observation::Read(vec![7, 8])));
}

// --------------------------------------------------------------------------
// Property tests (executable; mechanized versions deferred to M2.4 / M3)
// --------------------------------------------------------------------------

use proptest::prelude::*;

fn arb_place() -> impl Strategy<Value = Place> {
    (0u32..4).prop_map(Place::local)
}

fn arb_permission() -> impl Strategy<Value = BorrowPermission> {
    prop_oneof![
        Just(BorrowPermission::Unique),
        Just(BorrowPermission::SharedReadWrite),
        Just(BorrowPermission::SharedReadOnly),
        Just(BorrowPermission::Disabled),
    ]
}

fn arb_op() -> impl Strategy<Value = MemOp> {
    prop_oneof![
        (
            arb_place(),
            0usize..6,
            prop_oneof![Just(1usize), Just(2), Just(4)]
        )
            .prop_map(|(place, size, align)| MemOp::Alloc { place, size, align }),
        arb_place().prop_map(|place| MemOp::Dealloc { place }),
        (arb_place(), 0u64..6, 0usize..6).prop_map(|(place, offset, size)| MemOp::Read {
            place,
            offset,
            size
        }),
        (
            arb_place(),
            0u64..6,
            prop::collection::vec(any::<u8>(), 0..6)
        )
            .prop_map(|(place, offset, data)| MemOp::Write {
                place,
                offset,
                data
            }),
        // protector is always None: no protect op exists in the first batch, so
        // no protector tokens are ever live to reference.
        (arb_place(), arb_permission()).prop_map(|(place, permission)| MemOp::Retag {
            place,
            permission,
            protector: None
        }),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Lemma (1), executable form: `step` is deterministic on the non-opaque
    /// fragment (every op in the first batch is non-opaque). Two independent
    /// runs of the same op sequence produce identical observable traces.
    /// The `clean_kernel` mechanized determinism lemma is M2.4 (deferred).
    #[test]
    fn prop_step_determinism_non_opaque(ops in prop::collection::vec(arb_op(), 0..12)) {
        let first = run_step(&ops);
        let second = run_step(&ops);
        prop_assert_eq!(first, second);
    }

    /// The differential property over random sequences: `step` and the
    /// executable models never diverge (spec §3.3 lockstep pin).
    #[test]
    fn prop_step_matches_executable_models(ops in prop::collection::vec(arb_op(), 0..12)) {
        let stepped = run_step(&ops);
        let reference = run_reference(&ops);
        prop_assert_eq!(stepped, reference);
    }

    /// Lemma (2), executable form: allocation freshness / disjointness. Allocs
    /// over distinct non-conflicting places yield distinct, non-null
    /// (`AllocId != 0`) live blocks, and the null block is never live. The
    /// `clean_kernel` mechanized freshness lemma is M2.4 (deferred).
    #[test]
    fn prop_alloc_freshness_disjointness(n in 0usize..4) {
        let mut cfg = Config::new();
        let mut seen = Vec::new();
        for i in 0..n {
            let place = Place::local(i as u32);
            let outcome = step(
                cfg,
                MemOp::Alloc { place: place.clone(), size: 1, align: 1 },
            );
            let StepOutcome::Stepped { config, observation } = outcome else {
                prop_assert!(false, "alloc of a fresh place must step");
                unreachable!();
            };
            cfg = config;
            let Observation::Allocated(id) = observation else {
                prop_assert!(false, "alloc must observe Allocated");
                unreachable!();
            };
            // Freshness: a fresh AllocId never aliases a live block.
            prop_assert!(!seen.contains(&id), "fresh AllocId aliased a live block");
            // The null block AllocId(0) is never handed out.
            prop_assert_ne!(id.0, 0);
            prop_assert!(cfg.is_live(&place));
            seen.push(id);
        }
        // The reserved null block is never live (spec §3.5(2)).
        prop_assert!(!cfg.null_is_live());
    }
}

#[test]
fn test_distinct_places_map_to_distinct_allocations() {
    // Disjointness backbone of the §3.5(4) frame lemma: non-conflicting places
    // (`conflicts_with == false`) map to distinct AllocIds.
    let p0 = local(0);
    let p1 = local(1);
    assert!(!p0.conflicts_with(&p1));
    let mut cfg = Config::new();
    for p in [&p0, &p1] {
        let StepOutcome::Stepped { config, .. } = step(
            cfg,
            MemOp::Alloc {
                place: p.clone(),
                size: 1,
                align: 1,
            },
        ) else {
            panic!("alloc should step");
        };
        cfg = config;
    }
    assert_ne!(cfg.alloc_id(&p0), cfg.alloc_id(&p1));
}

#[test]
fn test_null_block_never_live() {
    let cfg = Config::new();
    assert!(!cfg.null_is_live());
}
