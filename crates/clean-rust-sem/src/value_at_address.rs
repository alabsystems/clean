// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! # Value-at-address operational semantics (M2, first increment)
//!
//! This module implements the **executable + differential legs** of milestone
//! M2 of the give-back plan (see `designs/2026-06-29-giveback-clean-refinement.md`,
//! §2–§3.5). It is *not* the `clean_kernel` mechanized metatheory — those proofs
//! are milestone **M2.4 / M3** and are deferred (see the property-test comments
//! and the deviations in the milestone register).
//!
//! ## What this delivers
//!
//! An **executable small-step relation** [`step`] over a [`Config`] that bundles
//! the two real, separately-keyed executable models of `clean-rust-sem`:
//!
//! - the byte/provenance block heap [`crate::memory::Memory`] (model (a) in the
//!   spec), keyed by [`crate::memory::Address`] / [`crate::memory::AllocId`];
//! - the active aliasing discipline [`crate::stacked_borrows::StackedBorrows`],
//!   keyed by [`crate::ownership::Place`];
//! - the load-bearing **`Place` ↔ `Address` keying bridge** (spec §3.1,
//!   R-CLEAN-2): a fixed correspondence so the borrow stack (indexed by `Place`)
//!   and the byte heap (indexed by `Address`) name the same cell. The bridge
//!   keeps the correspondence one-to-one per allocation, so distinct
//!   non-conflicting `Place`s (`Place::conflicts_with == false`) map to distinct
//!   live [`AllocId`]s — the structural fact the §3.5(4) frame lemma rests on.
//!
//! ## Soundness rule (spec §3.2)
//!
//! Every failing check — null, invalid-ptr, use-after-free, tainted-read,
//! out-of-bounds, misaligned, protected-conflict, unbound place — is a **stuck
//! configuration**: [`StepOutcome::Stuck`], the absence of a successor. A stuck
//! step *never* yields a fail-open value. The executable check order is mirrored
//! exactly from [`crate::memory::Memory`] and
//! [`crate::stacked_borrows::StackedBorrows`].

use std::collections::HashMap;

use crate::memory::{Address, AllocId, Memory, MemoryError};
use crate::ownership::Place;
use crate::stacked_borrows::{
    AccessKind, BorrowPermission, BorrowTag, ProtectorId, StackedBorrows, StackedBorrowsError,
};

/// A first-batch memory operation (spec §3.2: Alloc, Dealloc, Read, Write, Retag).
///
/// Each variant is the formal image of an existing executable method, named so
/// the pin to the executable model is mechanical. Opaque/havoc, two-phase and
/// closure retags are out of this first batch (see module docs / deviations).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum MemOp {
    /// Image of `Memory::allocate_aligned` + `StackedBorrows::ensure_base`:
    /// reserve a fresh block for `place` and establish its root borrow tag.
    Alloc {
        /// The place naming the new allocation.
        place: Place,
        /// Requested size in bytes.
        size: usize,
        /// Requested alignment (must be a non-zero power of two).
        align: usize,
    },
    /// Image of `Memory::deallocate`: mark `place`'s block dead.
    Dealloc {
        /// The place to free.
        place: Place,
    },
    /// Image of `Memory::read_bytes` gated by `StackedBorrows::access(Read)`.
    Read {
        /// The place to read through.
        place: Place,
        /// Byte offset within the allocation.
        offset: u64,
        /// Number of bytes to read.
        size: usize,
    },
    /// Image of `Memory::write_bytes` gated by `StackedBorrows::access(Write)`.
    Write {
        /// The place to write through.
        place: Place,
        /// Byte offset within the allocation.
        offset: u64,
        /// Bytes to store.
        data: Vec<u8>,
    },
    /// Image of `StackedBorrows::retag`: derive a fresh tag from `place`'s
    /// current tag with the given `permission` / optional `protector`.
    Retag {
        /// The place whose borrow stack is retagged.
        place: Place,
        /// Permission of the derived capability.
        permission: BorrowPermission,
        /// Optional protector token to attach.
        protector: Option<ProtectorId>,
    },
}

/// The observable result of a successful [`step`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Observation {
    /// An allocation was created at the given id.
    Allocated(AllocId),
    /// The block was deallocated.
    Deallocated,
    /// Bytes read from memory (the only value-carrying observation).
    Read(Vec<u8>),
    /// A write completed.
    Wrote,
    /// A retag produced the given fresh tag.
    Retagged(BorrowTag),
}

/// Why a configuration is **stuck** (no successor) — the rejection image of
/// every executable check failure (spec §3.2). Stuck is never a fail-open value.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum StuckReason {
    /// Null-block access (`MemoryError::NullPointer`).
    #[error("null pointer access")]
    NullPointer,
    /// Pointer into an unknown allocation (`MemoryError::InvalidPointer`).
    #[error("invalid pointer into {0:?}")]
    InvalidPointer(AllocId),
    /// Access to a freed block (`MemoryError::UseAfterFree`).
    #[error("use after free of {0:?}")]
    UseAfterFree(AllocId),
    /// Second free of an already-dead block (`MemoryError::DoubleFree`).
    #[error("double free of {0:?}")]
    DoubleFree(AllocId),
    /// Access outside the allocation (`MemoryError::OutOfBounds`).
    #[error("out-of-bounds access at offset {offset} size {size} (alloc size {alloc_size})")]
    OutOfBounds {
        /// Offset of the attempted access.
        offset: u64,
        /// Size of the attempted access.
        size: usize,
        /// Size of the allocation.
        alloc_size: usize,
    },
    /// Misaligned typed access (`MemoryError::Misaligned`).
    #[error("misaligned access at offset {offset} (align {align})")]
    Misaligned {
        /// Offset of the attempted access.
        offset: u64,
        /// Required alignment.
        align: usize,
    },
    /// Read of a tainted (havoc'd) block (`MemoryError::TaintedRead`).
    #[error("tainted read of {0:?}")]
    TaintedRead(AllocId),
    /// Pointer arithmetic overflow (`MemoryError::PointerOverflow`).
    #[error("pointer overflow")]
    PointerOverflow,
    /// Allocation request rejected (`MemoryError::AllocationFailed`).
    #[error("allocation of size {size} align {align} failed")]
    AllocationFailed {
        /// Requested size.
        size: usize,
        /// Requested alignment.
        align: usize,
    },
    /// A protected borrow would be invalidated (`StackedBorrowsError::ProtectedConflict`).
    #[error("access by {tag:?} blocked by protected tag {blocked_by:?}")]
    ProtectedConflict {
        /// The tag attempting the access/retag.
        tag: BorrowTag,
        /// The protected tag that blocks it.
        blocked_by: BorrowTag,
    },
    /// The capability cannot perform the access (`StackedBorrowsError::IncompatibleAccess`).
    #[error("tag {tag:?} cannot perform the requested access")]
    IncompatibleAccess {
        /// The offending tag.
        tag: BorrowTag,
    },
    /// The borrow stack has no entry for the tag (`StackedBorrowsError::UnknownTag`).
    #[error("unknown borrow tag {tag:?}")]
    UnknownBorrowTag {
        /// The missing tag.
        tag: BorrowTag,
    },
    /// The retag parent is gone (`StackedBorrowsError::MissingParent`).
    #[error("missing borrow parent {parent:?}")]
    MissingBorrowParent {
        /// The missing parent tag.
        parent: BorrowTag,
    },
    /// No borrow stack for the place (`StackedBorrowsError::UnknownLocation`).
    #[error("unknown borrow location")]
    UnknownBorrowLocation,
    /// The place has no `Place → Address` binding (bridge miss).
    #[error("place is not bound to any allocation")]
    UnboundPlace,
    /// An `Alloc` targeted an already-bound place (bridge collision).
    #[error("place is already bound to an allocation")]
    PlaceAlreadyBound,
    /// A conservative rejection produced by an adapter without a more specific reason.
    #[error("unclassified memory rejection")]
    UnclassifiedRejection,
}

impl From<MemoryError> for StuckReason {
    fn from(err: MemoryError) -> Self {
        match err {
            MemoryError::NullPointer => Self::NullPointer,
            MemoryError::InvalidPointer(id) => Self::InvalidPointer(id),
            MemoryError::UseAfterFree(id) => Self::UseAfterFree(id),
            MemoryError::DoubleFree(id) => Self::DoubleFree(id),
            MemoryError::OutOfBounds {
                offset,
                size,
                alloc_size,
            } => Self::OutOfBounds {
                offset,
                size,
                alloc_size,
            },
            MemoryError::Misaligned { offset, align } => Self::Misaligned { offset, align },
            MemoryError::TaintedRead(id) => Self::TaintedRead(id),
            MemoryError::PointerOverflow => Self::PointerOverflow,
            MemoryError::AllocationFailed { size, align } => Self::AllocationFailed { size, align },
        }
    }
}

/// Map a `Place`-keyed stacked-borrows error to a stuck reason.
///
/// `pub(crate)` so the differential harness can convert reference-model errors
/// through the same mapping `step` uses (so the comparison is exact).
pub(crate) fn stuck_from_borrow(err: StackedBorrowsError<Place>) -> StuckReason {
    match err {
        StackedBorrowsError::UnknownLocation { .. } => StuckReason::UnknownBorrowLocation,
        StackedBorrowsError::UnknownTag { tag, .. } => StuckReason::UnknownBorrowTag { tag },
        StackedBorrowsError::MissingParent { parent, .. } => {
            StuckReason::MissingBorrowParent { parent }
        }
        StackedBorrowsError::IncompatibleAccess { tag, .. } => {
            StuckReason::IncompatibleAccess { tag }
        }
        StackedBorrowsError::ProtectedConflict {
            tag, blocked_by, ..
        } => StuckReason::ProtectedConflict { tag, blocked_by },
    }
}

/// The `Place ↔ Address` keying bridge (spec §3.1, the load-bearing M2.0
/// definition). Holds a one-to-one correspondence between a `Place` and the
/// `AllocId` of its block, and the *current* borrow tag for that place.
#[derive(Debug, Clone, Default)]
struct PlaceAddressBridge {
    place_to_alloc: HashMap<Place, AllocId>,
    current_tag: HashMap<Place, BorrowTag>,
}

impl PlaceAddressBridge {
    fn alloc_id(&self, place: &Place) -> Option<AllocId> {
        self.place_to_alloc.get(place).copied()
    }

    fn tag(&self, place: &Place) -> Option<BorrowTag> {
        self.current_tag.get(place).copied()
    }

    fn bind(&mut self, place: Place, alloc: AllocId, tag: BorrowTag) {
        self.place_to_alloc.insert(place.clone(), alloc);
        self.current_tag.insert(place, tag);
    }

    fn set_tag(&mut self, place: &Place, tag: BorrowTag) {
        self.current_tag.insert(place.clone(), tag);
    }
}

/// A small-step configuration: the byte heap, the active aliasing state, and the
/// keying bridge between them (spec §3.1).
#[derive(Debug, Clone, Default)]
pub struct Config {
    memory: Memory,
    borrows: StackedBorrows<Place>,
    bridge: PlaceAddressBridge,
}

impl Config {
    /// A fresh, empty configuration.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// The `AllocId` bound to `place`, if any (bridge accessor).
    #[must_use]
    pub fn alloc_id(&self, place: &Place) -> Option<AllocId> {
        self.bridge.alloc_id(place)
    }

    /// Whether `place`'s block is currently live in the byte heap.
    #[must_use]
    pub fn is_live(&self, place: &Place) -> bool {
        match self.bridge.alloc_id(place) {
            Some(id) => self.memory.is_valid(Address::new(id, 0)),
            None => false,
        }
    }

    /// Whether the reserved null block is live. Always `false`: `AllocId(0)` is
    /// never a live allocation (spec §3.5(2)).
    #[must_use]
    pub fn null_is_live(&self) -> bool {
        self.memory.is_valid(self.memory.null_ptr())
    }

    /// Read bytes directly from a place's block (test/observation helper).
    /// Returns `None` on any rejection — observation only, not a step.
    #[must_use]
    pub fn peek(&self, place: &Place, offset: u64, size: usize) -> Option<Vec<u8>> {
        let id = self.bridge.alloc_id(place)?;
        self.memory
            .read_bytes(Address::new(id, offset), size)
            .ok()
            .map(<[u8]>::to_vec)
    }
}

/// The result of attempting a step: either a successor configuration with an
/// observation, or a stuck configuration (no successor).
#[derive(Debug)]
#[non_exhaustive]
pub enum StepOutcome {
    /// A successor configuration and its observable result.
    Stepped {
        /// The successor configuration.
        config: Config,
        /// The observable result of the step.
        observation: Observation,
    },
    /// No successor: the configuration is stuck for the given reason.
    Stuck(StuckReason),
}

impl StepOutcome {
    /// The observation, if the step succeeded.
    #[must_use]
    pub fn observation(&self) -> Option<&Observation> {
        match self {
            Self::Stepped { observation, .. } => Some(observation),
            Self::Stuck(_) => None,
        }
    }

    /// The stuck reason, if the configuration is stuck.
    #[must_use]
    pub fn stuck_reason(&self) -> Option<&StuckReason> {
        match self {
            Self::Stuck(reason) => Some(reason),
            Self::Stepped { .. } => None,
        }
    }

    /// Whether this outcome is stuck.
    #[must_use]
    pub fn is_stuck(&self) -> bool {
        matches!(self, Self::Stuck(_))
    }
}

/// The executable small-step relation `step : Config × MemOp → StepOutcome`
/// (spec §3.2).
///
/// `step` consumes the configuration and either returns a successor with an
/// observation, or [`StepOutcome::Stuck`] (no successor). Every executable check
/// failure becomes `Stuck`, mirroring the model's check order exactly; nothing
/// fails open.
#[must_use]
pub fn step(cfg: Config, op: MemOp) -> StepOutcome {
    match op {
        MemOp::Alloc { place, size, align } => step_alloc(cfg, place, size, align),
        MemOp::Dealloc { place } => step_dealloc(cfg, &place),
        MemOp::Read {
            place,
            offset,
            size,
        } => step_read(cfg, &place, offset, size),
        MemOp::Write {
            place,
            offset,
            data,
        } => step_write(cfg, &place, offset, &data),
        MemOp::Retag {
            place,
            permission,
            protector,
        } => step_retag(cfg, &place, permission, protector),
    }
}

fn step_alloc(mut cfg: Config, place: Place, size: usize, align: usize) -> StepOutcome {
    if cfg.bridge.alloc_id(&place).is_some() {
        return StepOutcome::Stuck(StuckReason::PlaceAlreadyBound);
    }
    let addr = match cfg.memory.allocate_aligned(size, align) {
        Ok(addr) => addr,
        Err(err) => return StepOutcome::Stuck(err.into()),
    };
    // Establish the root borrow tag for this place (StackedBorrows::ensure_base).
    let tag = cfg.borrows.ensure_base(place.clone());
    cfg.bridge.bind(place, addr.alloc_id, tag);
    StepOutcome::Stepped {
        config: cfg,
        observation: Observation::Allocated(addr.alloc_id),
    }
}

fn step_dealloc(mut cfg: Config, place: &Place) -> StepOutcome {
    let Some(id) = cfg.bridge.alloc_id(place) else {
        return StepOutcome::Stuck(StuckReason::UnboundPlace);
    };
    match cfg.memory.deallocate(Address::new(id, 0)) {
        Ok(()) => StepOutcome::Stepped {
            config: cfg,
            observation: Observation::Deallocated,
        },
        Err(err) => StepOutcome::Stuck(err.into()),
    }
}

fn step_read(mut cfg: Config, place: &Place, offset: u64, size: usize) -> StepOutcome {
    let Some(id) = cfg.bridge.alloc_id(place) else {
        return StepOutcome::Stuck(StuckReason::UnboundPlace);
    };
    let Some(tag) = cfg.bridge.tag(place) else {
        return StepOutcome::Stuck(StuckReason::UnboundPlace);
    };
    // Aliasing discipline first (ownership layer), then the byte heap (model a),
    // mirroring the executable layering. Both failing checks are stuck.
    if let Err(err) = cfg.borrows.access(place, tag, AccessKind::Read) {
        return StepOutcome::Stuck(stuck_from_borrow(err));
    }
    match cfg.memory.read_bytes(Address::new(id, offset), size) {
        Ok(bytes) => {
            let value = bytes.to_vec();
            StepOutcome::Stepped {
                config: cfg,
                observation: Observation::Read(value),
            }
        }
        Err(err) => StepOutcome::Stuck(err.into()),
    }
}

fn step_write(mut cfg: Config, place: &Place, offset: u64, data: &[u8]) -> StepOutcome {
    let Some(id) = cfg.bridge.alloc_id(place) else {
        return StepOutcome::Stuck(StuckReason::UnboundPlace);
    };
    let Some(tag) = cfg.bridge.tag(place) else {
        return StepOutcome::Stuck(StuckReason::UnboundPlace);
    };
    if let Err(err) = cfg.borrows.access(place, tag, AccessKind::Write) {
        return StepOutcome::Stuck(stuck_from_borrow(err));
    }
    // A full-allocation write clears the tainted flag (handled inside
    // `Memory::write_bytes`, spec §3.2).
    match cfg.memory.write_bytes(Address::new(id, offset), data) {
        Ok(()) => StepOutcome::Stepped {
            config: cfg,
            observation: Observation::Wrote,
        },
        Err(err) => StepOutcome::Stuck(err.into()),
    }
}

fn step_retag(
    mut cfg: Config,
    place: &Place,
    permission: BorrowPermission,
    protector: Option<ProtectorId>,
) -> StepOutcome {
    if cfg.bridge.alloc_id(place).is_none() {
        return StepOutcome::Stuck(StuckReason::UnboundPlace);
    }
    let Some(parent) = cfg.bridge.tag(place) else {
        return StepOutcome::Stuck(StuckReason::UnboundPlace);
    };
    match cfg.borrows.retag(place, parent, permission, protector) {
        Ok(tag) => {
            cfg.bridge.set_tag(place, tag);
            StepOutcome::Stepped {
                config: cfg,
                observation: Observation::Retagged(tag),
            }
        }
        Err(err) => StepOutcome::Stuck(stuck_from_borrow(err)),
    }
}

#[cfg(test)]
mod value_at_address_tests;
