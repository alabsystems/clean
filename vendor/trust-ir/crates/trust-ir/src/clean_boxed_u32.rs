// Copyright 2026 Andrew Yates | Apache-2.0
//! Source-bound, sequential ownership semantics of Clean's 64-bit UInt32 leaf ABI.
//!
//! This is a concrete byte/ownership model, NOT a HostCalls callback, body license,
//! native link attestation or a change to the general interpreter's ARC rules.
//! The source binding identifies the Rust runtime, not a compiled C/header copy.
//! Initial memory and caller-owned credits are explicit admission premises.
//! Unsafe runtime inputs outside that premise are refused here, not executed:
//! these errors do not assert that the unsafe native runtime traps on bad pointers.
//!
//! A UInt32 heap box is a live, 8-aligned, 12-byte Ctor leaf: header bytes
//! [rc:u32 LE, tag=0, kind=0, children=0, scalar_size=4], payload:u32 LE.
//! RC stores references MINUS ONE. Sticky drops preserve the cell; last drops
//! retire it. All u32 encoder outputs on this target are tagged, including MAX.
//! Ghost frame credits count input OCCURRENCES, including aliased words. They
//! never create native references. Distinct frames can share only pre-owned
//! credits; every release consumes exactly one slot, even for a tagged scalar.

use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

pub const CLEAN_RUNTIME_REVISION: &str = "1ffadbf63246159a02b7443f8fab4a0400388001";
pub const RC_STICKY_DROP: u32 = 0xe000_0000;
pub const HEADER_BYTES: usize = 8;
pub const BOX_BYTES: usize = 12;

/// The complete sources needed to identify this leaf runtime path.
pub struct RuntimeSources<'a> {
    pub object_model: &'a [u8],
    pub ctor_scalar: &'a [u8],
    pub rc_core: &'a [u8],
    pub refcount: &'a [u8],
    pub public_api: &'a [u8],
}
/// Identity of inspected source only; supplies no kernel or machine-code credit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RuntimeSourceBinding {
    _sealed: (),
}

// Source digests inserted from the immutable Clean revision, not caller labels.
const SOURCE_HASHES: [&str; 5] = [
    "0cea35dcfc1bc034c55254c3d585bf58e3f627f465dcb319226967775eb4a671",
    "6cab70395f281189a500c1bc93c98ba72d45ebec1bbc5397fd59c2ce622a7562",
    "e7e239ce957e898a06257e00d82c27cf67d162e0573e167d26b510c20082aec2",
    "614a811b14ae8084e44f0833006a8e4d0bdb04706532f3aa27c061f59562882b",
    "1c7a25fea627e48d599dc20f5d2c808436ba4ce38730155fa1cbeb1dbb054987",
];
impl RuntimeSources<'_> {
    pub fn bind(&self) -> Result<RuntimeSourceBinding, Fault> {
        for (i, bytes) in [
            self.object_model,
            self.ctor_scalar,
            self.rc_core,
            self.refcount,
            self.public_api,
        ]
        .into_iter()
        .enumerate()
        {
            if format!("{:x}", Sha256::digest(bytes)) != SOURCE_HASHES[i] {
                return Err(Fault::RuntimeSourceMismatch(i));
            }
        }
        Ok(RuntimeSourceBinding { _sealed: () })
    }
}

/// A complete allocation image. Alignment is the allocation/deallocation layout,
/// not just an address divisibility fact. Unrelated cells are preserved byte-for-byte.
/// Byte None means uninitialized. Dead cells remain as retirement evidence;
/// this model never reuses an address (no provenance erasure by reallocation).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Allocation {
    pub address: u64,
    pub alignment: u64,
    pub bytes: Vec<Option<u8>>,
    pub live: bool,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct FrameId(u64);
#[derive(Debug, Clone, PartialEq, Eq)]
struct Frame {
    words: Vec<u64>,
    remaining: Vec<bool>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UInt32Heap {
    allocations: BTreeMap<u64, Allocation>,
    caller_credits: BTreeMap<u64, u64>,
    frames: BTreeMap<FrameId, Frame>,
    retired_frames: BTreeSet<FrameId>,
    next_frame: u64,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fault {
    RuntimeSourceMismatch(usize),
    InvalidAllocation,
    OverlappingAllocations,
    Null,
    TaggedOutOfRange,
    Misaligned,
    UnknownAllocation,
    DeadAllocation,
    Uninitialized(usize),
    WrongKind,
    WrongLayout,
    InvalidRefcount,
    MissingOwnedReferences { address: u64, need: u64, have: u64 },
    FrameExhausted,
    UnknownFrame,
    RetiredFrame,
    InvalidSlot,
    ReleasedInput,
    UnreleasedInputs,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReleaseEffect {
    Tagged,
    Decremented {
        address: u64,
        before: u32,
        after: u32,
    },
    Frozen {
        address: u64,
        count: u32,
    },
    Freed {
        address: u64,
        size: u64,
        alignment: u64,
    },
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OwnedOutput {
    word: u64,
    value: u32,
}
impl OwnedOutput {
    pub fn word(self) -> u64 {
        self.word
    }
    pub fn value(self) -> u32 {
        self.value
    }
}
/// Exact canonical encoder on pointer64: no heap allocation, no 31-bit cutoff.
pub fn encode(value: u32) -> OwnedOutput {
    OwnedOutput {
        word: (u64::from(value) << 1) | 1,
        value,
    }
}

impl UInt32Heap {
    /// Admit a nonoverlapping bounded64 memory and separately owned references.
    /// Credits may omit references owned by the caller's external frame. Frozen
    /// counts need explicit ghost credits too; they do not license alias forgery.
    pub fn new(
        _: RuntimeSourceBinding,
        images: Vec<Allocation>,
        credits: BTreeMap<u64, u64>,
    ) -> Result<Self, Fault> {
        let mut allocations = BTreeMap::new();
        for image in images {
            if image.address == 0
                || !image.alignment.is_power_of_two()
                || image.address % image.alignment != 0
                || image.bytes.is_empty()
                || image
                    .address
                    .checked_add(image.bytes.len() as u64)
                    .is_none()
                || allocations.insert(image.address, image).is_some()
            {
                return Err(Fault::InvalidAllocation);
            }
        }
        let mut end = 0;
        for image in allocations.values() {
            if image.address < end {
                return Err(Fault::OverlappingAllocations);
            }
            end = image.address + image.bytes.len() as u64;
        }
        let heap = Self {
            allocations,
            caller_credits: credits,
            frames: BTreeMap::new(),
            retired_frames: BTreeSet::new(),
            next_frame: 0,
        };
        for (&address, &need) in &heap.caller_credits {
            let (_, rc) = heap.inspect_heap(address)?;
            if rc < RC_STICKY_DROP && need > u64::from(rc) + 1 {
                return Err(Fault::MissingOwnedReferences {
                    address,
                    need,
                    have: u64::from(rc) + 1,
                });
            }
        }
        Ok(heap)
    }
    pub fn allocations(&self) -> &BTreeMap<u64, Allocation> {
        &self.allocations
    }
    pub fn caller_credits(&self) -> &BTreeMap<u64, u64> {
        &self.caller_credits
    }
    /// The word of one still-owned occurrence; no credit is created.
    pub fn transferred_input(&self, frame: FrameId, slot: usize) -> Result<u64, Fault> {
        self.slot(frame, slot)
    }
    /// Read-only transferred-reference occurrences for a refinement projection.
    /// This creates no ownership or execution authority; spent slots are absent.
    pub fn transferred_inputs(&self) -> Vec<(FrameId, Vec<u64>)> {
        self.frames
            .iter()
            .map(|(id, frame)| {
                (
                    *id,
                    frame
                        .words
                        .iter()
                        .zip(&frame.remaining)
                        .filter_map(|(&word, &live)| live.then_some(word))
                        .collect(),
                )
            })
            .collect()
    }
    pub fn is_retired(&self, frame: FrameId) -> bool {
        self.retired_frames.contains(&frame)
    }

    fn inspect_heap(&self, word: u64) -> Result<(u32, u32), Fault> {
        if word == 0 {
            return Err(Fault::Null);
        }
        if word % 8 != 0 {
            return Err(Fault::Misaligned);
        }
        let image = self
            .allocations
            .get(&word)
            .ok_or(Fault::UnknownAllocation)?;
        if !image.live {
            return Err(Fault::DeadAllocation);
        }
        if image.alignment != 8 || image.bytes.len() != BOX_BYTES {
            return Err(Fault::WrongLayout);
        }
        let mut bytes = [0; BOX_BYTES];
        for (i, b) in bytes.iter_mut().enumerate() {
            *b = image.bytes[i].ok_or(Fault::Uninitialized(i))?;
        }
        if bytes[5] != 0 {
            return Err(Fault::WrongKind);
        }
        if bytes[4] != 0 || bytes[6] != 0 || bytes[7] != 4 {
            return Err(Fault::WrongLayout);
        }
        let rc = u32::from_le_bytes(bytes[..4].try_into().unwrap());
        if rc == u32::MAX {
            return Err(Fault::InvalidRefcount);
        }
        let value = u32::from_le_bytes(bytes[HEADER_BYTES..].try_into().unwrap());
        Ok((value, rc))
    }
    /// Borrowing read. No release/credit creation; validity is checked anew.
    pub fn decode(&self, word: u64) -> Result<u32, Fault> {
        if word & 1 == 1 {
            u32::try_from(word >> 1).map_err(|_| Fault::TaggedOutOfRange)
        } else {
            self.inspect_heap(word).map(|(value, _)| value)
        }
    }
    /// Atomic admission: validate every occurrence and multiplicity BEFORE
    /// transferring any credits or creating a frame. No hidden retain operation.
    pub fn begin(&mut self, words: &[u64]) -> Result<FrameId, Fault> {
        let mut needed = BTreeMap::<u64, u64>::new();
        for &word in words {
            self.decode(word)?;
            if word & 1 == 0 {
                *needed.entry(word).or_default() += 1;
            }
        }
        for (&address, &need) in &needed {
            let have = self.caller_credits.get(&address).copied().unwrap_or(0);
            if need > have {
                return Err(Fault::MissingOwnedReferences {
                    address,
                    need,
                    have,
                });
            }
        }
        let id = FrameId(self.next_frame);
        let next = self
            .next_frame
            .checked_add(1)
            .ok_or(Fault::FrameExhausted)?;
        for (address, need) in needed {
            *self.caller_credits.get_mut(&address).unwrap() -= need;
        }
        self.frames.insert(
            id,
            Frame {
                words: words.to_vec(),
                remaining: vec![true; words.len()],
            },
        );
        self.next_frame = next;
        Ok(id)
    }
    fn frame(&self, id: FrameId) -> Result<&Frame, Fault> {
        self.frames.get(&id).ok_or(if self.is_retired(id) {
            Fault::RetiredFrame
        } else {
            Fault::UnknownFrame
        })
    }
    fn slot(&self, id: FrameId, slot: usize) -> Result<u64, Fault> {
        let frame = self.frame(id)?;
        let remaining = frame.remaining.get(slot).ok_or(Fault::InvalidSlot)?;
        if !remaining {
            return Err(Fault::ReleasedInput);
        }
        Ok(frame.words[slot])
    }
    pub fn decode_input(&self, id: FrameId, slot: usize) -> Result<u32, Fault> {
        self.decode(self.slot(id, slot)?)
    }
    /// One source-bound runtime leaf release: update the RC bytes or retire exactly
    /// the last-owned leaf. No arbitrary host effect or whole-world equality.
    pub fn release(&mut self, id: FrameId, slot: usize) -> Result<ReleaseEffect, Fault> {
        let word = self.slot(id, slot)?;
        let effect = if word & 1 == 1 {
            self.decode(word)?;
            ReleaseEffect::Tagged
        } else {
            let (_, rc) = self.inspect_heap(word)?;
            let cell = self.allocations.get_mut(&word).unwrap();
            if rc >= RC_STICKY_DROP {
                ReleaseEffect::Frozen {
                    address: word,
                    count: rc,
                }
            } else if rc == 0 {
                // drop_cell first wraps 0 to MAX, then the last-drop path frees
                // this childless Ctor with object_layout(0,4) = (12,8).
                cell.bytes[..4].fill(Some(255));
                cell.live = false;
                ReleaseEffect::Freed {
                    address: word,
                    size: BOX_BYTES as u64,
                    alignment: 8,
                }
            } else {
                for (b, v) in cell.bytes[..4].iter_mut().zip((rc - 1).to_le_bytes()) {
                    *b = Some(v);
                }
                ReleaseEffect::Decremented {
                    address: word,
                    before: rc,
                    after: rc - 1,
                }
            }
        };
        self.frames.get_mut(&id).unwrap().remaining[slot] = false;
        Ok(effect)
    }
    /// Root retirement requires EVERY transferred occurrence consumed. Failure
    /// preserves the open frame and memory so no leaked reference is concealed.
    /// The canonical output is an owned immediate, not a fresh heap allocation.
    pub fn finish(&mut self, id: FrameId, value: u32) -> Result<OwnedOutput, Fault> {
        if self.frame(id)?.remaining.iter().any(|&live| live) {
            return Err(Fault::UnreleasedInputs);
        }
        self.frames.remove(&id);
        self.retired_frames.insert(id);
        Ok(encode(value))
    }
}
