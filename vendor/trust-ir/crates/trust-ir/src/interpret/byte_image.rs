// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Byte images and the sparse allocation store of the reference interpreter.
//!
//! An [`Image`] is a byte range (`None` = an uninitialized byte) held as a
//! persistent rope ([`super::rope`]): its size follows its STRUCTURE, never
//! its length. A run of one byte state is one node, `count` copies of a unit
//! are one node sharing the unit, a copy of an image shares its nodes, and
//! only literal bytes cost their length (they were written one by one).
//!
//! A [`ByteStore`] is one allocation's contents: images tiling `[0, len)`,
//! keyed by start offset. Allocating is one run whatever the size, a `MemSet`
//! is one run, a store of a splat is one run, and a `MemCopy` stores the
//! source's image as ONE run that shares the source's nodes, so copying a
//! region onto its own neighbourhood (the doubling copy of `<[T]>::repeat`)
//! adds a node, never the bytes. A literal store writes in place when a
//! literal run already covers it. Host memory therefore follows the
//! instructions the program RAN, never the sizes or counts it names.

use std::collections::BTreeMap;

use super::rope::{Rope, RopeElem};

#[path = "byte_image_observed.rs"]
mod observed_impl;

/// A byte image: see the module docs.
pub(crate) type Image = Rope<Option<u8>>;

impl RopeElem for Option<u8> {
    /// A literal image is one buffer, however long: it is written in place.
    const FRESH_LEAF: usize = usize::MAX;

    fn same(&self, other: &Self) -> bool {
        self == other
    }
}

impl Rope<Option<u8>> {
    /// Literal bytes.
    pub(crate) fn literal(bytes: Vec<Option<u8>>) -> Self {
        Rope::dense(bytes)
    }

    /// Fully initialized literal bytes.
    pub(crate) fn init_bytes(bytes: &[u8]) -> Self {
        Self::literal(bytes.iter().copied().map(Some).collect())
    }

    /// `len` copies of one byte state: one node.
    pub(crate) fn fill(byte: Option<u8>, len: u64) -> Self {
        Rope::uniform(byte, len)
    }

    /// The offset of the first uninitialized byte, if any. Structural: a
    /// run is asked once, a repeat's first copy answers for all.
    pub(crate) fn first_uninit(&self) -> Option<u64> {
        self.find_first(Option::is_none).map(|(offset, _)| offset)
    }

    /// This image with every uninitialized byte defined as `0` (the object
    /// file's zero padding of a global). Structural: O(nodes + literal
    /// bytes), never O(len).
    pub(crate) fn zero_uninit(&self) -> Self {
        match self.try_map(|byte| Ok::<_, core::convert::Infallible>(Some(byte.unwrap_or(0)))) {
            Ok(image) => image,
            Err(never) => match never {},
        }
    }
}

/// One allocation's bytes: images tiling `[0, len)`, keyed by start offset.
#[derive(Clone)]
pub(crate) struct ByteStore {
    len: u64,
    runs: BTreeMap<u64, Image>,
}

impl core::fmt::Debug for ByteStore {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ByteStore")
            .field("len", &self.len)
            .field("runs", &self.runs.len())
            .finish()
    }
}

impl ByteStore {
    /// `len` bytes in one state (`None`: uninitialized). O(1) in `len`.
    pub(crate) fn new(len: u64, byte: Option<u8>) -> Self {
        let mut runs = BTreeMap::new();
        if len > 0 {
            runs.insert(0, Image::fill(byte, len));
        }
        Self { len, runs }
    }

    /// The image of `[start, start + len)` (in bounds): the covering runs,
    /// sliced and joined, SHARING their nodes. O(runs touched · height).
    pub(crate) fn read(&self, start: u64, len: u64) -> Image {
        if len == 0 {
            return Image::empty();
        }
        let end = start + len;
        let first = self
            .runs
            .range(..=start)
            .next_back()
            .map(|(key, _)| *key)
            .unwrap_or(0);
        let mut parts = Vec::new();
        for (&run_start, image) in self.runs.range(first..end) {
            let run_end = run_start + image.len();
            if run_end <= start {
                continue;
            }
            let lo = start.max(run_start);
            let hi = end.min(run_end);
            parts.push(image.slice(lo - run_start, hi - lo));
        }
        Image::concat(parts)
    }

    /// Byte `offset` (in bounds).
    #[cfg(test)]
    pub(crate) fn byte(&self, offset: u64) -> Option<u8> {
        *self.read(offset, 1).get(0).expect("in bounds")
    }

    /// The number of runs (for structural-size assertions).
    #[cfg(test)]
    pub(crate) fn run_count(&self) -> usize {
        self.runs.len()
    }

    /// Overwrite `[start, start + image.len())` (in bounds) with `image`.
    ///
    /// A literal or uniform image is written in place when one literal run
    /// covers the range, or appended to the literal run that ends where it
    /// starts. Any other image — a repeat, or the joined runs a `MemCopy`
    /// read — is stored as ONE run that shares the image's nodes.
    pub(crate) fn write(&mut self, start: u64, image: &Image) {
        let len = image.len();
        if len == 0 {
            return;
        }
        let end = start + len;
        if image.is_leaf() && self.write_in_place(start, end, image) {
            return;
        }
        self.split_at(start);
        self.split_at(end);
        let covered: Vec<u64> = self.runs.range(start..end).map(|(key, _)| *key).collect();
        for key in covered {
            self.runs.remove(&key);
        }
        // Append a literal to an adjacent literal run that ends where it
        // starts, so a sequence of small stores stays one run.
        if let Some(bytes) = image.as_dense()
            && let Some((&left_start, left)) = self.runs.range_mut(..start).next_back()
            && left_start + left.len() == start
            && left.try_append_in_place(bytes)
        {
            return;
        }
        self.runs.insert(start, image.clone());
    }

    /// Write a literal or uniform `leaf` into the literal run that covers
    /// `[start, end)`, if there is one (copy-on-write of that run's window
    /// when its buffer is shared: its bytes were paid for when written).
    fn write_in_place(&mut self, start: u64, end: u64, leaf: &Image) -> bool {
        let Some((&run_start, run)) = self.runs.range_mut(..=start).next_back() else {
            return false;
        };
        if run_start + run.len() < end || run.as_dense().is_none() {
            return false;
        }
        let window = run.dense_mut().expect("a dense run");
        let at = (start - run_start) as usize;
        let len = (end - start) as usize;
        if let Some(bytes) = leaf.as_dense() {
            window[at..at + len].copy_from_slice(bytes);
        } else if let Some(byte) = leaf.as_uniform() {
            window[at..at + len].fill(*byte);
        } else {
            unreachable!("a leaf is dense or uniform");
        }
        true
    }

    /// Make `offset` a run boundary.
    fn split_at(&mut self, offset: u64) {
        if offset == 0 || offset >= self.len || self.runs.contains_key(&offset) {
            return;
        }
        let Some((&run_start, run)) = self.runs.range(..offset).next_back() else {
            return;
        };
        let run_len = run.len();
        if run_start + run_len <= offset {
            return;
        }
        let left = run.slice(0, offset - run_start);
        let right = run.slice(offset - run_start, run_start + run_len - offset);
        self.runs.insert(run_start, left);
        self.runs.insert(offset, right);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_four_gib_store_is_one_run_and_reads_back_structurally() {
        let len = 4u64 << 30;
        let mut store = ByteStore::new(len, None);
        let element = Image::init_bytes(&[1, 0, 0, 0]);
        store.write(0, &element.repeat(len / 4));
        assert_eq!(store.run_count(), 1);
        assert_eq!(
            store.read(len - 4, 4).to_vec(),
            vec![Some(1), Some(0), Some(0), Some(0)]
        );
        // An unaligned window is still a compact image.
        // Cutting a repeat of 2^30 copies joins its balanced spine along the
        // cut: O(log len) nodes, never O(len).
        let window = store.read(3, len - 8);
        assert!(window.node_count() <= 4 * 64, "{}", window.node_count());
        assert!(window.height() <= 64, "height {}", window.height());
        assert_eq!(window.first_uninit(), None);
    }

    #[test]
    fn literal_stores_merge_and_write_in_place() {
        let mut store = ByteStore::new(64, None);
        for offset in 0..16 {
            store.write(offset, &Image::init_bytes(&[offset as u8]));
        }
        assert_eq!(
            store.run_count(),
            2,
            "one literal run plus the untouched tail"
        );
        store.write(4, &Image::init_bytes(&[0xAA, 0xBB]));
        assert_eq!(store.run_count(), 2, "written in place");
        assert_eq!(store.byte(5), Some(0xBB));
        assert_eq!(store.byte(20), None);
        store.write(0, &Image::fill(Some(7), 64));
        assert_eq!(store.run_count(), 1);
        assert_eq!(store.byte(63), Some(7));
    }

    #[test]
    fn a_write_inside_a_repeat_splits_it_without_expanding_it() {
        let len = 1u64 << 40;
        let mut store = ByteStore::new(len, None);
        store.write(0, &Image::init_bytes(&[1, 2]).repeat(len / 2));
        store.write(1000, &Image::init_bytes(&[9, 9]));
        assert!(store.run_count() <= 3);
        assert_eq!(store.byte(999), Some(2));
        assert_eq!(store.byte(1000), Some(9));
        assert_eq!(store.byte(1002), Some(1));
        assert!(store.read(0, len).node_count() <= 4 * 64);
    }

    #[test]
    fn repeat_normalizes_uniform_units_to_fills() {
        let fill = Image::init_bytes(&[0, 0, 0, 0]).repeat(1 << 50);
        assert_eq!(fill.node_count(), 1);
        assert_eq!(fill.as_uniform(), Some(&Some(0)));
        let nested = Image::init_bytes(&[1, 2]).repeat(3).repeat(5);
        assert_eq!(nested.node_count(), 2, "one repeat of the literal unit");
        assert_eq!(nested.len(), 30);
        assert_eq!(nested.get(29), Some(&Some(2)));
    }

    /// The `<[T]>::repeat` shape (reviewer B, 2026-09-23): copy `[0, k)` to
    /// `[k, 2k)` with `k` doubling. Each copy stores the source's image as
    /// one run that shares it, so the store grows by a node per copy — never
    /// by the bytes copied.
    #[test]
    fn a_doubling_copy_adds_nodes_not_bytes() {
        let len = 1u64 << 40;
        let mut store = ByteStore::new(len, None);
        store.write(0, &Image::init_bytes(&[1]));
        store.write(1, &Image::init_bytes(&[2]));
        let mut k = 2u64;
        while k < len {
            let copy = store.read(0, k);
            store.write(k, &copy);
            k *= 2;
        }
        let whole = store.read(0, len);
        assert!(whole.node_count() <= 8, "{} nodes", whole.node_count());
        assert_eq!(store.byte(len - 1), Some(2));
        assert_eq!(store.byte(len - 2), Some(1));
        assert_eq!(whole.first_uninit(), None);
    }

    /// Random literal writes, fills and (overlapping) copies against a dense
    /// model of the allocation.
    #[test]
    fn random_store_operations_agree_with_a_dense_model() {
        let mut state = 0x2545_F491_4F6C_DD1Du64;
        let mut next = move |bound: u64| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state % bound.max(1)
        };
        for _ in 0..300 {
            let len = 1 + next(96);
            let mut store = ByteStore::new(len, None);
            let mut model: Vec<Option<u8>> = vec![None; len as usize];
            for _ in 0..60 {
                let start = next(len);
                let span = 1 + next(len - start);
                match next(4) {
                    0 => {
                        let bytes: Vec<Option<u8>> = (0..span)
                            .map(|_| match next(3) {
                                0 => None,
                                n => Some(n as u8),
                            })
                            .collect();
                        store.write(start, &Image::literal(bytes.clone()));
                        model[start as usize..(start + span) as usize].copy_from_slice(&bytes);
                    }
                    1 => {
                        let byte = Some(next(3) as u8);
                        store.write(start, &Image::fill(byte, span));
                        model[start as usize..(start + span) as usize].fill(byte);
                    }
                    _ => {
                        // A memmove: read the whole source, then write it.
                        let to = next(len - span + 1);
                        let image = store.read(start, span);
                        store.write(to, &image);
                        let copied = model[start as usize..(start + span) as usize].to_vec();
                        model[to as usize..(to + span) as usize].copy_from_slice(&copied);
                    }
                }
                let at = next(len);
                let width = 1 + next(len - at);
                let window = store.read(at, width);
                window.check_invariants();
                assert_eq!(
                    window.to_vec(),
                    model[at as usize..(at + width) as usize].to_vec()
                );
                assert_eq!(
                    window.first_uninit(),
                    model[at as usize..(at + width) as usize]
                        .iter()
                        .position(Option::is_none)
                        .map(|index| index as u64)
                );
            }
            assert_eq!(store.read(0, len).to_vec(), model);
            let zeroed = store.read(0, len).zero_uninit();
            assert!(zeroed.iter().all(Option::is_some));
        }
    }

    /// The same doubling, with a distinct byte written between copies: no
    /// two copies are the same unit, and the image is still a DAG whose size
    /// follows the number of copies.
    #[test]
    fn an_interleaved_doubling_copy_stays_a_dag() {
        let steps = 40u32;
        let len = (1u64 << (steps + 1)) + 64;
        let mut store = ByteStore::new(len, None);
        store.write(0, &Image::init_bytes(&[0]));
        let mut filled = 1u64;
        for step in 0..steps {
            let copy = store.read(0, filled);
            store.write(filled, &Image::init_bytes(&[step as u8 + 1]));
            store.write(filled + 1, &copy);
            filled = 2 * filled + 1;
        }
        // Each copy reads O(step) runs, so the DAG has O(steps^2) nodes —
        // for 2^41 bytes.
        let whole = store.read(0, filled);
        assert!(
            whole.node_count() <= 16 * (steps * steps) as usize,
            "{} nodes",
            whole.node_count()
        );
        assert!(whole.height() <= 128, "height {}", whole.height());
        assert_eq!(whole.first_uninit(), None);
        // Byte `2^j - 1` is the separator written at step `j - 1`.
        for step in 1..=steps {
            assert_eq!(store.byte((1u64 << step) - 1), Some(step as u8));
        }
    }
}
