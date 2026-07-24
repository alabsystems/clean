// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Finite separation-logic semantics for verification-side checks.
//!
//! This keeps the shared core operators intentionally small:
//! - `emp`
//! - singleton points-to cells
//! - separating conjunction
//! - magic wand
//! - pure propositions
//! - explicit finite existential witnesses
//!
//! `Exists` is represented as a list of concrete witness instantiations, and
//! `Wand` quantifies over heaps generated from the points-to atoms that appear
//! in the propositions plus one fresh singleton cell. That gives the verifier a
//! predictable finite model for basic tests and entailment checks.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::sem_memory_model::{Address, MemoryValue};

/// Separation-logic propositions over shared kernel addresses and values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SepLogicProp {
    /// Empty heap proposition.
    Emp,
    /// Singleton heap proposition `addr |-> value`.
    PointsTo {
        /// Concrete address owned by the proposition.
        address: Address,
        /// Value stored at `address`.
        value: MemoryValue,
    },
    /// Separating conjunction `P * Q`.
    Star(Box<Self>, Box<Self>),
    /// Magic wand `P -* Q`.
    Wand(Box<Self>, Box<Self>),
    /// Heap-independent proposition.
    Pure(bool),
    /// Finite existential witnesses.
    Exists(Vec<Self>),
}

impl SepLogicProp {
    /// Build a singleton points-to proposition.
    #[must_use]
    pub fn points_to(address: Address, value: MemoryValue) -> Self {
        Self::PointsTo { address, value }
    }

    /// Build a separating conjunction.
    #[must_use]
    pub fn star(left: Self, right: Self) -> Self {
        Self::Star(Box::new(left), Box::new(right))
    }

    /// Build a magic wand.
    #[must_use]
    pub fn wand(left: Self, right: Self) -> Self {
        Self::Wand(Box::new(left), Box::new(right))
    }

    /// Build a finite existential proposition.
    #[must_use]
    pub fn exists(witnesses: impl IntoIterator<Item = Self>) -> Self {
        Self::Exists(witnesses.into_iter().collect())
    }
}

/// Partial heap model used by the evaluator.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct HeapModel {
    cells: BTreeMap<Address, MemoryValue>,
}

impl HeapModel {
    /// Create an empty heap.
    #[must_use]
    pub fn new() -> Self {
        Self {
            cells: BTreeMap::new(),
        }
    }

    /// Create a singleton heap.
    #[must_use]
    pub fn singleton(address: Address, value: MemoryValue) -> Self {
        let mut heap = Self::new();
        heap.insert(address, value);
        heap
    }

    /// Insert or overwrite a heap cell.
    pub fn insert(&mut self, address: Address, value: MemoryValue) -> Option<MemoryValue> {
        self.cells.insert(address, value)
    }

    /// Remove a heap cell.
    pub fn remove(&mut self, address: &Address) -> Option<MemoryValue> {
        self.cells.remove(address)
    }

    /// Read a heap cell.
    #[must_use]
    pub fn get(&self, address: &Address) -> Option<MemoryValue> {
        self.cells.get(address).copied()
    }

    /// Check whether the heap is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Return the number of cells in the heap.
    #[must_use]
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Iterate over heap cells.
    pub fn iter(&self) -> impl Iterator<Item = (&Address, &MemoryValue)> {
        self.cells.iter()
    }

    /// Check whether two heaps are address-disjoint.
    #[must_use]
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.cells
            .keys()
            .all(|address| !other.cells.contains_key(address))
    }

    /// Union two disjoint heaps.
    #[must_use]
    pub fn union(&self, other: &Self) -> Option<Self> {
        if !self.is_disjoint(other) {
            return None;
        }

        let mut cells = self.cells.clone();
        cells.extend(
            other
                .cells
                .iter()
                .map(|(address, value)| (*address, *value)),
        );
        Some(Self { cells })
    }

    fn entries(&self) -> Vec<(Address, MemoryValue)> {
        self.cells
            .iter()
            .map(|(address, value)| (*address, *value))
            .collect()
    }
}

impl FromIterator<(Address, MemoryValue)> for HeapModel {
    fn from_iter<T: IntoIterator<Item = (Address, MemoryValue)>>(iter: T) -> Self {
        Self {
            cells: iter.into_iter().collect(),
        }
    }
}

/// Evaluate a separation-logic proposition against a heap.
#[must_use]
pub fn evaluate(prop: &SepLogicProp, heap: &HeapModel) -> bool {
    let candidates = candidate_heaps(&[prop], &[heap]);
    evaluate_with_candidates(prop, heap, &candidates)
}

/// Apply the frame rule by checking that the same framed subheap is preserved
/// between `initial_heap` and `result_heap`.
///
/// If `initial_heap` does not satisfy `pre * frame`, the implication is treated
/// as vacuously true.
#[must_use]
pub fn frame_rule(
    initial_heap: &HeapModel,
    result_heap: &HeapModel,
    pre: &SepLogicProp,
    post: &SepLogicProp,
    frame: &SepLogicProp,
) -> bool {
    let candidates = candidate_heaps(&[pre, post, frame], &[initial_heap, result_heap]);
    let mut has_framed_pre = false;

    let holds = exists_heap_split(initial_heap, &mut |pre_heap, frame_before| {
        if !evaluate_with_candidates(pre, pre_heap, &candidates)
            || !evaluate_with_candidates(frame, frame_before, &candidates)
        {
            return false;
        }

        has_framed_pre = true;
        exists_heap_split(result_heap, &mut |post_heap, frame_after| {
            frame_before == frame_after
                && evaluate_with_candidates(post, post_heap, &candidates)
                && evaluate_with_candidates(frame, frame_after, &candidates)
        })
    });

    holds || !has_framed_pre
}

/// Check basic entailment `lhs |- rhs` by finite model search.
#[must_use]
pub fn entailment_check(lhs: &SepLogicProp, rhs: &SepLogicProp) -> bool {
    let candidates = candidate_heaps(&[lhs, rhs], &[]);
    candidates.iter().all(|heap| {
        !evaluate_with_candidates(lhs, heap, &candidates)
            || evaluate_with_candidates(rhs, heap, &candidates)
    })
}

fn evaluate_with_candidates(
    prop: &SepLogicProp,
    heap: &HeapModel,
    candidates: &[HeapModel],
) -> bool {
    match prop {
        SepLogicProp::Emp => heap.is_empty(),
        SepLogicProp::PointsTo { address, value } => {
            heap.len() == 1 && heap.get(address) == Some(*value)
        }
        SepLogicProp::Star(left, right) => exists_heap_split(heap, &mut |left_heap, right_heap| {
            evaluate_with_candidates(left, left_heap, candidates)
                && evaluate_with_candidates(right, right_heap, candidates)
        }),
        SepLogicProp::Wand(left, right) => candidates.iter().all(|extension| {
            if !heap.is_disjoint(extension) {
                return true;
            }
            if !evaluate_with_candidates(left, extension, candidates) {
                return true;
            }

            heap.union(extension)
                .map(|combined| evaluate_with_candidates(right, &combined, candidates))
                .unwrap_or(false)
        }),
        SepLogicProp::Pure(value) => *value,
        SepLogicProp::Exists(witnesses) => witnesses
            .iter()
            .any(|witness| evaluate_with_candidates(witness, heap, candidates)),
    }
}

fn candidate_heaps(props: &[&SepLogicProp], heaps: &[&HeapModel]) -> Vec<HeapModel> {
    let mut domains: BTreeMap<Address, BTreeSet<MemoryValue>> = BTreeMap::new();
    for prop in props {
        collect_atoms(prop, &mut domains);
    }
    for heap in heaps {
        for (address, value) in heap.iter() {
            domains.entry(*address).or_default().insert(*value);
        }
    }

    if let Some(fresh_address) = fresh_address(&domains) {
        domains
            .entry(fresh_address)
            .or_default()
            .insert(MemoryValue::ZERO);
    }

    enumerate_heaps(&domains)
}

fn collect_atoms(prop: &SepLogicProp, domains: &mut BTreeMap<Address, BTreeSet<MemoryValue>>) {
    match prop {
        SepLogicProp::Emp | SepLogicProp::Pure(_) => {}
        SepLogicProp::PointsTo { address, value } => {
            domains.entry(*address).or_default().insert(*value);
        }
        SepLogicProp::Star(left, right) | SepLogicProp::Wand(left, right) => {
            collect_atoms(left, domains);
            collect_atoms(right, domains);
        }
        SepLogicProp::Exists(witnesses) => {
            for witness in witnesses {
                collect_atoms(witness, domains);
            }
        }
    }
}

fn fresh_address(domains: &BTreeMap<Address, BTreeSet<MemoryValue>>) -> Option<Address> {
    let max_raw = domains
        .keys()
        .map(|address| address.raw())
        .max()
        .unwrap_or(0);
    max_raw.checked_add(1).map(Address::new)
}

fn enumerate_heaps(domains: &BTreeMap<Address, BTreeSet<MemoryValue>>) -> Vec<HeapModel> {
    fn go(
        entries: &[(Address, Vec<MemoryValue>)],
        idx: usize,
        current: &mut HeapModel,
        out: &mut Vec<HeapModel>,
    ) {
        if idx == entries.len() {
            out.push(current.clone());
            return;
        }

        let (address, values) = &entries[idx];

        go(entries, idx + 1, current, out);
        for value in values {
            current.insert(*address, *value);
            go(entries, idx + 1, current, out);
            current.remove(address);
        }
    }

    let entries: Vec<_> = domains
        .iter()
        .map(|(address, values)| (*address, values.iter().copied().collect::<Vec<_>>()))
        .collect();
    let mut out = Vec::new();
    let mut current = HeapModel::new();
    go(&entries, 0, &mut current, &mut out);
    out
}

fn exists_heap_split<F>(heap: &HeapModel, predicate: &mut F) -> bool
where
    F: FnMut(&HeapModel, &HeapModel) -> bool,
{
    fn go<F>(
        entries: &[(Address, MemoryValue)],
        idx: usize,
        left: &mut HeapModel,
        right: &mut HeapModel,
        predicate: &mut F,
    ) -> bool
    where
        F: FnMut(&HeapModel, &HeapModel) -> bool,
    {
        if idx == entries.len() {
            return predicate(left, right);
        }

        let (address, value) = entries[idx];

        left.insert(address, value);
        if go(entries, idx + 1, left, right, predicate) {
            return true;
        }
        left.remove(&address);

        right.insert(address, value);
        if go(entries, idx + 1, left, right, predicate) {
            return true;
        }
        right.remove(&address);

        false
    }

    let entries = heap.entries();
    let mut left = HeapModel::new();
    let mut right = HeapModel::new();
    go(&entries, 0, &mut left, &mut right, predicate)
}

#[cfg(test)]
mod tests {
    use super::{entailment_check, evaluate, frame_rule, HeapModel, SepLogicProp};
    use clean_kernel::sem_memory_model::{Address, MemoryValue};

    fn addr(raw: u64) -> Address {
        Address::new(raw)
    }

    fn val(byte: u8) -> MemoryValue {
        MemoryValue::new(byte)
    }

    #[test]
    fn evaluate_emp_matches_only_empty_heap() {
        assert!(evaluate(&SepLogicProp::Emp, &HeapModel::new()));
        assert!(!evaluate(
            &SepLogicProp::Emp,
            &HeapModel::singleton(addr(1), val(7)),
        ));
    }

    #[test]
    fn evaluate_points_to_matches_singleton_heap() {
        let prop = SepLogicProp::points_to(addr(1), val(7));
        assert!(evaluate(&prop, &HeapModel::singleton(addr(1), val(7))));
        assert!(!evaluate(&prop, &HeapModel::singleton(addr(1), val(8))));
    }

    #[test]
    fn evaluate_star_requires_disjoint_subheaps() {
        let prop = SepLogicProp::star(
            SepLogicProp::points_to(addr(1), val(7)),
            SepLogicProp::points_to(addr(2), val(9)),
        );
        let heap = HeapModel::from_iter([(addr(1), val(7)), (addr(2), val(9))]);

        assert!(evaluate(&prop, &heap));
        assert!(!evaluate(&prop, &HeapModel::singleton(addr(1), val(7))));
    }

    #[test]
    fn evaluate_wand_quantifies_over_candidate_extensions() {
        let wand = SepLogicProp::wand(
            SepLogicProp::points_to(addr(1), val(10)),
            SepLogicProp::star(
                SepLogicProp::points_to(addr(1), val(10)),
                SepLogicProp::points_to(addr(2), val(20)),
            ),
        );

        assert!(evaluate(&wand, &HeapModel::singleton(addr(2), val(20))));
        assert!(!evaluate(&wand, &HeapModel::new()));
    }

    #[test]
    fn evaluate_pure_is_heap_independent() {
        assert!(evaluate(
            &SepLogicProp::Pure(true),
            &HeapModel::singleton(addr(1), val(1)),
        ));
        assert!(!evaluate(&SepLogicProp::Pure(false), &HeapModel::new()));
    }

    #[test]
    fn evaluate_exists_accepts_any_matching_witness() {
        let prop = SepLogicProp::exists([
            SepLogicProp::points_to(addr(1), val(9)),
            SepLogicProp::points_to(addr(1), val(10)),
        ]);

        assert!(evaluate(&prop, &HeapModel::singleton(addr(1), val(10))));
        assert!(!evaluate(&prop, &HeapModel::singleton(addr(1), val(11))));
    }

    #[test]
    fn frame_rule_requires_the_frame_to_be_preserved() {
        let pre = SepLogicProp::points_to(addr(1), val(10));
        let post = SepLogicProp::points_to(addr(1), val(11));
        let frame = SepLogicProp::points_to(addr(2), val(20));

        let initial = HeapModel::from_iter([(addr(1), val(10)), (addr(2), val(20))]);
        let result = HeapModel::from_iter([(addr(1), val(11)), (addr(2), val(20))]);
        let mutated_frame = HeapModel::from_iter([(addr(1), val(11)), (addr(2), val(21))]);

        assert!(frame_rule(&initial, &result, &pre, &post, &frame));
        assert!(!frame_rule(&initial, &mutated_frame, &pre, &post, &frame,));
    }

    #[test]
    fn entailment_check_handles_basic_entailment() {
        let lhs = SepLogicProp::points_to(addr(1), val(10));
        let rhs = SepLogicProp::star(lhs.clone(), SepLogicProp::Emp);
        let bad_rhs = SepLogicProp::points_to(addr(1), val(11));

        assert!(entailment_check(&lhs, &rhs));
        assert!(!entailment_check(&lhs, &bad_rhs));
    }
}
