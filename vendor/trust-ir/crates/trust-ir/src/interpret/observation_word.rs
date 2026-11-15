// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Opaque symbolic sequences for structural reference observations. Symbols
//! are caller labels, never fabricated interpreter values or proof evidence.

use super::rope::{Rope, RopeElem};

#[derive(Clone, Copy)]
struct Symbol(u64);

impl RopeElem for Symbol {
    const FRESH_LEAF: usize = 16;
    fn same(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

/// A checked sequence operation exceeded the u64 logical length domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WordLengthOverflow;

impl core::fmt::Display for WordLengthOverflow {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("observation word length exceeds u64")
    }
}
impl std::error::Error for WordLengthOverflow {}

/// A persistent symbolic word backed by the interpreter's structural rope.
/// Construction preserves uniform runs, periodic units and shared pieces.
/// Labels have no intrinsic meaning; comparison uses the caller's stable pair
/// predicate. This ordinary reference API supplies no execution admission,
/// observation budget, source license or proof authority.
///
/// ```
/// use trust_ir::interpret::ObservationWord;
/// let a = ObservationWord::from_symbols(&[1, 2]).unwrap().repeat(4096).unwrap();
/// let b = ObservationWord::from_symbols(&[3, 4, 3, 4]).unwrap().repeat(2048).unwrap();
/// assert!(a.equivalent_by(&b, |x, y| x % 2 == y % 2));
/// ```
#[derive(Clone)]
pub struct ObservationWord {
    rope: Rope<Symbol>,
}

impl ObservationWord {
    pub fn empty() -> Self {
        Self {
            rope: Rope::empty(),
        }
    }

    /// One stored symbol, regardless of the logical count.
    pub fn uniform(symbol: u64, len: u64) -> Self {
        Self {
            rope: Rope::uniform(Symbol(symbol), len),
        }
    }

    /// Copy actual stored symbols into bounded literal leaves. The slice
    /// length is physical input, never an inferred logical repetition count.
    pub fn from_symbols(symbols: &[u64]) -> Result<Self, WordLengthOverflow> {
        u64::try_from(symbols.len()).map_err(|_| WordLengthOverflow)?;
        let rope = Rope::from_elements(
            symbols
                .iter()
                .map(|&s| Ok::<_, core::convert::Infallible>(Symbol(s))),
        )
        .unwrap_or_else(|never| match never {});
        Ok(Self { rope })
    }

    pub fn len(&self) -> u64 {
        self.rope.len()
    }
    pub fn is_empty(&self) -> bool {
        self.rope.is_empty()
    }

    /// Concatenate while checking the length before entering rope operations.
    pub fn concat(&self, right: &Self) -> Result<Self, WordLengthOverflow> {
        self.len()
            .checked_add(right.len())
            .ok_or(WordLengthOverflow)?;
        Ok(Self {
            rope: self.rope.append(&right.rope),
        })
    }

    pub fn repeat(&self, count: u64) -> Result<Self, WordLengthOverflow> {
        self.len().checked_mul(count).ok_or(WordLengthOverflow)?;
        Ok(Self {
            rope: self.rope.repeat(count),
        })
    }

    /// Exact element-wise comparison under a stable pair predicate on
    /// labels. Shared structures and periodic words use the same memoized
    /// comparison as interpreter arrays. Different periods may require distinct
    /// alignments; this does not promise universal linear time in stored nodes.
    pub fn equivalent_by(&self, right: &Self, mut eq: impl FnMut(u64, u64) -> bool) -> bool {
        self.rope.eq_by(&right.rope, |a, b| eq(a.0, b.0))
    }
}

impl core::fmt::Debug for ObservationWord {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ObservationWord")
            .field("len", &self.len())
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn observation_words_check_all_length_boundaries() {
        let empty = ObservationWord::empty();
        assert!(empty.is_empty());
        assert_eq!(empty.repeat(u64::MAX).unwrap().len(), 0);
        let huge = ObservationWord::uniform(7, u64::MAX);
        assert_eq!(huge.len(), u64::MAX);
        assert_eq!(
            huge.concat(&ObservationWord::uniform(8, 1)).unwrap_err(),
            WordLengthOverflow
        );
        assert_eq!(huge.repeat(2).unwrap_err(), WordLengthOverflow);
        assert_eq!(huge.concat(&empty).unwrap().len(), u64::MAX);
        assert!(ObservationWord::uniform(0, 0).is_empty());
        let mut calls = 0;
        assert!(!huge.equivalent_by(&empty, |_, _| {
            calls += 1;
            true
        }));
        assert_eq!(calls, 0);
    }

    #[test]
    fn observation_words_compare_full_huge_periods_and_late_mismatches() {
        let len = 4 * (u64::MAX / 4);
        let a = ObservationWord::from_symbols(&[0, 1])
            .unwrap()
            .repeat(len / 2)
            .unwrap();
        let b = ObservationWord::from_symbols(&[2, 3, 2, 3])
            .unwrap()
            .repeat(len / 4)
            .unwrap();
        let mut calls = 0;
        assert!(a.equivalent_by(&b, |x, y| {
            calls += 1;
            x % 2 == y % 2
        }));
        assert!(calls <= 16, "period comparison must stay structural");
        let bad = ObservationWord::from_symbols(&[2, 3, 2, 4])
            .unwrap()
            .repeat(len / 4)
            .unwrap();
        assert!(!a.equivalent_by(&bad, |x, y| x % 2 == y % 2));
        let a = ObservationWord::uniform(0, u64::MAX - 1)
            .concat(&ObservationWord::uniform(1, 1))
            .unwrap();
        let b = ObservationWord::uniform(2, u64::MAX - 1)
            .concat(&ObservationWord::uniform(3, 1))
            .unwrap();
        let mut calls = 0;
        assert!(a.equivalent_by(&b, |x, y| {
            calls += 1;
            x % 2 == y % 2
        }));
        assert!(
            calls < 16,
            "uniform windows compare actual stored pairs: {calls}"
        );
        let same = ObservationWord::uniform(0, u64::MAX);
        let mut calls = 0;
        assert!(same.equivalent_by(&a, |x, y| {
            calls += 1;
            x % 2 == y % 2 || y == 1
        }));
        assert!(
            calls < 16,
            "constant pair results ignore repeated extents: {calls}"
        );
        let bad = ObservationWord::uniform(2, u64::MAX - 1)
            .concat(&ObservationWord::uniform(4, 1))
            .unwrap();
        assert!(!a.equivalent_by(&bad, |x, y| x % 2 == y % 2));
    }

    fn phased_word(
        phase: u64,
        len: u64,
        memo: &mut std::collections::HashMap<(u64, u64), ObservationWord>,
    ) -> ObservationWord {
        if let Some(word) = memo.get(&(phase, len)) {
            return word.clone();
        }
        let word = if len <= 16 {
            ObservationWord::from_symbols(
                &(0..len).map(|i| (phase + i) % 3 + 1).collect::<Vec<_>>(),
            )
            .unwrap()
        } else {
            let lower = len / 2;
            let left = phased_word(phase, lower, memo);
            let right = phased_word((phase + lower) % 3, len - lower, memo);
            left.concat(&right).unwrap()
        };
        memo.insert((phase, len), word.clone());
        word
    }

    #[test]
    fn observation_words_compare_shared_dags_against_periods_without_fresh_slices() {
        let unit = ObservationWord::from_symbols(&[1, 2, 3]).unwrap();
        // The small case fails promptly if memo reuse regresses, before the
        // huge case could expand billions of equivalent logical windows.
        for depth in [10, 40] {
            // Odd repeat counts keep canonical half boundaries out of phase.
            // Doubling identical words would normalize straight into Repeat.
            let count = (1 << depth) + 37;
            let shared = phased_word(0, 3 * count, &mut std::collections::HashMap::new());
            let topology = shared.rope.structure();
            let mut incoming = vec![0; topology.nodes.len()];
            let mut concats = 0;
            for node in &topology.nodes {
                use crate::interpret::rope::StructureNode;
                match node {
                    StructureNode::Concat { left, right } => {
                        incoming[*left] += 1;
                        incoming[*right] += 1;
                        concats += 1;
                    }
                    StructureNode::Repeat { unit, .. } => incoming[*unit] += 1,
                    StructureNode::Dense(_) | StructureNode::Uniform { .. } => {}
                }
            }
            assert!(
                concats > 0
                    && topology.nodes.iter().enumerate().any(|(i, node)| {
                        matches!(node, crate::interpret::rope::StructureNode::Concat { .. })
                            && incoming[i] > 1
                    }),
                "fixture must retain shared concat nodes, not only a Repeat"
            );
            assert!(
                topology.nodes.len() < 2048,
                "fixture construction must remain physical"
            );
            let periodic = unit.repeat(count).unwrap();
            let mut calls = 0;
            assert!(shared.equivalent_by(&periodic, |a, b| {
                calls += 1;
                a == b
            }));
            let bound = if depth == 10 { 1024 } else { 8192 };
            assert!(
                calls < bound,
                "the same original windows must be reused: {calls}"
            );
            let changed = unit
                .repeat(count - 1)
                .unwrap()
                .concat(&ObservationWord::from_symbols(&[1, 2, 99]).unwrap())
                .unwrap();
            let mut calls = 0;
            assert!(!shared.equivalent_by(&changed, |a, b| {
                calls += 1;
                a == b
            }));
            assert!(
                calls < 16384,
                "late mismatches must retain shared windows: {calls}"
            );
        }
    }

    #[test]
    fn observation_word_pair_predicates_check_every_distinct_period_alignment() {
        let a = ObservationWord::from_symbols(&[0, 1])
            .unwrap()
            .repeat(3)
            .unwrap();
        let b = ObservationWord::from_symbols(&[2, 3, 4])
            .unwrap()
            .repeat(2)
            .unwrap();
        // Stable pair predicates need not be equivalence relations. The
        // (0,3) pair is beyond the old four-element Fine-Wilf prefix.
        for mask in 0..64 {
            let predicate = |x: u64, y: u64| mask & (1 << (3 * x + y - 2)) != 0;
            let expected = (0..6).all(|i| predicate(i % 2, 2 + i % 3));
            assert_eq!(a.equivalent_by(&b, predicate), expected, "pair mask {mask}");
        }
        assert!(!a.equivalent_by(&a, |_, _| false));
    }

    #[test]
    fn observation_words_match_finite_materialized_reference_across_shapes() {
        for len in 0..=65 {
            let labels = (0..len).map(|n| (n % 3) as u64).collect::<Vec<_>>();
            let dense = ObservationWord::from_symbols(&labels).unwrap();
            let mut pieces = ObservationWord::empty();
            for &label in &labels {
                pieces = pieces
                    .concat(&ObservationWord::uniform(label + 3, 1))
                    .unwrap();
            }
            assert!(dense.equivalent_by(&pieces, |x, y| x % 3 == y % 3));
            if len > 0 {
                let mut changed = labels.clone();
                changed[len - 1] += 1;
                let other = ObservationWord::from_symbols(&changed).unwrap();
                assert_eq!(
                    dense.equivalent_by(&other, |x, y| x % 3 == y % 3),
                    labels.iter().zip(&changed).all(|(x, y)| x % 3 == y % 3)
                );
            }
        }
    }
}
