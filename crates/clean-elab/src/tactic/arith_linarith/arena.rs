// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arena-backed storage for linarith coefficient combinations.

use std::collections::{BTreeMap, BTreeSet};

use super::super::arithmetic::LinearExpr;

/// Stable slot id for an arena-allocated linear combination.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ArenaId(u32);

impl ArenaId {
    const EMPTY_RAW: u32 = 0;

    pub(crate) const EMPTY: Self = Self(Self::EMPTY_RAW);

    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy)]
struct ArenaSlot {
    start: usize,
    len: usize,
}

impl ArenaSlot {
    const EMPTY: Self = Self { start: 0, len: 0 };

    fn end(self) -> usize {
        self.start + self.len
    }
}

/// Append-only coefficient storage plus reusable slot ids.
#[derive(Debug)]
pub(crate) struct ArenaAllocator {
    entries: Vec<(usize, i128)>,
    slots: Vec<Option<ArenaSlot>>,
    free: Vec<ArenaId>,
    scratch: Vec<(usize, i128)>,
}

impl ArenaAllocator {
    pub(crate) fn new() -> Self {
        Self {
            entries: Vec::new(),
            slots: vec![Some(ArenaSlot::EMPTY)],
            free: Vec::new(),
            scratch: Vec::new(),
        }
    }

    fn slot(&self, id: ArenaId) -> Option<ArenaSlot> {
        self.slots.get(id.index()).copied().flatten()
    }

    fn live_slot(&self, id: ArenaId) -> ArenaSlot {
        self.slot(id).expect("arena id must reference a live slot")
    }

    fn alloc_slot(&mut self, slot: ArenaSlot) -> ArenaId {
        if let Some(id) = self.free.pop() {
            self.slots[id.index()] = Some(slot);
            id
        } else {
            let id =
                ArenaId(u32::try_from(self.slots.len()).expect("linarith arena exceeded u32 ids"));
            self.slots.push(Some(slot));
            id
        }
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn contains(&self, id: ArenaId) -> bool {
        self.slot(id).is_some()
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn live_len(&self) -> usize {
        self.slots.iter().flatten().count().saturating_sub(1)
    }

    pub(crate) fn coeffs(&self, id: ArenaId) -> Option<&[(usize, i128)]> {
        let slot = self.slot(id)?;
        Some(&self.entries[slot.start..slot.end()])
    }

    fn coeffs_live(&self, id: ArenaId) -> &[(usize, i128)] {
        self.coeffs(id)
            .expect("arena id must reference a live slot")
    }

    pub(crate) fn alloc_from_slice(&mut self, coeffs: &[(usize, i128)]) -> ArenaId {
        if coeffs.is_empty() {
            return ArenaId::EMPTY;
        }

        let start = self.entries.len();
        self.entries.extend_from_slice(coeffs);
        self.alloc_slot(ArenaSlot {
            start,
            len: coeffs.len(),
        })
    }

    pub(crate) fn alloc_from_iter<I>(&mut self, coeffs: I) -> ArenaId
    where
        I: IntoIterator<Item = (usize, i128)>,
    {
        let start = self.entries.len();
        for (var, coeff) in coeffs {
            if coeff != 0 {
                self.entries.push((var, coeff));
            }
        }
        if self.entries.len() == start {
            ArenaId::EMPTY
        } else {
            self.alloc_slot(ArenaSlot {
                start,
                len: self.entries.len() - start,
            })
        }
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn dealloc(&mut self, id: ArenaId) -> bool {
        if id == ArenaId::EMPTY {
            return false;
        }

        let Some(slot) = self.slots.get_mut(id.index()) else {
            return false;
        };
        if slot.take().is_some() {
            self.free.push(id);
            true
        } else {
            false
        }
    }

    fn scale(&mut self, id: ArenaId, factor: i128) -> Option<ArenaId> {
        if factor == 0 || self.live_slot(id).len == 0 {
            return Some(ArenaId::EMPTY);
        }
        if factor == 1 {
            return Some(id);
        }

        let mut scratch = std::mem::take(&mut self.scratch);
        scratch.clear();
        scratch.reserve(self.live_slot(id).len);

        let ok = {
            let coeffs = self.coeffs_live(id);
            let mut ok = true;
            for &(var, coeff) in coeffs {
                match coeff.checked_mul(factor) {
                    Some(0) => {}
                    Some(new_coeff) => scratch.push((var, new_coeff)),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            ok
        };

        let result = ok.then(|| self.alloc_from_slice(&scratch));
        scratch.clear();
        self.scratch = scratch;
        result
    }

    fn add(&mut self, lhs: ArenaId, rhs: ArenaId) -> Option<ArenaId> {
        if self.live_slot(lhs).len == 0 {
            return Some(rhs);
        }
        if self.live_slot(rhs).len == 0 {
            return Some(lhs);
        }

        let mut scratch = std::mem::take(&mut self.scratch);
        scratch.clear();
        scratch.reserve(
            self.live_slot(lhs)
                .len
                .saturating_add(self.live_slot(rhs).len),
        );

        let ok = {
            let lhs_coeffs = self.coeffs_live(lhs);
            let rhs_coeffs = self.coeffs_live(rhs);
            let mut li = 0;
            let mut ri = 0;
            let mut ok = true;

            while li < lhs_coeffs.len() || ri < rhs_coeffs.len() {
                match (lhs_coeffs.get(li), rhs_coeffs.get(ri)) {
                    (Some(&(lhs_var, lhs_coeff)), Some(&(rhs_var, rhs_coeff))) => {
                        if lhs_var == rhs_var {
                            match lhs_coeff.checked_add(rhs_coeff) {
                                Some(0) => {}
                                Some(sum) => scratch.push((lhs_var, sum)),
                                None => {
                                    ok = false;
                                    break;
                                }
                            }
                            li += 1;
                            ri += 1;
                        } else if lhs_var < rhs_var {
                            scratch.push((lhs_var, lhs_coeff));
                            li += 1;
                        } else {
                            scratch.push((rhs_var, rhs_coeff));
                            ri += 1;
                        }
                    }
                    (Some(&(lhs_var, lhs_coeff)), None) => {
                        scratch.push((lhs_var, lhs_coeff));
                        li += 1;
                    }
                    (None, Some(&(rhs_var, rhs_coeff))) => {
                        scratch.push((rhs_var, rhs_coeff));
                        ri += 1;
                    }
                    (None, None) => break,
                }
            }

            ok
        };

        let result = ok.then(|| self.alloc_from_slice(&scratch));
        scratch.clear();
        self.scratch = scratch;
        result
    }

    fn without_var(&mut self, id: ArenaId, var: usize) -> ArenaId {
        let (pos, len) = {
            let coeffs = self.coeffs_live(id);
            let Ok(pos) = coeffs.binary_search_by_key(&var, |&(candidate, _)| candidate) else {
                return id;
            };
            (pos, coeffs.len())
        };

        let mut scratch = std::mem::take(&mut self.scratch);
        scratch.clear();
        scratch.reserve(len.saturating_sub(1));
        {
            let coeffs = self.coeffs_live(id);
            scratch.extend_from_slice(&coeffs[..pos]);
            scratch.extend_from_slice(&coeffs[pos + 1..]);
        }

        let result = self.alloc_from_slice(&scratch);
        scratch.clear();
        self.scratch = scratch;
        result
    }

    fn coeff(&self, id: ArenaId, var: usize) -> i128 {
        self.coeffs_live(id)
            .binary_search_by_key(&var, |&(candidate, _)| candidate)
            .ok()
            .map(|idx| self.coeffs_live(id)[idx].1)
            .unwrap_or(0)
    }

    fn extend_variables(&self, id: ArenaId, vars: &mut BTreeSet<usize>) {
        vars.extend(self.coeffs_live(id).iter().map(|&(var, _)| var));
    }
}

impl Default for ArenaAllocator {
    fn default() -> Self {
        Self::new()
    }
}

/// Arena-backed wide linear expression for certified FM.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ArenaLinearCombo {
    pub(crate) constant: i128,
    coeffs: ArenaId,
}

impl ArenaLinearCombo {
    pub(crate) fn constant(c: i128) -> Self {
        Self {
            constant: c,
            coeffs: ArenaId::EMPTY,
        }
    }

    pub(crate) fn from_linear_expr(expr: &LinearExpr, arena: &mut ArenaAllocator) -> Self {
        Self {
            constant: i128::from(expr.constant),
            coeffs: arena.alloc_from_iter(
                expr.coeffs
                    .iter()
                    .map(|&(var, coeff)| (var, i128::from(coeff))),
            ),
        }
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn arena_id(&self) -> ArenaId {
        self.coeffs
    }

    pub(crate) fn scale(&self, arena: &mut ArenaAllocator, factor: i128) -> Option<Self> {
        if factor == 0 {
            return Some(Self::constant(0));
        }

        Some(Self {
            constant: self.constant.checked_mul(factor)?,
            coeffs: arena.scale(self.coeffs, factor)?,
        })
    }

    pub(crate) fn add(&self, other: &Self, arena: &mut ArenaAllocator) -> Option<Self> {
        Some(Self {
            constant: self.constant.checked_add(other.constant)?,
            coeffs: arena.add(self.coeffs, other.coeffs)?,
        })
    }

    pub(crate) fn without_var(&self, arena: &mut ArenaAllocator, var: usize) -> Self {
        Self {
            constant: self.constant,
            coeffs: arena.without_var(self.coeffs, var),
        }
    }

    pub(crate) fn coeff(&self, arena: &ArenaAllocator, var: usize) -> i128 {
        arena.coeff(self.coeffs, var)
    }

    pub(crate) fn is_constant(&self) -> bool {
        self.coeffs == ArenaId::EMPTY
    }

    pub(crate) fn extend_variables(&self, arena: &ArenaAllocator, vars: &mut BTreeSet<usize>) {
        arena.extend_variables(self.coeffs, vars);
    }
}

#[cfg_attr(not(test), allow(dead_code))]
/// Snapshot of equivalent arena and `BTreeMap` lookup sequences.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ArenaBenchmarkComparison {
    pub(crate) arena_slot: ArenaId,
    pub(crate) arena_entries: Vec<(usize, i128)>,
    pub(crate) map_entries: Vec<(usize, i128)>,
    pub(crate) lookups: Vec<(usize, i128, i128)>,
}

impl ArenaBenchmarkComparison {
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn from_queries<I>(
        combo: &ArenaLinearCombo,
        arena: &ArenaAllocator,
        map: &BTreeMap<usize, i128>,
        queries: I,
    ) -> Self
    where
        I: IntoIterator<Item = usize>,
    {
        Self {
            arena_slot: combo.arena_id(),
            arena_entries: arena.coeffs_live(combo.arena_id()).to_vec(),
            map_entries: map.iter().map(|(&var, &coeff)| (var, coeff)).collect(),
            lookups: queries
                .into_iter()
                .map(|var| (var, combo.coeff(arena, var), *map.get(&var).unwrap_or(&0)))
                .collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expr_with_coeffs(constant: i64, coeffs: &[(usize, i64)]) -> LinearExpr {
        LinearExpr::from_coeffs(constant, coeffs.iter().copied())
    }

    #[test]
    fn test_linarith_arena_alloc_dealloc_and_lookup() {
        let mut arena = ArenaAllocator::new();
        let first = arena.alloc_from_slice(&[(1, 2), (4, -3)]);
        let second = arena.alloc_from_iter([(0, 7)]);

        assert_eq!(arena.coeffs(first), Some(&[(1, 2), (4, -3)][..]));
        assert_eq!(arena.coeffs(second), Some(&[(0, 7)][..]));
        assert_eq!(arena.live_len(), 2);

        assert!(arena.dealloc(first));
        assert_eq!(arena.coeffs(first), None);
        assert!(!arena.contains(first));
        assert!(!arena.dealloc(ArenaId::EMPTY));

        let reused = arena.alloc_from_slice(&[(9, 1)]);
        assert_eq!(reused, first);
        assert_eq!(arena.coeffs(reused), Some(&[(9, 1)][..]));
    }

    #[test]
    fn test_linarith_arena_linear_combo_ops() {
        let mut arena = ArenaAllocator::new();
        let lhs = ArenaLinearCombo::from_linear_expr(
            &expr_with_coeffs(3, &[(0, 2), (2, -1)]),
            &mut arena,
        );
        let rhs = ArenaLinearCombo::from_linear_expr(
            &expr_with_coeffs(-1, &[(1, 5), (2, 1)]),
            &mut arena,
        );

        let sum = lhs
            .add(&rhs, &mut arena)
            .expect("arena coefficient merge should not overflow");
        assert_eq!(sum.constant, 2);
        assert_eq!(sum.coeff(&arena, 0), 2);
        assert_eq!(sum.coeff(&arena, 1), 5);
        assert_eq!(sum.coeff(&arena, 2), 0);

        let scaled = sum
            .scale(&mut arena, -2)
            .expect("arena coefficient scaling should not overflow");
        assert_eq!(scaled.constant, -4);
        assert_eq!(scaled.coeff(&arena, 0), -4);
        assert_eq!(scaled.coeff(&arena, 1), -10);

        let stripped = scaled.without_var(&mut arena, 1).without_var(&mut arena, 0);
        assert!(stripped.is_constant());
        assert_eq!(stripped.coeff(&arena, 1), 0);
    }

    #[test]
    fn test_linarith_arena_benchmark_comparison_matches_btreemap() {
        let expr = expr_with_coeffs(5, &[(0, 3), (2, -4)]);
        let mut arena = ArenaAllocator::new();
        let combo = ArenaLinearCombo::from_linear_expr(&expr, &mut arena);
        let map: BTreeMap<usize, i128> = expr
            .coeffs
            .iter()
            .map(|&(var, coeff)| (var, i128::from(coeff)))
            .collect();

        let comparison = ArenaBenchmarkComparison::from_queries(&combo, &arena, &map, [0, 1, 2, 4]);
        assert_eq!(comparison.arena_entries, comparison.map_entries);
        assert_eq!(
            comparison.lookups,
            vec![(0, 3, 3), (1, 0, 0), (2, -4, -4), (4, 0, 0)]
        );
        assert_ne!(comparison.arena_slot, ArenaId::EMPTY);
    }
}
