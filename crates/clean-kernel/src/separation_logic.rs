// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared separation-logic abstractions for semantics crates.
//!
//! The kernel already exposes shared address and memory-value wrappers via
//! [`crate::sem_memory_model`]. This module layers a small separation-logic
//! vocabulary on top of those wrappers without committing to any concrete
//! operational memory model.
//!
//! `Pure(Expr)` and `Wand` require extra logical context beyond a concrete heap:
//! - pure propositions need an external logical evaluator
//! - magic wand quantifies over possible disjoint heap extensions
//!
//! The default [`satisfies`] checker therefore stays conservative:
//! - `Pure(_)` is treated as opaque / false
//! - `Wand` is checked only against the empty extension
//!
//! Callers that need richer reasoning can use [`satisfies_with`] or
//! [`satisfies_with_extensions`].

use crate::expr::Expr;
use crate::sem_memory_model::{Address, MemoryValue};
use std::collections::HashMap;
use std::hash::Hash;

/// Separation-logic expressions over abstract addresses and values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SepExpr<A = Address, V = MemoryValue> {
    /// Empty heap predicate.
    Emp,
    /// Singleton heap predicate `addr |-> val`.
    PointsTo { addr: A, val: V },
    /// Separating conjunction.
    Star(Box<Self>, Box<Self>),
    /// Magic wand / separating implication.
    Wand(Box<Self>, Box<Self>),
    /// Pure proposition that does not consume heap resources.
    Pure(Expr),
}

impl<A, V> SepExpr<A, V> {
    /// Build a singleton points-to predicate.
    pub fn points_to(addr: A, val: V) -> Self {
        Self::PointsTo { addr, val }
    }

    /// Build a separating conjunction.
    pub fn star(left: Self, right: Self) -> Self {
        Self::Star(Box::new(left), Box::new(right))
    }

    /// Build a separating implication.
    pub fn wand(left: Self, right: Self) -> Self {
        Self::Wand(Box::new(left), Box::new(right))
    }
}

/// Concrete finite heap used by the logical checker.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SepHeap<A: Eq + Hash = Address, V = MemoryValue> {
    cells: HashMap<A, V>,
}

impl<A, V> SepHeap<A, V>
where
    A: Eq + Hash,
{
    /// Construct an empty heap.
    pub fn new() -> Self {
        Self {
            cells: HashMap::new(),
        }
    }

    /// Insert or overwrite a heap cell.
    pub fn insert(&mut self, addr: A, val: V) -> Option<V> {
        self.cells.insert(addr, val)
    }

    /// Read a heap cell.
    pub fn get(&self, addr: &A) -> Option<&V> {
        self.cells.get(addr)
    }

    /// Remove a heap cell.
    pub fn remove(&mut self, addr: &A) -> Option<V> {
        self.cells.remove(addr)
    }

    /// Return whether the heap is empty.
    pub fn is_empty(&self) -> bool {
        self.cells.is_empty()
    }

    /// Return the number of heap cells.
    pub fn len(&self) -> usize {
        self.cells.len()
    }

    /// Iterate over all heap cells.
    pub fn iter(&self) -> impl Iterator<Item = (&A, &V)> {
        self.cells.iter()
    }

    /// Return whether two heaps are address-disjoint.
    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.cells
            .keys()
            .all(|addr| !other.cells.contains_key(addr))
    }
}

impl<A, V> SepHeap<A, V>
where
    A: Clone + Eq + Hash,
    V: Clone,
{
    /// Build a singleton heap.
    pub fn singleton(addr: A, val: V) -> Self {
        let mut heap = Self::new();
        heap.insert(addr, val);
        heap
    }

    /// Snapshot the heap entries for finite search procedures.
    fn entries(&self) -> Vec<(A, V)> {
        self.cells
            .iter()
            .map(|(addr, val)| (addr.clone(), val.clone()))
            .collect()
    }

    /// Union two disjoint heaps.
    pub fn union(&self, other: &Self) -> Option<Self> {
        if !self.is_disjoint(other) {
            return None;
        }

        let mut cells = self.cells.clone();
        cells.extend(
            other
                .cells
                .iter()
                .map(|(addr, val)| (addr.clone(), val.clone())),
        );
        Some(Self { cells })
    }
}

impl<A, V> FromIterator<(A, V)> for SepHeap<A, V>
where
    A: Eq + Hash,
{
    fn from_iter<T: IntoIterator<Item = (A, V)>>(iter: T) -> Self {
        Self {
            cells: iter.into_iter().collect(),
        }
    }
}

/// Conservative satisfaction checker for the shared logical layer.
///
/// This treats pure propositions as opaque and only checks `Wand` against the
/// empty extension. Use [`satisfies_with`] or [`satisfies_with_extensions`] for
/// richer semantics.
pub fn satisfies<A, V>(heap: &SepHeap<A, V>, expr: &SepExpr<A, V>) -> bool
where
    A: Clone + Eq + Hash,
    V: Clone + Eq,
{
    satisfies_with_extensions(heap, expr, &|_| false, &[SepHeap::new()])
}

/// Satisfaction checker with caller-supplied interpretation for `Pure`.
///
/// `Wand` is still checked only against the empty extension; use
/// [`satisfies_with_extensions`] to quantify over additional candidate heaps.
pub fn satisfies_with<A, V, F>(heap: &SepHeap<A, V>, expr: &SepExpr<A, V>, pure_eval: &F) -> bool
where
    A: Clone + Eq + Hash,
    V: Clone + Eq,
    F: Fn(&Expr) -> bool,
{
    satisfies_with_extensions(heap, expr, pure_eval, &[SepHeap::new()])
}

/// Satisfaction checker with caller-supplied interpretations for both `Pure`
/// and `Wand`.
///
/// `extensions` is a finite set of candidate disjoint heaps used when checking
/// `Wand(P, Q)`: every disjoint candidate heap that satisfies `P` must make the
/// union heap satisfy `Q`.
pub fn satisfies_with_extensions<A, V, F>(
    heap: &SepHeap<A, V>,
    expr: &SepExpr<A, V>,
    pure_eval: &F,
    extensions: &[SepHeap<A, V>],
) -> bool
where
    A: Clone + Eq + Hash,
    V: Clone + Eq,
    F: Fn(&Expr) -> bool,
{
    match expr {
        SepExpr::Emp => heap.is_empty(),
        SepExpr::PointsTo { addr, val } => heap.len() == 1 && heap.get(addr) == Some(val),
        SepExpr::Star(left, right) => exists_heap_split(heap, &mut |left_heap, right_heap| {
            satisfies_with_extensions(left_heap, left, pure_eval, extensions)
                && satisfies_with_extensions(right_heap, right, pure_eval, extensions)
        }),
        SepExpr::Wand(left, right) => extensions.iter().all(|extension| {
            if !heap.is_disjoint(extension) {
                return true;
            }

            if !satisfies_with_extensions(extension, left, pure_eval, extensions) {
                return true;
            }

            heap.union(extension)
                .map(|combined| satisfies_with_extensions(&combined, right, pure_eval, extensions))
                .unwrap_or(false)
        }),
        SepExpr::Pure(prop) => pure_eval(prop),
    }
}

/// Check the standard frame-rule shape with conservative logical semantics.
///
/// If the framed precondition does not hold on `initial_heap`, the implication
/// is vacuously true. Otherwise the checker searches for:
/// - a split of `initial_heap` into `pre_heap` and `frame_before`
/// - a split of `result_heap` into `post_heap` and `frame_after`
/// - `pre_heap |= pre`, `frame_before |= frame`, `post_heap |= post`,
///   and `frame_after |= frame`
/// - `cmd_preserves_frame(frame_before, frame_after)`
pub fn check_frame_rule<A, V, F>(
    initial_heap: &SepHeap<A, V>,
    result_heap: &SepHeap<A, V>,
    pre: &SepExpr<A, V>,
    post: &SepExpr<A, V>,
    frame: &SepExpr<A, V>,
    cmd_preserves_frame: F,
) -> bool
where
    A: Clone + Eq + Hash,
    V: Clone + Eq,
    F: Fn(&SepHeap<A, V>, &SepHeap<A, V>) -> bool,
{
    check_frame_rule_with(
        initial_heap,
        result_heap,
        pre,
        post,
        frame,
        &|_| false,
        cmd_preserves_frame,
    )
}

/// Frame-rule checker with caller-supplied interpretation for `Pure`.
pub fn check_frame_rule_with<A, V, P, F>(
    initial_heap: &SepHeap<A, V>,
    result_heap: &SepHeap<A, V>,
    pre: &SepExpr<A, V>,
    post: &SepExpr<A, V>,
    frame: &SepExpr<A, V>,
    pure_eval: &P,
    cmd_preserves_frame: F,
) -> bool
where
    A: Clone + Eq + Hash,
    V: Clone + Eq,
    P: Fn(&Expr) -> bool,
    F: Fn(&SepHeap<A, V>, &SepHeap<A, V>) -> bool,
{
    let mut has_framed_pre = false;
    let holds = exists_heap_split(initial_heap, &mut |pre_heap, frame_before| {
        if !satisfies_with(pre_heap, pre, pure_eval)
            || !satisfies_with(frame_before, frame, pure_eval)
        {
            return false;
        }

        has_framed_pre = true;
        exists_heap_split(result_heap, &mut |post_heap, frame_after| {
            satisfies_with(post_heap, post, pure_eval)
                && satisfies_with(frame_after, frame, pure_eval)
                && cmd_preserves_frame(frame_before, frame_after)
        })
    });

    holds || !has_framed_pre
}

/// Small proof-term language for separation-logic derivations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SepLogicProof<A = Address, V = MemoryValue> {
    /// Assumed proposition.
    Assume(SepExpr<A, V>),
    /// Proof of `emp`.
    EmpIntro,
    /// Proof of a singleton heap predicate.
    PointsToIntro { addr: A, val: V },
    /// Proof of `P * Q` from proofs of `P` and `Q`.
    StarIntro { left: Box<Self>, right: Box<Self> },
    /// Proof of `P -* Q`.
    WandIntro {
        premise: SepExpr<A, V>,
        proof: Box<Self>,
    },
    /// Frame-rule application.
    Frame {
        frame: SepExpr<A, V>,
        proof: Box<Self>,
    },
    /// Proof of a pure proposition.
    PureIntro(Expr),
}

fn exists_heap_split<A, V, F>(heap: &SepHeap<A, V>, predicate: &mut F) -> bool
where
    A: Clone + Eq + Hash,
    V: Clone,
    F: FnMut(&SepHeap<A, V>, &SepHeap<A, V>) -> bool,
{
    fn go<A, V, F>(
        entries: &[(A, V)],
        idx: usize,
        left: &mut SepHeap<A, V>,
        right: &mut SepHeap<A, V>,
        predicate: &mut F,
    ) -> bool
    where
        A: Clone + Eq + Hash,
        V: Clone,
        F: FnMut(&SepHeap<A, V>, &SepHeap<A, V>) -> bool,
    {
        if idx == entries.len() {
            return predicate(left, right);
        }

        let (addr, val) = &entries[idx];

        left.insert(addr.clone(), val.clone());
        if go(entries, idx + 1, left, right, predicate) {
            return true;
        }
        left.remove(addr);

        right.insert(addr.clone(), val.clone());
        if go(entries, idx + 1, left, right, predicate) {
            return true;
        }
        right.remove(addr);

        false
    }

    let entries = heap.entries();
    let mut left = SepHeap::new();
    let mut right = SepHeap::new();
    go(&entries, 0, &mut left, &mut right, predicate)
}

#[cfg(test)]
mod tests {
    use super::{check_frame_rule, satisfies, SepExpr, SepHeap};
    use crate::sem_memory_model::{Address, MemoryValue};

    #[test]
    fn emp_satisfies_empty_heap() {
        let heap = SepHeap::<Address, MemoryValue>::new();
        assert!(satisfies(&heap, &SepExpr::Emp));
    }

    #[test]
    fn points_to_satisfies_singleton_heap() {
        let heap = SepHeap::from_iter([(Address::new(1), MemoryValue::new(7))]);
        let expr = SepExpr::points_to(Address::new(1), MemoryValue::new(7));

        assert!(satisfies(&heap, &expr));
    }

    #[test]
    fn star_splits_heap_into_disjoint_subheaps() {
        let heap = SepHeap::from_iter([
            (Address::new(1), MemoryValue::new(7)),
            (Address::new(2), MemoryValue::new(9)),
        ]);
        let expr = SepExpr::star(
            SepExpr::points_to(Address::new(1), MemoryValue::new(7)),
            SepExpr::points_to(Address::new(2), MemoryValue::new(9)),
        );

        assert!(satisfies(&heap, &expr));
    }

    #[test]
    fn frame_rule_holds_when_command_preserves_frame() {
        let initial_heap = SepHeap::from_iter([
            (Address::new(1), MemoryValue::new(10)),
            (Address::new(2), MemoryValue::new(20)),
        ]);
        let result_heap = SepHeap::from_iter([
            (Address::new(1), MemoryValue::new(11)),
            (Address::new(2), MemoryValue::new(20)),
        ]);
        let pre = SepExpr::points_to(Address::new(1), MemoryValue::new(10));
        let post = SepExpr::points_to(Address::new(1), MemoryValue::new(11));
        let frame = SepExpr::points_to(Address::new(2), MemoryValue::new(20));

        assert!(check_frame_rule(
            &initial_heap,
            &result_heap,
            &pre,
            &post,
            &frame,
            |frame_before, frame_after| frame_before == frame_after,
        ));
    }
}
