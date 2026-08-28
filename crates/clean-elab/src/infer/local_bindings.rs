// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The elaborator's local-binding stack, with a generation that moves on
//! every mutation.
//!
//! `ElabCtx::shared_local_ctx` memoises the kernel `LocalContext` built from
//! these bindings (plus the metavariable state) and serves the cached context
//! while the generation is unchanged. A stale context would change `whnf` /
//! def-eq answers — a SOUNDNESS bug in the elaborator's view of its own
//! context — so the invalidation has to be total. This type makes it total
//! at compile time rather than by grep: the stack is reachable read-only
//! through `Deref<Target = Vec<_>>`, there is deliberately no `DerefMut`, and
//! every mutating operation is an inherent method that re-mints the
//! generation before it writes. Adding a new way to mutate the stack means
//! adding a method here, where the bump cannot be forgotten.
//!
//! The let-value side table (`let x : T := v` locals whose value is
//! body-visible / zeta-reducible) lives here too, so it is maintained in
//! lock-step with the entries it annotates: popping or truncating an entry
//! drops its value, and the generation covers both.

use crate::state_generation::next_generation;
use clean_kernel::{Expr, FVarId};
use std::collections::HashMap;
use std::ops::Deref;

/// One binding: surface name, the free variable standing for it, its type.
pub(crate) type LocalEntry = (String, FVarId, Expr);

/// Local-binding stack plus let-value side table, generation-stamped.
#[derive(Debug)]
pub(crate) struct LocalBindings {
    entries: Vec<LocalEntry>,
    /// `fvar -> value` for let-bound locals. A local in `entries` that also
    /// appears here is a local DEFINITION (`let x : T := v`), emitted to the
    /// kernel as `push_let_with_id` so WHNF can zeta-reduce `x` to `v`;
    /// opaque hypotheses (`have` / binders) have no entry and stay rigid.
    let_values: HashMap<FVarId, Expr>,
    /// See the module doc and `crate::state_generation`.
    generation: u64,
}

impl LocalBindings {
    pub(crate) fn new() -> Self {
        Self {
            entries: Vec::new(),
            let_values: HashMap::new(),
            generation: next_generation(),
        }
    }

    /// Generation of the current content; equal generations, equal content.
    #[must_use]
    pub(crate) fn generation(&self) -> u64 {
        self.generation
    }

    #[inline]
    fn touch(&mut self) {
        self.generation = next_generation();
    }

    /// Push an opaque binding.
    pub(crate) fn push(&mut self, entry: LocalEntry) {
        self.touch();
        self.entries.push(entry);
    }

    /// Push a let-bound binding whose `value` is body-visible.
    pub(crate) fn push_let(&mut self, entry: LocalEntry, value: Expr) {
        self.touch();
        self.let_values.insert(entry.1, value);
        self.entries.push(entry);
    }

    /// Pop the innermost binding, dropping its let value (if any) in
    /// lock-step so a popped let-local cannot leak its value into a later,
    /// unrelated scope.
    pub(crate) fn pop(&mut self) -> Option<LocalEntry> {
        let entry = self.entries.pop()?;
        self.touch();
        self.let_values.remove(&entry.1);
        Some(entry)
    }

    /// Drop every binding above `len` (and their let values). A no-op when
    /// nothing is above `len`, in which case the generation is kept.
    pub(crate) fn truncate(&mut self, len: usize) {
        if self.entries.len() <= len {
            return;
        }
        self.touch();
        for (_, fvar, _) in self.entries.drain(len..) {
            self.let_values.remove(&fvar);
        }
    }

    /// Keep only the bindings `keep` accepts (auto-implicit take-back), dropping
    /// the let values of the removed ones. A no-op keeps the generation.
    pub(crate) fn retain(&mut self, mut keep: impl FnMut(&LocalEntry) -> bool) {
        let before = self.entries.len();
        let mut removed: Vec<FVarId> = Vec::new();
        self.entries.retain(|entry| {
            let keep_it = keep(entry);
            if !keep_it {
                removed.push(entry.1);
            }
            keep_it
        });
        if self.entries.len() == before {
            return;
        }
        self.touch();
        for fvar in removed {
            self.let_values.remove(&fvar);
        }
    }

    /// The body-visible value of a let-bound local, if `fvar` is one.
    #[must_use]
    pub(crate) fn let_value(&self, fvar: FVarId) -> Option<&Expr> {
        self.let_values.get(&fvar)
    }

    /// The whole let-value side table (for exact scope snapshots).
    #[must_use]
    pub(crate) fn let_values(&self) -> &HashMap<FVarId, Expr> {
        &self.let_values
    }

    /// Replace the entire content from a snapshot taken with
    /// `(self.clone(), self.let_values().clone())`.
    pub(crate) fn restore(&mut self, entries: Vec<LocalEntry>, let_values: HashMap<FVarId, Expr>) {
        self.touch();
        self.entries = entries;
        self.let_values = let_values;
    }
}

/// Read-only view of the stack. There is intentionally no `DerefMut`.
impl Deref for LocalBindings {
    type Target = Vec<LocalEntry>;

    fn deref(&self) -> &Self::Target {
        &self.entries
    }
}

impl<'a> IntoIterator for &'a LocalBindings {
    type Item = &'a LocalEntry;
    type IntoIter = std::slice::Iter<'a, LocalEntry>;

    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter()
    }
}

/// Lets tests compare the live stack against a `Vec` snapshot.
impl PartialEq<Vec<LocalEntry>> for LocalBindings {
    fn eq(&self, other: &Vec<LocalEntry>) -> bool {
        &self.entries == other
    }
}

#[cfg(test)]
mod tests {
    use super::LocalBindings;
    use clean_kernel::{Expr, FVarId};

    fn entry(i: u64) -> (String, FVarId, Expr) {
        (format!("x{i}"), FVarId::new(i), Expr::prop())
    }

    #[test]
    fn test_every_mutation_moves_the_generation_and_reads_do_not() {
        let mut b = LocalBindings::new();
        let g0 = b.generation();
        assert_eq!(b.len(), 0);
        assert_eq!(b.generation(), g0, "reads keep the generation");

        b.push(entry(0));
        let g1 = b.generation();
        assert_ne!(g1, g0);

        b.push_let(entry(1), Expr::type_());
        let g2 = b.generation();
        assert_ne!(g2, g1);
        assert!(b.let_value(FVarId::new(1)).is_some());

        assert!(b.pop().is_some());
        let g3 = b.generation();
        assert_ne!(g3, g2);
        assert!(
            b.let_value(FVarId::new(1)).is_none(),
            "pop drops the let value in lock-step"
        );

        b.truncate(5);
        assert_eq!(b.generation(), g3, "a no-op truncate keeps the generation");
        b.push_let(entry(2), Expr::type_());
        b.push(entry(3));
        b.truncate(1);
        assert_ne!(b.generation(), g3);
        assert_eq!(b.len(), 1);
        assert!(b.let_value(FVarId::new(2)).is_none());

        b.push_let(entry(7), Expr::type_());
        let g_retain = b.generation();
        b.retain(|_| true);
        assert_eq!(
            b.generation(),
            g_retain,
            "a no-op retain keeps the generation"
        );
        b.retain(|(_, fvar, _)| *fvar != FVarId::new(7));
        assert_ne!(b.generation(), g_retain);
        assert!(
            b.let_value(FVarId::new(7)).is_none(),
            "retain drops let values"
        );

        let snapshot = (b.clone(), b.let_values().clone());
        let g4 = b.generation();
        b.restore(snapshot.0, snapshot.1);
        assert_ne!(
            b.generation(),
            g4,
            "restoring even identical content mints a fresh generation"
        );
    }
}
