// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A nested inductive's occurrences by container, argument count and a hash
//! of their arguments (R176). A site, or a new occurrence in phase 1, is
//! compared only with the occurrences whose key it shares, never with every
//! occurrence of its container: an equal leading argument held in another
//! allocation was walked whole before a later one differed, about
//! `m² / 2 × |X|` for `m` occurrences. A key decides nothing: equal argument
//! lists have equal keys, and every candidate is compared exactly, so a
//! collision costs a comparison and is never a refusal.

use std::collections::HashMap;
use std::hash::Hasher;

use super::walk::{narrowed, same_args};
use super::Charge;
use crate::name::Name;
use crate::nested::{NestedError, Occurrence};
use crate::term::Term;

/// The key of an argument list with `arg` appended to one whose key is
/// `key`: [`args_key`] folds this over a list from `0`, so a spine's
/// applications are keyed one argument at a time. The key is [`narrowed`],
/// which outside tests leaves it whole.
pub(crate) fn mix(key: u64, arg: &Term) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    h.write_u64(key);
    h.write_u64(arg.cached_hash());
    narrowed(h.finish())
}

/// The key of an argument list, from its arguments' cached structural
/// hashes: equal lists have equal keys.
pub(crate) fn args_key(args: &[Term]) -> u64 {
    args.iter().fold(0, mix)
}

/// The occurrences found so far, by container (R176).
#[derive(Default)]
pub(crate) struct OccIndex {
    by_container: HashMap<Name, ByContainer>,
}

#[derive(Default)]
struct ByContainer {
    /// The argument counts of the container's occurrences, largest first,
    /// each once.
    arities: Vec<usize>,
    /// Where each occurrence is in the list, by argument count and
    /// [`args_key`], in the order they were found.
    places: HashMap<(usize, u64), Vec<usize>>,
}

impl OccIndex {
    /// The index of `occurrences`, in their order.
    #[cfg(test)]
    pub(crate) fn of(occurrences: &[Occurrence]) -> OccIndex {
        let mut index = OccIndex::default();
        for (place, o) in occurrences.iter().enumerate() {
            index.insert(&o.container, &o.args, place);
        }
        index
    }

    /// Record that the occurrence at `place` is of `container` with `args`.
    pub(crate) fn insert(&mut self, container: &Name, args: &[Term], place: usize) {
        let entry = self.by_container.entry(container.clone()).or_default();
        let arity = args.len();
        // Largest first: an entry larger than `arity` sorts before it.
        if let Err(at) = entry.arities.binary_search_by(|n| arity.cmp(n)) {
            entry.arities.insert(at, arity);
        }
        entry
            .places
            .entry((arity, args_key(args)))
            .or_default()
            .push(place);
    }

    /// The argument counts of `container`'s occurrences, largest first.
    pub(crate) fn arities(&self, container: &Name) -> &[usize] {
        self.by_container
            .get(container)
            .map(|c| c.arities.as_slice())
            .unwrap_or_default()
    }

    /// The first occurrence, in the order found, of `container` with
    /// arguments equal to `args`, whose [`args_key`] is `key`. Only the
    /// occurrences with that key are compared, and each pair of nodes a
    /// comparison looks at is charged before it is looked at.
    pub(crate) fn find<'o>(
        &self,
        occurrences: &'o [Occurrence],
        container: &Name,
        args: &[Term],
        key: u64,
        charge: &mut Charge<'_>,
    ) -> Result<Option<&'o Occurrence>, NestedError> {
        let Some(places) = self
            .by_container
            .get(container)
            .and_then(|c| c.places.get(&(args.len(), key)))
        else {
            return Ok(None);
        };
        for &place in places {
            let Some(occ) = occurrences.get(place) else {
                continue;
            };
            if occ.container != *container || occ.args.len() != args.len() {
                continue;
            }
            if same_args(&occ.args, args, charge)? {
                return Ok(Some(occ));
            }
        }
        Ok(None)
    }
}
