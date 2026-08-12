// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Append-only, interior-mutability map handing out STABLE `&V` references.
//
// VENDORED (not depended-on) from `elsa` (Apache-2.0 / MIT,
// https://github.com/Manishearth/elsa), reduced to the minimal `insert`/`get`/
// `contains_key` the lazy `ConstantSource` needs. Operator decision 2026-06-25:
// the trust-critical zero-copy loading path carries NO external supply chain, so
// the one `unsafe` block lives here in `clean-mathverse` (which already uses
// `unsafe` for `memmap2`) and is auditable in-tree — `clean-kernel` stays
// `#![forbid(unsafe_code)]` and dependency-free, gaining only a pure-safe trait.

use std::collections::HashMap;
use std::hash::Hash;
use std::sync::Mutex;

/// An append-only map with interior mutability that returns `&V` references valid
/// for the lifetime of `&self`.
///
/// This is the primitive behind lazy constant materialization: `get_const` returns
/// `&ConstantInfo` and has thousands of call sites, so the lazy tier must hand out
/// borrows (not clones) through a shared `&self`. A plain `Mutex<HashMap<..>>`
/// cannot — its guard's borrow ends with the lock. `FrozenMap` boxes each value so
/// its heap address is fixed, and never removes or replaces an entry, so a `&V`
/// taken from an entry already in the map stays valid for `&self`.
///
/// # Soundness invariants (the `unsafe` in `get`/`insert` relies on BOTH)
/// 1. **APPEND-ONLY**: an inserted key is never removed, and its value is never
///    overwritten (`insert` keeps the first value on a duplicate key).
/// 2. **BOXED VALUES**: each `V` lives behind its own `Box`, so `HashMap`
///    rehashing moves the `Box` *pointer* but never the pointed-to `V`.
///
/// Together: a `*const V` read from an entry stays valid as long as `&self` lives
/// (the `V` is never moved or dropped), and no `&mut V` is ever exposed, so the
/// shared `&V` cannot alias a mutable borrow. The `Mutex` serializes the `HashMap`
/// structural mutations; the returned `&V` points at the stable boxed target,
/// outside the structure the lock protects.
#[derive(Debug, Default)]
pub(crate) struct FrozenMap<K, V> {
    map: Mutex<HashMap<K, Box<V>>>,
}

impl<K: Eq + Hash, V> FrozenMap<K, V> {
    pub(crate) fn new() -> Self {
        Self {
            map: Mutex::new(HashMap::new()),
        }
    }

    /// Stable reference to the value for `key`, if present.
    pub(crate) fn get(&self, key: &K) -> Option<&V> {
        let guard = self
            .map
            .lock()
            .expect("invariant: FrozenMap mutex poisoned");
        let ptr = guard.get(key).map(|boxed| &**boxed as *const V);
        drop(guard);
        // SAFETY: append-only + boxed values (see type docs) ⇒ the `V` behind `ptr`
        // is never moved or dropped while `&self` lives, so extending the borrow to
        // `&self`'s lifetime is sound. The lock is dropped before the deref; no
        // `&mut V` is ever produced, so the shared `&V` cannot alias.
        ptr.map(|p| unsafe { &*p })
    }

    /// Insert `value` for `key` if absent; return a stable reference to the stored
    /// value. On a duplicate key the existing value is kept (append-only) and
    /// `value` is dropped — the returned reference is to the pre-existing value.
    pub(crate) fn insert(&self, key: K, value: V) -> &V {
        let mut guard = self
            .map
            .lock()
            .expect("invariant: FrozenMap mutex poisoned");
        let ptr = &**guard.entry(key).or_insert_with(|| Box::new(value)) as *const V;
        drop(guard);
        // SAFETY: identical argument to `get` — append-only + boxed ⇒ the target is
        // stable for `&self`, and no `&mut V` escapes.
        unsafe { &*ptr }
    }

    #[cfg(test)]
    pub(crate) fn contains_key(&self, key: &K) -> bool {
        self.map
            .lock()
            .expect("invariant: FrozenMap mutex poisoned")
            .contains_key(key)
    }

    pub(crate) fn len(&self) -> usize {
        self.map
            .lock()
            .expect("invariant: FrozenMap mutex poisoned")
            .len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_then_get() {
        let m: FrozenMap<u32, String> = FrozenMap::new();
        assert_eq!(m.insert(1, "one".to_owned()), "one");
        assert_eq!(m.get(&1).map(String::as_str), Some("one"));
        assert_eq!(m.get(&2), None);
        assert!(m.contains_key(&1));
        assert_eq!(m.len(), 1);
    }

    #[test]
    fn duplicate_key_keeps_first_value() {
        let m: FrozenMap<u32, String> = FrozenMap::new();
        let first = m.insert(7, "first".to_owned());
        assert_eq!(first, "first");
        // Append-only: second insert of the same key returns the FIRST value.
        assert_eq!(m.insert(7, "second".to_owned()), "first");
        assert_eq!(m.get(&7).map(String::as_str), Some("first"));
        assert_eq!(m.len(), 1);
    }

    /// THE soundness property: a `&V` handed out stays valid and unchanged (same
    /// address) across many subsequent inserts that force `HashMap` rehashing —
    /// exactly what the lazy `ConstantSource` relies on when it returns
    /// `&ConstantInfo` borrows from a shared `&self`.
    #[test]
    fn refs_stay_valid_across_rehashing_inserts() {
        let m: FrozenMap<u32, String> = FrozenMap::new();
        let first: &String = m.insert(1, "one".to_owned());
        let first_addr = first as *const String;
        // Force growth/rehash while holding `first` (all shared &self borrows).
        for i in 2..2000 {
            let _ = m.insert(i, format!("v{i}"));
        }
        assert_eq!(first, "one"); // value intact
        assert_eq!(first as *const String, first_addr); // address stable
        assert_eq!(m.get(&1).map(String::as_str), Some("one"));
        assert_eq!(m.get(&1999).map(String::as_str), Some("v1999"));
        assert_eq!(m.len(), 1999);
    }
}
