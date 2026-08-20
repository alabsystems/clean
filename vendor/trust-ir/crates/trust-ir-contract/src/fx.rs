// Deterministic hash collections (rustc-hash) for the contract types.
//
// Mirrors `trust_types::fx` for the subset this crate needs (FxHashMap /
// FxHashSet). Within the Trust workspace the `[patch] rustc-hash ->
// tla-hash-fx` redirect unifies these with trust-types' aliases so the
// re-exported public types (e.g. `Formula::free_variables() -> FxHashSet`)
// are byte-for-byte the same type.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

pub use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet, FxHasher};
