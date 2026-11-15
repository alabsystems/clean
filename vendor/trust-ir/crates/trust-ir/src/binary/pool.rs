// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The binary writer's string table, in its two phases.
//!
//! A module's strings are emitted ONCE, as a length-prefixed table in the
//! header, and every later field spells a string as an INDEX into that table.
//! The encoder is therefore two walks over the same module: a COLLECTION walk
//! (`collect_*`) that fills the table and settles the header version, and a
//! WRITE walk (`write_*`) that indexes it. If the write walk could add a
//! string, it would index past the table the header already committed to; if
//! it could lower the header requirement, it would emit a feature under a
//! header the reader refuses.
//!
//! The two types here are what separate the phases. [`StringPoolBuilder`] is
//! the open phase: it can [`intern`](StringPoolBuilder::intern) and
//! [`raise_to`](StringPoolBuilder::raise_to). [`seal`](StringPoolBuilder::seal)
//! converts it into a [`SealedStringPool`], which has neither method and is
//! handed out only behind `&`. Every `write_*` function in the parent module
//! takes `&SealedStringPool`, so the pool a write function is HANDED can
//! neither grow nor move its version, and [`id_of`](SealedStringPool::id_of)
//! refuses by name a string the collection walk never interned.
//!
//! TWO THINGS THIS DOES NOT GIVE, stated so the next reader does not
//! over-trust the types.
//!
//! First, `new`, `intern` and `seal` are `pub(super)`, and `super` is the
//! whole `binary` module — where all 44 write functions live. A write
//! function can therefore still build a table of its own:
//!
//! ```text
//! let mut fabricated = StringPoolBuilder::new();
//! fabricated.intern("never-in-the-header-table");
//! let fabricated = fabricated.seal();
//! write_str(buf, &fabricated, "never-in-the-header-table");
//! ```
//!
//! MEASURED 2026-09-20, that compiles clean at the top of `write_ty` and
//! emits index 0 into a table the header never committed to — a
//! self-inconsistent blob, which is the original defect's effect reached by
//! another route. What the split does kill is the one-line version of the
//! mistake, `pool.intern(..)` on the pool already in hand; the fabrication
//! above takes a deliberate three lines. Closing it means the write walk
//! being able to name the sealed type ONLY: the `collect_*` walk moved into a
//! sibling submodule, so `StringPoolBuilder` is not in scope on the write
//! side at all. That move is not made here.
//!
//! Second, these types do not make the two walks AGREE. `id_of` sees one
//! direction only — the writer spelling a string the collection walk skipped.
//! A collection walk that raises the header version or interns a string where
//! the writer spells nothing is invisible to the sealed pool: it changes the
//! header and shifts every later id, unopposed. That direction is pinned by
//! tests instead (see the contract-surface comment in
//! `collect_function_strings`, which names the assertion and the measurement).
//!
//! MEASURED 2026-09-20 with `targo --unverified check -p trust-ir` (the
//! no-proof-claim lane), by adding each line below to a real body and reading
//! what `trustc` said. A late `intern` in the write walk — `pool.intern(..)`
//! in `write_ty`:
//!
//! ```text
//! error[E0599]: no method named `intern` found for reference `&SealedStringPool` in the current scope
//!     --> crates/trust-ir/src/binary.rs:2079:10
//!      |
//! 2079 |     pool.intern("late-interned-string");
//!      |          ^^^^^^
//! ```
//!
//! a late header raise in the write walk — `pool.raise_to(45)` in `write_ty`:
//!
//! ```text
//! error[E0599]: no method named `raise_to` found for reference `&SealedStringPool` in the current scope
//!     --> crates/trust-ir/src/binary.rs:2079:10
//!      |
//! 2079 |     pool.raise_to(45);
//!      |          ^^^^^^^^ method not found in `&SealedStringPool`
//! ```
//!
//! and the assignment that regressed the monotone raise — `pool.minimum_version
//! = 45` in `collect_type_identity_strings`, where the OPEN builder IS in hand:
//!
//! ```text
//! error[E0609]: no field `minimum_version` on type `&mut StringPoolBuilder`
//!     --> crates/trust-ir/src/binary.rs:1724:10
//!      |
//! 1724 |     pool.minimum_version = 45;
//!      |          ^^^^^^^^^^^^^^^ unknown field
//! ```
//!
//! None of the three is spelled as a `compile_fail` doctest, and that is not
//! an omission — MEASURED the same day under `--features binary` (the lane
//! `scripts/ci_gates.sh` runs doctests in, and the only configuration in
//! which this codec ships at all), a doctest naming
//! `trust_ir::binary::pool::StringPoolBuilder::new()` dies on the very
//! privacy that carries the invariant, before reaching any property:
//!
//! ```text
//! error[E0603]: module `pool` is private
//!    |                        (a temporary doc fence, so no real site)
//!    | let _ = trust_ir::binary::pool::StringPoolBuilder::new();
//!    |                           ^^^^  ----------------- struct `StringPoolBuilder` is not publicly re-exported
//!    |                           |
//!    |                           private module
//!
//! error[E0624]: associated function `new` is private
//! ```
//!
//! (With default features it dies one level earlier still, on ``module
//! `binary` is private`` — `pub mod binary` is itself feature-gated — so that
//! lane measures the feature gate, not the `mod pool` privacy above.)
//!
//! A doctest compiles as an EXTERNAL crate, so the privacy that makes this
//! invariant hold is the same privacy that puts it out of a doctest's reach: a
//! `compile_fail` fence here would pass on the module path and prove nothing
//! about interning. What stays runnable is the unit tests at the bottom of
//! this file — raise monotonicity in either order, that sealing preserves the
//! table and the settled version, and a `#[should_panic]` on the fail-closed
//! lookup.

use std::collections::BTreeMap;
use std::rc::Rc;

use super::BASE_FORMAT_VERSION;

/// The table itself, shared by both phases and reachable from neither: a
/// phase's method set is the whole of what that phase can do to it.
#[derive(Clone)]
struct Table {
    // The ordered wire table and the lookup index share one allocation for
    // each unique string. Module serialization is also the stable-digest
    // path, so retaining two owned `String` copies here used to add a second
    // whole-string-table memory component to every digest/serialization.
    strings: Vec<Rc<str>>,
    // `u64`, not `u32`: an id is a table position, and the table's COUNT is
    // what the format limits (`write_count` reports a table past `u32::MAX`
    // entries). The writer spells an id with `write_v64`, byte-identical to
    // the `write_v32` spelling for every id the format can carry.
    map: BTreeMap<Rc<str>, u64>,
    minimum_version: u32,
    blank_debug_files: bool,
}

impl Table {
    fn debug_file<'p>(&self, path: &'p str) -> &'p str {
        if self.blank_debug_files { "" } else { path }
    }
}

/// The OPEN phase: the table as the collection walk sees it.
pub(super) struct StringPoolBuilder(Table);

impl StringPoolBuilder {
    pub(super) fn new() -> Self {
        Self::with_blanked_debug_files(false)
    }

    /// With `blank_debug_files`, a builder for the v3 IDENTITY projection
    /// (`IdentityScheme::V3`, WS4.10), which writes every `Module.files` path
    /// as `""` and keeps the table length. The projection is chosen HERE, at
    /// construction, so it is a property of the pool a walk was handed rather
    /// than a flag some later step can flip: `ModuleBinaryPlan::identity` is
    /// the only caller that passes `true`, and it is not a serialization path.
    pub(super) fn with_blanked_debug_files(blank_debug_files: bool) -> Self {
        Self(Table {
            strings: Vec::new(),
            map: BTreeMap::new(),
            minimum_version: BASE_FORMAT_VERSION,
            blank_debug_files,
        })
    }

    pub(super) fn intern(&mut self, s: &str) -> u64 {
        if let Some(&id) = self.0.map.get(s) {
            return id;
        }
        // `usize` is at most 64 bits on every target Rust supports, so this
        // widening cast is exact.
        let id = self.0.strings.len() as u64;
        let owned = Rc::<str>::from(s);
        self.0.map.insert(Rc::clone(&owned), id);
        self.0.strings.push(owned);
        id
    }

    /// Require the header to be at least `version`. The only mutator of the
    /// requirement, and it is a MAX rather than an assignment, so two
    /// features that each need a different minimum cannot overwrite one
    /// another whatever order the walk discovers them in.
    pub(super) fn raise_to(&mut self, version: u32) {
        self.0.minimum_version = self.0.minimum_version.max(version);
    }

    /// Only the sealed table's version is read on a write path; this reader
    /// exists for the monotonicity test below.
    #[cfg(test)]
    pub(super) fn minimum_version(&self) -> u32 {
        self.0.minimum_version
    }

    /// The `Module.files` entry the writer spells for `path`: the path itself,
    /// or `""` under the v3 identity projection.
    pub(super) fn debug_file<'p>(&self, path: &'p str) -> &'p str {
        self.0.debug_file(path)
    }

    /// Close the table. Everything after this point can look a string up and
    /// read the settled version; nothing can add to either.
    pub(super) fn seal(self) -> SealedStringPool {
        SealedStringPool::closed(self.0)
    }
}

/// The SEALED phase: the table as the write walk sees it, and as it was
/// emitted.
pub(super) struct SealedStringPool {
    table: Table,
    /// Test-only. The wire census probes ~45 tag spaces by running each
    /// sampled value through the real writer, and has no collection walk of
    /// its own to pair with any of them. Under
    /// [`by_replay_from`](Self::by_replay_from) a lookup miss is RECORDED here
    /// and the walk repeated against a table that now holds the string,
    /// instead of refusing. No non-test constructor sets this, so no
    /// serialization path can take the recording branch.
    #[cfg(test)]
    discovered: Option<std::cell::RefCell<Vec<Rc<str>>>>,
}

impl SealedStringPool {
    fn closed(table: Table) -> Self {
        Self {
            table,
            #[cfg(test)]
            discovered: None,
        }
    }

    /// The wire table, in emitted order.
    pub(super) fn strings(&self) -> &[Rc<str>] {
        &self.table.strings
    }

    /// The id the emitted table gave `s`.
    ///
    /// Fail-closed and always on: a string the collection walk never interned
    /// has no id in the table the header already committed to, so there is no
    /// number to write. This is the one residual check of collector coverage,
    /// and unlike the five scattered table-length deltas it replaces it names
    /// the string that is missing.
    pub(super) fn id_of(&self, s: &str) -> u64 {
        if let Some(&id) = self.table.map.get(s) {
            return id;
        }
        #[cfg(test)]
        if let Some(discovered) = &self.discovered {
            let mut discovered = discovered.borrow_mut();
            if !discovered.iter().any(|seen| &**seen == s) {
                discovered.push(Rc::<str>::from(s));
            }
            return 0;
        }
        panic!("binary string collector missed an emitted string: {s:?}");
    }

    pub(super) fn minimum_version(&self) -> u32 {
        self.table.minimum_version
    }

    /// The `Module.files` entry the writer spells for `path`: the path itself,
    /// or `""` under the v3 identity projection.
    pub(super) fn debug_file<'p>(&self, path: &'p str) -> &'p str {
        self.table.debug_file(path)
    }

    #[cfg(test)]
    pub(super) fn into_reader_strings(self) -> Vec<String> {
        self.table
            .strings
            .into_iter()
            .map(|value| value.as_ref().to_owned())
            .collect()
    }

    /// Test-only: the bytes `spell` writes, against a table sealed by REPLAY.
    ///
    /// `spell` is run against a recording probe until a pass discovers no new
    /// string (a nested record can spell one only after an outer id has been
    /// written), the discovered strings are interned in first-spelled order —
    /// which is the order a fresh pool used to assign them in, so the bytes
    /// are unchanged — and then `spell` runs once more against the sealed
    /// table. The census needs this because it samples variants, not modules;
    /// a real serialization gets its table from `collect_strings`, which IS
    /// the collection walk.
    #[cfg(test)]
    pub(super) fn by_replay_from(
        mut seed: StringPoolBuilder,
        spell: impl Fn(&Self, &mut Vec<u8>),
    ) -> Vec<u8> {
        loop {
            let probe = Self {
                table: seed.0.clone(),
                discovered: Some(std::cell::RefCell::new(Vec::new())),
            };
            spell(&probe, &mut Vec::new());
            let found = probe
                .discovered
                .expect("the probe was constructed recording")
                .into_inner();
            if found.is_empty() {
                break;
            }
            for string in found {
                seed.intern(&string);
            }
        }
        let sealed = seed.seal();
        let mut bytes = Vec::new();
        spell(&sealed, &mut bytes);
        bytes
    }

    /// Test-only: [`by_replay_from`](Self::by_replay_from) starting from an
    /// empty table.
    #[cfg(test)]
    pub(super) fn by_replay(spell: impl Fn(&Self, &mut Vec<u8>)) -> Vec<u8> {
        Self::by_replay_from(StringPoolBuilder::new(), spell)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn writer_string_pool_shares_one_owned_value_between_order_and_lookup() {
        let mut pool = StringPoolBuilder::new();
        let first = pool.intern("shared-compiler-identity");
        let repeated = pool.intern("shared-compiler-identity");

        assert_eq!(first, repeated);
        assert_eq!(pool.0.strings.len(), 1);
        assert_eq!(pool.0.map.len(), 1);
        let ordered = &pool.0.strings[first as usize];
        let indexed = pool
            .0
            .map
            .keys()
            .next()
            .expect("one lookup-index allocation");
        assert!(
            Rc::ptr_eq(ordered, indexed),
            "wire order and lookup index must share the same string allocation"
        );
    }

    #[test]
    fn raising_the_header_requirement_is_monotone_in_either_order() {
        let mut ascending = StringPoolBuilder::new();
        ascending.raise_to(41);
        ascending.raise_to(45);
        let mut descending = StringPoolBuilder::new();
        descending.raise_to(45);
        descending.raise_to(41);
        assert_eq!(ascending.minimum_version(), 45);
        assert_eq!(descending.minimum_version(), 45);
    }

    #[test]
    fn sealing_preserves_the_table_and_the_settled_version() {
        let mut builder = StringPoolBuilder::new();
        builder.intern("first");
        builder.intern("second");
        builder.raise_to(43);
        let sealed = builder.seal();
        assert_eq!(sealed.id_of("first"), 0);
        assert_eq!(sealed.id_of("second"), 1);
        assert_eq!(sealed.strings().len(), 2);
        assert_eq!(sealed.minimum_version(), 43);
    }

    #[test]
    #[should_panic(expected = "binary string collector missed an emitted string")]
    fn a_string_the_collector_missed_has_no_id_to_write() {
        StringPoolBuilder::new().seal().id_of("never-collected");
    }

    #[test]
    fn replay_assigns_the_ids_a_fresh_interning_pool_would_have() {
        let bytes = SealedStringPool::by_replay(|pool, buf| {
            for s in ["a", "b", "a", "c"] {
                buf.push(u8::try_from(pool.id_of(s)).expect("small id"));
            }
        });
        assert_eq!(bytes, [0, 1, 0, 2]);
    }

    #[test]
    fn replay_carries_the_seed_version_through() {
        let mut seed = StringPoolBuilder::new();
        seed.raise_to(45);
        let bytes = SealedStringPool::by_replay_from(seed, |pool, buf| {
            buf.push(u8::try_from(pool.minimum_version()).expect("small version"));
        });
        assert_eq!(bytes, [45]);
    }
}
