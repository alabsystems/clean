// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// The fresh-id rule (`FreshIds`, r11) and the table-id rule (`table_index`,
// rule 4 of `docs/SPEC_RATIFICATIONS.md`, "A construct or count with no wire
// image is refused by the writer's own arm, at every trust-ir entry point")
// are stated here once, so nothing here may panic, index, wrap or truncate.
// Rung: a type-resolved lint (gate 0 `workspace-clippy`), below type-level; a
// visible `#[allow]` defeats it.
#![cfg_attr(
    not(test),
    deny(
        clippy::panic,
        clippy::unwrap_used,
        clippy::expect_used,
        clippy::indexing_slicing,
        clippy::arithmetic_side_effects,
        clippy::cast_possible_truncation
    )
)]

macro_rules! typed_id {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
        pub struct $name(pub u32);

        impl core::fmt::Debug for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, "{}({})", stringify!($name), self.0)
            }
        }

        impl core::fmt::Display for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, "{}", self.0)
            }
        }

        impl $name {
            pub const fn new(index: u32) -> Self {
                Self(index)
            }

            pub const fn index(self) -> u32 {
                self.0
            }

            pub const fn as_usize(self) -> usize {
                self.0 as usize
            }
        }

        impl $crate::value::TypedId for $name {
            const SPACE: &'static str = stringify!($name);

            fn from_index(index: u32) -> Self {
                Self(index)
            }

            fn index(self) -> u32 {
                self.0
            }
        }
    };
}

typed_id!(
    /// SSA value reference. Index into a function's value table.
    ValueId
);

typed_id!(
    /// Basic block reference. Index into a function's block list.
    BlockId
);

typed_id!(
    /// Function reference. Index into a module's function list.
    FuncId
);

typed_id!(
    /// Struct definition reference. Index into a module's struct table.
    StructId
);

typed_id!(
    /// Type reference. Index into a module's type table.
    TyId
);

typed_id!(
    /// Function type reference. Index into a module's func type table.
    FuncTyId
);

typed_id!(
    /// Enum definition reference. Index into a module's enum table.
    EnumId
);

typed_id!(
    /// Global definition reference. Index into a module's `globals` table.
    ///
    /// Materialized as an SSA pointer by `Inst::GlobalAddr`. A frontend lowers
    /// `&STATIC`, a `&str` literal's backing data, and a trait-object vtable
    /// reference to a `GlobalAddr` of the corresponding `GlobalId`; `trust-cg`
    /// emits a relocation to the data/rodata symbol named by that global.
    GlobalId
);

typed_id!(
    /// Proof annotation reference. Index into a module's proof table.
    ProofId
);

typed_id!(
    /// Custom proof tag for extensible proof annotations.
    ProofTag
);

typed_id!(
    /// Binding frame reference.
    ///
    /// Identifies a binding frame — a typed record of SSA slots used to
    /// lower quantifier bodies (`\E i \in S : P(i)`, `\A i \in S : P(i)`).
    /// Each `Inst::OpenFrame` declares a fresh `BindingFrameId` that is
    /// unique within the enclosing function.
    ///
    /// Binding frames are SSA values (not memory) so backends can lower
    /// them to either stack allocations (CPU) or per-lane register banks
    /// (GPU). See `designs/2026-04-18-ty-supremacy-trust-ir-scope.md` §R4.
    BindingFrameId
);

typed_id!(
    /// Record definition reference. Index into a module's record table.
    ///
    /// Records (ty-style) differ from structs: they have named fields but no
    /// fixed layout, no offset/size/align metadata, and equality is by
    /// field-set rather than memory layout. Frontends that need C-style layout
    /// should use `StructId` instead.
    RecordId
);

typed_id!(
    /// Refinement predicate reference. Index into a module's `predicates`
    /// table (see [`crate::pred::Pred`]).
    ///
    /// **Content-interned.** Unlike `StructId`/`EnumId`/`RecordId`, whose
    /// definitions carry a name and therefore a producer-chosen identity, a
    /// `PredId` is a pure function of the predicate's CONTENT: two predicates
    /// with the same meaning are the same id no matter which proof, pass or
    /// frontend minted them. That is not a convenience — it is the structural
    /// fix for the join-drop miscompile class, where two carriers over an
    /// identical universe failed to merge at a control-flow join because they
    /// had been cited by different proofs, the shape was dropped, and the
    /// value silently reverted to the raw encoding convention. Mint one with
    /// [`crate::Module::intern_pred`]; the validator rejects a `predicates`
    /// table containing duplicate content.
    PredId
);

typed_id!(
    /// Universe reference. Index into a module's `universes` table (see
    /// [`crate::pred::Universe`]).
    ///
    /// Content-interned for exactly the reason [`PredId`] is: a universe's
    /// identity is its extension and nothing else. Mint one with
    /// [`crate::Module::intern_universe`].
    UnivId
);

typed_id!(
    /// Imported-module reference. Index into a module's `imports` table (see
    /// [`crate::ModuleImport`]).
    ///
    /// **Content-interned**, for the same reason [`PredId`] and [`UnivId`] are:
    /// an import's identity is the exact `(name, digest, producer)` triple it
    /// names and nothing else, so two `ExternRef`s that cite the same artifact
    /// carry the same id no matter which certificate or summary minted them.
    /// Mint one with [`crate::Module::intern_import`], never `push`.
    ///
    /// Renumbering-invariance is the point: an `ImportId` is meaningful only
    /// against its own module's table order, which is why every cross-module
    /// claim travels as an [`crate::ExternRef`] carrying this id ALONGSIDE the
    /// symbol and obligation it names, rather than as a bare index.
    ImportId
);

typed_id!(
    /// Closure type reference. Index into a module's closure type table.
    ///
    /// A closure is a first-class function value bundled with a captured
    /// environment (see `ClosureTy` in `ty`). Bare function-pointer types
    /// (no captures) use `FuncTyId` directly.
    ClosureTyId
);

typed_id!(
    /// A template's type or const parameter (amendment S): an index into
    /// `TemplateHeader::params`. Spelled `$n` in text.
    ParamId
);

typed_id!(
    /// A template's hole (amendment S): an index into
    /// `TemplateHeader::holes`. Spelled `?n` in text.
    HoleId
);

// ---------------------------------------------------------------------------
// Fresh ids: the ONE rule for minting an id of a u32 space
// ---------------------------------------------------------------------------

/// Every id of one `u32` id space (or of one reserved range of it) is taken.
///
/// This is the one refusal of the one rule for minting a fresh id
/// ([`FreshIds`], [`IdRun`]): an exhausted space is REFUSED, never wrapped
/// onto an id already in use and never clamped to one. `space` names what ran
/// out — a typed id's name (`"ValueId"`, `"BlockId"`, `"ProofId"`, …, the
/// [`TypedId::SPACE`] of the id) or a named reserved range.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IdSpaceExhausted {
    /// The exhausted space.
    pub space: &'static str,
}

impl IdSpaceExhausted {
    /// The refusal for the whole id space of `I`.
    pub const fn of<I: TypedId>() -> Self {
        Self { space: I::SPACE }
    }
}

impl core::fmt::Display for IdSpaceExhausted {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "the {} id space is exhausted: every id is taken (refused, never wrapped)",
            self.space
        )
    }
}

impl std::error::Error for IdSpaceExhausted {}

/// A typed `u32` id ([`ValueId`], [`BlockId`], [`ProofId`], …).
///
/// Implemented by every id `typed_id!` defines, and by hand for the ids
/// defined elsewhere (`proof::ProofLineageId`). It exists so the one fresh-id
/// rule ([`FreshIds`], [`IdRun`]) is written once for every id space.
pub trait TypedId: Copy {
    /// The id space's name, as [`IdSpaceExhausted::space`] reports it.
    const SPACE: &'static str;
    /// The id with raw index `index`.
    fn from_index(index: u32) -> Self;
    /// This id's raw index.
    fn index(self) -> u32;
}

// The rule's DECISIONS, monomorphic over raw `u32` indices. [`FreshIds`] and
// [`IdRun`] are generic over the id type and carry `Option`s, and the
// verified lane cannot state a law about either (measured 2026-10-01: a law
// over `FreshIds::<ValueId>::after([u32::MAX])` or `IdRun::span(0, u32::MAX)`
// stays UNKNOWN). So every bound the rule decides is one of the three
// comparison tables below, and gate 13 (`scripts/verified_contracts.py`)
// proves each over every input and at every boundary row (`laws::fresh_*` in
// crates/trust-ir-laws; Certified, KernelRechecked, under refuting same-shape
// mutants).
//
// The cursor decides by these tables AND BY NOTHING ELSE. After a table
// admits, the value it licenses (`id + 1`, `first + extra`, `last - first`)
// is computed with `wrapping_*`, which is exact on every input the table
// admitted and decides nothing. A `checked_*` step there would decide the
// same bound a second time, and where the two disagreed the cursor would
// follow the unproved one: measured 2026-10-01 (review of this rule), with
// the table edited to admit `u32::MAX` the old checked cursor still refused,
// and with the table's read cut every cited Rust test stayed green — the
// proved table held nothing. Now a table that admits `u32::MAX`, or a cursor
// that stops reading a table, computes a wrapped value: each of the three
// reads cut turns `the_cursor_decides_by_the_fresh_id_tables` red, and the
// exhaustion and run reads cut, or the wrapping table, also turn
// `fresh_ids_are_one_past_the_highest_and_never_wrap` red (mutation-checked
// 2026-10-01, each edit alone).
// What is PROVED is each table; that the cursor reads them, and that the
// `wrapping_*` step is exact under the table's verdict, is code, TESTED.

/// Whether the id `id` has a SUCCESSOR in its `u32` space: exactly when it is
/// below `u32::MAX`.
///
/// The exhaustion row of the fresh-id rule. A cursor moves past an id only
/// through this table — [`FreshIds::take`] past the id it hands out,
/// [`FreshIds::after`] past a used id, a run past its last id, [`IdRun`] past
/// a non-final id — so `u32::MAX`, and only it, leaves a cursor exhausted:
/// refused, never wrapped onto id 0. An [`IdRun::span`]'s count `width + 1` is
/// representable by the same row (only the whole space, width `u32::MAX`, has
/// none).
///
/// PROVED, every boundary row (gate 13): `laws::fresh_successor_iff_below_max`
/// (the row over every `u32`), `laws::fresh_successor_absent_at_max`,
/// `laws::fresh_successor_present_below_max`, `laws::fresh_successor_present_at_zero`.
#[must_use]
pub const fn fresh_id_has_successor(id: u32) -> bool {
    id < u32::MAX
}

/// Whether a run whose LAST id lies `extra` ids past its first fits in the
/// `room` its space has above that first id (`u32::MAX - first`, which the
/// cursor computes as the complement `!first`, total for every `u32`):
/// exactly when `extra <= room`.
///
/// The all-or-nothing row of [`FreshIds::take_run`] /
/// [`FreshIds::take_run_below`]: a run of `count` ids from the cursor is taken
/// whole when `count - 1` fits the room, and otherwise refused with the
/// cursor unchanged. Stated over the room rather than the first id because the
/// lane proves a comparison and not the subtraction (measured 2026-10-01:
/// `extra <= u32::MAX - first` in the table leaves its overflow row UNKNOWN).
///
/// PROVED, every boundary row (gate 13): `laws::fresh_run_fits_iff_within_room`
/// (the row over every pair), `laws::fresh_run_fits_single_id_anywhere`,
/// `laws::fresh_run_fits_whole_space`, `laws::fresh_run_fits_refused_past_max`.
#[must_use]
pub const fn fresh_run_fits(extra: u32, room: u32) -> bool {
    extra <= room
}

/// Whether `id` lies strictly below `end_exclusive`.
///
/// The bounded row of [`FreshIds::take_run_below`] (a run whose last id
/// reaches the bound is refused, so a caller's reserved range above it is
/// never handed out), and the order the rule reads twice more:
/// [`FreshIds::after`] leaves the cursor where it is exactly when a used id
/// is below it, and [`IdRun::span`] is empty exactly when its last id is
/// below its first.
///
/// PROVED, every boundary row (gate 13): `laws::fresh_below_iff_less` (the row
/// over every pair), `laws::fresh_below_refuses_the_bound`,
/// `laws::fresh_below_admits_the_last_id_under_the_bound`.
#[must_use]
pub const fn fresh_id_below(id: u32, end_exclusive: u32) -> bool {
    id < end_exclusive
}

/// The id after `id`, decided by [`fresh_id_has_successor`] and by nothing
/// else; `None` when the space has no successor to give.
const fn successor(id: u32) -> Option<u32> {
    if fresh_id_has_successor(id) {
        // Exact: the table admitted `id < u32::MAX`, so `id + 1` is in range.
        // `wrapping_add` so that this step decides nothing (see above).
        Some(id.wrapping_add(1))
    } else {
        None
    }
}

/// The last id of a run that starts at `first` and ends `extra` ids later,
/// decided by [`fresh_run_fits`] against the room above `first` and by
/// nothing else; `None` when the run does not fit. The room is `!first`, the
/// bitwise complement, which IS `u32::MAX - first` for every `u32` and is
/// spelled without arithmetic.
const fn run_last(first: u32, extra: u32) -> Option<u32> {
    if fresh_run_fits(extra, !first) {
        // Exact: the table admitted `extra <= u32::MAX - first`.
        Some(first.wrapping_add(extra))
    } else {
        None
    }
}

/// Fresh ids of one space, in increasing order. Total: a take either returns
/// an id no earlier take of this cursor returned, or refuses with
/// [`IdSpaceExhausted`].
///
/// "Fresh" means ONE PAST THE HIGHEST id in use ([`Self::after`]), never a
/// recycled gap: a stale reference to a deleted row must not bind a new one.
/// The cursor is deliberately neither `Clone` nor `Copy`, so an id cannot be
/// minted twice from a duplicated cursor.
pub struct FreshIds<I> {
    /// The next id to hand out; `None` once the space is exhausted (absorbing).
    next: Option<u32>,
    _id: core::marker::PhantomData<fn() -> I>,
}

impl<I> core::fmt::Debug for FreshIds<I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("FreshIds")
            .field("next", &self.next)
            .finish()
    }
}

impl<I> PartialEq for FreshIds<I> {
    fn eq(&self, other: &Self) -> bool {
        self.next == other.next
    }
}

impl<I> Eq for FreshIds<I> {}

impl<I: TypedId> Default for FreshIds<I> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: TypedId> FreshIds<I> {
    /// A cursor over an unused space: the first id is `0`.
    pub const fn new() -> Self {
        Self {
            next: Some(0),
            _id: core::marker::PhantomData,
        }
    }

    /// The cursor one past the HIGHEST id in `used` (`0` for none). Exhausted
    /// exactly when `used` holds `u32::MAX`, whatever else it holds.
    pub fn after(used: impl IntoIterator<Item = I>) -> Self {
        let mut next = Some(0_u32);
        for id in used {
            let index = id.index();
            next = match (next, successor(index)) {
                // A used id below the cursor leaves it; one at or above it
                // moves it to that id's successor (the max, by the table).
                (Some(current), Some(candidate)) => Some(if fresh_id_below(index, current) {
                    current
                } else {
                    candidate
                }),
                _ => None,
            };
        }
        Self {
            next,
            _id: core::marker::PhantomData,
        }
    }

    /// The id the next [`Self::take`] returns, or `None` when exhausted.
    pub fn peek(&self) -> Option<I> {
        self.next.map(I::from_index)
    }

    /// Whether every id of the space is taken.
    pub fn is_exhausted(&self) -> bool {
        self.next.is_none()
    }

    /// Take the next id.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] once `u32::MAX` has been taken; the cursor stays
    /// exhausted.
    pub fn take(&mut self) -> Result<I, IdSpaceExhausted> {
        let id = self.next.ok_or(IdSpaceExhausted::of::<I>())?;
        self.next = successor(id);
        Ok(I::from_index(id))
    }

    /// Take `count` consecutive ids as one run, all or nothing.
    ///
    /// `count == 0` is an empty run and consumes nothing.
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when fewer than `count` ids remain; the cursor is
    /// then unchanged.
    pub fn take_run(&mut self, count: u32) -> Result<IdRun<I>, IdSpaceExhausted> {
        self.take_run_until(count, None)
    }

    /// [`Self::take_run`] inside a BOUNDED space: every id of the run must be
    /// below `end_exclusive` (a caller that reserves the ids above it for
    /// something else).
    ///
    /// # Errors
    ///
    /// [`IdSpaceExhausted`] when the run would reach `end_exclusive` or past
    /// `u32::MAX`; the cursor is then unchanged.
    pub fn take_run_below(
        &mut self,
        count: u32,
        end_exclusive: u32,
    ) -> Result<IdRun<I>, IdSpaceExhausted> {
        self.take_run_until(count, Some(end_exclusive))
    }

    fn take_run_until(
        &mut self,
        count: u32,
        end_exclusive: Option<u32>,
    ) -> Result<IdRun<I>, IdSpaceExhausted> {
        let exhausted = IdSpaceExhausted::of::<I>();
        let Some(extra) = count.checked_sub(1) else {
            return Ok(IdRun::empty());
        };
        let first = self.next.ok_or(exhausted)?;
        let last = run_last(first, extra).ok_or(exhausted)?;
        if end_exclusive.is_some_and(|end| !fresh_id_below(last, end)) {
            return Err(exhausted);
        }
        self.next = successor(last);
        Ok(IdRun {
            next: first,
            remaining: count,
            _id: core::marker::PhantomData,
        })
    }
}

/// A reserved, finite run of consecutive ids, handed out in increasing order.
///
/// The number of ids left is STORED, so no subtraction of cursor positions
/// exists to go wrong. Minted only by [`FreshIds::take_run`],
/// [`FreshIds::take_run_below`] or [`IdRun::span`]; neither `Clone` nor
/// `Copy`, so no id of a run is handed out twice.
pub struct IdRun<I> {
    next: u32,
    remaining: u32,
    _id: core::marker::PhantomData<fn() -> I>,
}

impl<I> core::fmt::Debug for IdRun<I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("IdRun")
            .field("next", &self.next)
            .field("remaining", &self.remaining)
            .finish()
    }
}

impl<I> PartialEq for IdRun<I> {
    fn eq(&self, other: &Self) -> bool {
        self.next == other.next && self.remaining == other.remaining
    }
}

impl<I> Eq for IdRun<I> {}

impl<I: TypedId> IdRun<I> {
    const fn empty() -> Self {
        Self {
            next: 0,
            remaining: 0,
            _id: core::marker::PhantomData,
        }
    }

    /// The fixed range `first..=last_inclusive`, e.g. a reserved block-id
    /// range. `None` when `first > last_inclusive`, or when the range holds
    /// all `2^32` ids (a count no `u32` holds).
    pub fn span(first: u32, last_inclusive: u32) -> Option<Self> {
        if fresh_id_below(last_inclusive, first) {
            return None;
        }
        // Exact: the table refused `last_inclusive < first`. `wrapping_sub`
        // so that this step decides nothing (see the comment above
        // `fresh_id_has_successor`).
        let width = last_inclusive.wrapping_sub(first);
        let remaining = successor(width)?;
        Some(Self {
            next: first,
            remaining,
            _id: core::marker::PhantomData,
        })
    }

    /// How many ids the run has left.
    pub fn remaining(&self) -> u32 {
        self.remaining
    }

    /// Take the run's next id, or `None` once it is used up.
    pub fn take(&mut self) -> Option<I> {
        let rest = self.remaining.checked_sub(1)?;
        let id = self.next;
        // A run minted by a constructor never ends past `u32::MAX`, so a
        // non-final id always has a successor; were it ever not, the take
        // refuses to mint rather than clamp.
        let next = if rest > 0 { successor(id)? } else { id };
        self.next = next;
        self.remaining = rest;
        Some(I::from_index(id))
    }
}

// ---------------------------------------------------------------------------
// Table ids: the ONE rule for naming a table slot by a u32 id
// ---------------------------------------------------------------------------

/// The raw `u32` id of table slot `index` — pass a table's length to name
/// its NEXT slot — or the refusal naming `space`.
///
/// The one statement of "a table index names an id" (rule 4 of
/// `docs/SPEC_RATIFICATIONS.md`, "A construct or count with no wire image is
/// refused by the writer's own arm, at every trust-ir entry point"): an index
/// past `u32::MAX` names nothing and is REFUSED, never truncated — `index as
/// u32` would alias slot `2^32 + k` onto slot `k`. It exists beside
/// [`table_id`] for the one table named by a raw `u32` rather than a typed id
/// (`Module.files`, through `SourceSpan.file`). A loop that only needs the
/// index of each entry it visits states the same rule as the exact
/// enumeration `(0..=u32::MAX).zip(..)`, where an entry past `u32::MAX` can
/// be named by nothing.
///
/// # Errors
///
/// [`IdSpaceExhausted`] naming `space` when `index > u32::MAX`.
pub fn table_index(index: usize, space: &'static str) -> Result<u32, IdSpaceExhausted> {
    u32::try_from(index).map_err(|_| IdSpaceExhausted { space })
}

/// The typed id of table slot `index` — pass a table's length to name its
/// NEXT slot — or the refusal naming `I`'s space ([`table_index`]).
///
/// # Errors
///
/// [`IdSpaceExhausted::of::<I>()`](IdSpaceExhausted::of) when
/// `index > u32::MAX`.
pub fn table_id<I: TypedId>(index: usize) -> Result<I, IdSpaceExhausted> {
    table_index(index, I::SPACE).map(I::from_index)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SourceSpan {
    pub file: u32,
    pub line: u32,
    pub col: u32,
}

/// One entry in a function's LEXICAL SCOPE TREE (v33).
///
/// A scope is the debug-info notion, not the SSA one: it records where in the
/// SOURCE a name became visible, so a debugger stopped at an instruction can be
/// told which bindings are in scope there. SSA values are function-unique and
/// scope-free; this table sits beside them as claim-style metadata and carries
/// no operational semantics.
///
/// INVARIANTS (checked by the consumer, which fails closed rather than trusting
/// them — a producer bug must not become a debugger lie):
/// * index `0` is the OUTERMOST scope and is the only one with `parent: None`;
/// * every other entry has `parent: Some(p)` with `p <` its own index.
///
/// The `p < index` rule makes the table topologically ordered by construction,
/// so acyclicity is a range check rather than a traversal — and a consumer can
/// build its own tree in one forward pass.
///
/// **Inlining chain (WS4.19, F-082).** A scope that came from an INLINED
/// callee — the body of `callee` spliced into this function at a call site —
/// records that fact in [`inlined_at`](Self::inlined_at). Walking `parent`
/// links from an instruction's scope and collecting every `inlined_at` on the
/// way up yields the DWARF `DW_TAG_inlined_subroutine` chain ("inlined from
/// caller.rs:12"), which is the only way a diagnostic or a debugger can
/// attribute an inlined Clean body to its Clean source instead of to the Rust
/// caller's scope. Without the field the attribution is imprecise, not
/// unsound; with the field it is checkable, and the validator checks it
/// (`InvalidInlinedScope`, `SpanFileIndexOutOfRange`).
///
/// **Transport.** The text, JSON and MessagePack formats carry the chain
/// losslessly. The BINARY format does not yet: its carrier is a member of the
/// next open wire batch (roadmap WS4.19 "wire impact"; a version must be
/// reserved through `docs/wire-allocation.md` before any byte spells it), and
/// until that batch lands the binary writer REFUSES a module whose scope
/// table carries a chain (`BinaryProjectionError::InlinedScopeChainUnencodable`;
/// the infallible entry points panic with the same message) rather than
/// silently dropping it and calling the round trip complete.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ScopeData {
    /// Enclosing scope index, or `None` for the outermost scope.
    pub parent: Option<u32>,
    /// Where the scope OPENS. `None` when the producer had no usable location.
    pub span: Option<SourceSpan>,
    /// The call site this scope was inlined at, when the scope is the body of
    /// an inlined callee; `None` for an ordinary lexical scope.
    ///
    /// Sole trailing conditionally-skipped field of this struct: the canonical
    /// MessagePack codec is POSITIONAL, so a pre-WS4.19 array stops at `span`
    /// and decodes with no chain, and a module without a chain keeps its
    /// exact pre-WS4.19 JSON and MessagePack bytes. The call-site span and the
    /// callee travel as ONE record ([`InlinedAt`]) for the same reason: two
    /// independently optional trailing fields cannot both be skipped
    /// positionally, and a chain link with only half its content is not a
    /// chain link (MIR's own `SourceScopeData::inlined` is likewise one
    /// `Option<(Instance, Span)>`).
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub inlined_at: Option<InlinedAt>,
}

impl ScopeData {
    /// An ordinary lexical scope with no inlining chain link.
    pub const fn new(parent: Option<u32>, span: Option<SourceSpan>) -> Self {
        Self {
            parent,
            span,
            inlined_at: None,
        }
    }
}

/// One link of a lexical scope's inlining chain (WS4.19): the CALL SITE an
/// inlined callee's body was spliced in at, and which callee it was.
///
/// Both halves are required. `span` is the call site in the CALLER's source
/// (a `DW_AT_call_file` / `DW_AT_call_line` pair; `span.file` indexes
/// `Module.files` like every other span, and the validator range-checks it).
/// `callee` is the callee's human display path — a `Function.display_path`
/// when the callee is a function of this module, or any producer-side path
/// (a Clean declaration name) when it is not — and must be non-empty: a link
/// that cannot name what was inlined is refused, never spelled as "unknown"
/// and called complete.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct InlinedAt {
    /// The call site, in the caller's source.
    pub span: SourceSpan,
    /// Display path of the inlined callee.
    pub callee: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn value_id_construction_and_index() {
        let v = ValueId::new(42);
        assert_eq!(v.index(), 42);
        assert_eq!(v.as_usize(), 42);
        assert_eq!(v.0, 42);
    }

    #[test]
    fn block_id_construction_and_index() {
        let b = BlockId::new(7);
        assert_eq!(b.index(), 7);
        assert_eq!(b.as_usize(), 7);
    }

    #[test]
    fn func_id_construction_and_index() {
        let f = FuncId::new(3);
        assert_eq!(f.index(), 3);
        assert_eq!(f.as_usize(), 3);
    }

    #[test]
    fn struct_id_construction() {
        let s = StructId::new(1);
        assert_eq!(s.index(), 1);
    }

    #[test]
    fn ty_id_construction() {
        let t = TyId::new(5);
        assert_eq!(t.index(), 5);
    }

    #[test]
    fn func_ty_id_construction() {
        let ft = FuncTyId::new(0);
        assert_eq!(ft.index(), 0);
    }

    #[test]
    fn proof_id_and_tag_construction() {
        let p = ProofId::new(10);
        assert_eq!(p.index(), 10);
        let t = ProofTag::new(99);
        assert_eq!(t.index(), 99);
    }

    #[test]
    fn record_id_construction() {
        let r = RecordId::new(7);
        assert_eq!(r.index(), 7);
        assert_eq!(r.as_usize(), 7);
        assert_eq!(format!("{:?}", r), "RecordId(7)");
        assert_eq!(format!("{}", r), "7");
    }

    #[test]
    fn global_id_construction() {
        let g = GlobalId::new(4);
        assert_eq!(g.index(), 4);
        assert_eq!(g.as_usize(), 4);
        assert_eq!(format!("{g:?}"), "GlobalId(4)");
        assert_eq!(format!("{g}"), "4");
    }

    #[test]
    fn closure_ty_id_construction() {
        let c = ClosureTyId::new(3);
        assert_eq!(c.index(), 3);
        assert_eq!(format!("{:?}", c), "ClosureTyId(3)");
    }

    #[test]
    fn record_and_closure_ids_are_distinct_types() {
        // They share a u32 payload but are distinct Rust types.
        let r = RecordId::new(0);
        let c = ClosureTyId::new(0);
        assert_eq!(r.index(), c.index());
    }

    #[test]
    fn display_outputs_raw_index() {
        assert_eq!(format!("{}", ValueId::new(0)), "0");
        assert_eq!(format!("{}", ValueId::new(123)), "123");
        assert_eq!(format!("{}", BlockId::new(5)), "5");
        assert_eq!(format!("{}", FuncId::new(2)), "2");
    }

    #[test]
    fn debug_includes_type_name() {
        assert_eq!(format!("{:?}", ValueId::new(1)), "ValueId(1)");
        assert_eq!(format!("{:?}", BlockId::new(2)), "BlockId(2)");
        assert_eq!(format!("{:?}", FuncId::new(3)), "FuncId(3)");
    }

    #[test]
    fn ids_are_ordered() {
        assert!(ValueId::new(0) < ValueId::new(1));
        assert!(BlockId::new(5) > BlockId::new(3));
        assert_eq!(FuncId::new(2), FuncId::new(2));
    }

    #[test]
    fn ids_are_copy() {
        let a = ValueId::new(1);
        let b = a; // Copy
        assert_eq!(a, b);
    }

    #[test]
    fn binding_frame_id_construction() {
        let bf = BindingFrameId::new(7);
        assert_eq!(bf.index(), 7);
        assert_eq!(bf.as_usize(), 7);
        assert_eq!(format!("{bf}"), "7");
        assert_eq!(format!("{bf:?}"), "BindingFrameId(7)");
    }

    #[test]
    fn pred_and_univ_id_construction() {
        let p = PredId::new(3);
        assert_eq!(p.index(), 3);
        assert_eq!(p.as_usize(), 3);
        assert_eq!(format!("{p:?}"), "PredId(3)");
        assert_eq!(format!("{p}"), "3");
        let u = UnivId::new(0);
        assert_eq!(u.index(), 0);
        assert_eq!(format!("{u:?}"), "UnivId(0)");
        // Distinct Rust types over the same payload, exactly like
        // RecordId/ClosureTyId above.
        assert_eq!(PredId::new(1).index(), UnivId::new(1).index());
    }

    /// The tested twin of the fresh-id rule's three decision tables, at every
    /// boundary row gate 13 proves (`laws::fresh_*`, crates/trust-ir-laws)
    /// and a few rows beside them. A test samples; the laws are about every
    /// `u32`.
    #[test]
    fn fresh_id_tables_hold_every_boundary_row() {
        // The exhaustion row: an id has a successor exactly below u32::MAX.
        assert!(!fresh_id_has_successor(u32::MAX));
        assert!(fresh_id_has_successor(u32::MAX - 1));
        assert!(fresh_id_has_successor(0));
        // The run room: a run ending `extra` past its first id fits exactly
        // when `extra` is at most the room above that id.
        for room in [0, 1, u32::MAX - 1, u32::MAX] {
            assert!(fresh_run_fits(0, room), "a one-id run fits anywhere");
            assert!(fresh_run_fits(room, room), "a run filling the room fits");
        }
        // The full room (a row the cursor never asks: a run's count is a u32,
        // so its `extra` is at most u32::MAX - 1).
        assert!(fresh_run_fits(u32::MAX, u32::MAX), "the full room");
        assert!(!fresh_run_fits(1, 0), "two ids from u32::MAX");
        assert!(!fresh_run_fits(u32::MAX, u32::MAX - 1));
        // The bound: strictly below, so the bound's own id is refused.
        assert!(!fresh_id_below(0xE000_0000, 0xE000_0000));
        assert!(fresh_id_below(0xDFFF_FFFF, 0xE000_0000));
        assert!(!fresh_id_below(0, 0));
        assert!(!fresh_id_below(u32::MAX, u32::MAX));
    }

    /// The cursor DECIDES by the three tables, at every boundary id: what
    /// `take`, `after`, `take_run`, `take_run_below` and `span` do is what
    /// the tables say, never an independent spelling of the same bound.
    /// Mutation check (2026-10-01): cutting `successor`'s, `run_last`'s or
    /// `span`'s read of its table (the value step then wraps) turns this red,
    /// and so does `after`'s max with its operands swapped or the bounded run
    /// admitting its bound. A table edit the cursor follows (the strict room)
    /// is seen by `fresh_id_tables_hold_every_boundary_row` instead.
    #[test]
    fn the_cursor_decides_by_the_fresh_id_tables() {
        let ids_at_the_edges = [
            0,
            1,
            7,
            0xDFFF_FFFF,
            0xE000_0000,
            u32::MAX - 2,
            u32::MAX - 1,
            u32::MAX,
        ];
        for id in ids_at_the_edges {
            // `take` hands out `id`; the cursor survives exactly when `id`
            // has a successor.
            let mut ids = FreshIds::<ValueId>::after(id.checked_sub(1).map(ValueId::new));
            assert_eq!(ids.take(), Ok(ValueId::new(id)));
            assert_eq!(
                ids.is_exhausted(),
                !fresh_id_has_successor(id),
                "take at {id}"
            );
            // `after`: a used id leaves the cursor where it is exactly when
            // it is below the cursor; otherwise the cursor is its successor.
            for cursor in ids_at_the_edges {
                let before =
                    FreshIds::<ValueId>::after(cursor.checked_sub(1).map(ValueId::new)).peek();
                let used = FreshIds::after(
                    cursor
                        .checked_sub(1)
                        .map(ValueId::new)
                        .into_iter()
                        .chain([ValueId::new(id)]),
                );
                if fresh_id_below(id, cursor) {
                    assert_eq!(used.peek(), before, "after({id}) below the cursor {cursor}");
                } else if fresh_id_has_successor(id) {
                    assert_eq!(
                        used.peek(),
                        Some(ValueId::new(id + 1)),
                        "after({id}) at or above {cursor}"
                    );
                } else {
                    assert!(used.is_exhausted(), "after(u32::MAX)");
                }
            }
            // `take_run` from `id`: a run ending `extra` past it is taken
            // exactly when the table says it fits the room above `id`.
            let room = u32::MAX - id;
            for extra in [
                0,
                1,
                2,
                room.saturating_sub(1),
                room,
                room.saturating_add(1),
            ] {
                let Some(count) = extra.checked_add(1) else {
                    continue;
                };
                let mut ids = FreshIds::<BlockId>::after(id.checked_sub(1).map(BlockId::new));
                let taken = ids.take_run(count);
                assert_eq!(
                    taken.is_ok(),
                    fresh_run_fits(extra, room),
                    "take_run({count}) at {id}"
                );
                // ... and inside a bound, exactly when its last id is below it.
                let mut bounded = FreshIds::<BlockId>::after(id.checked_sub(1).map(BlockId::new));
                let below = bounded.take_run_below(count, 0xE000_0000);
                let expected =
                    fresh_run_fits(extra, room) && fresh_id_below(id + extra, 0xE000_0000);
                assert_eq!(
                    below.is_ok(),
                    expected,
                    "take_run_below({count}, 0xE000_0000) at {id}"
                );
            }
            // `span(first, id)`: empty exactly when `id` is below `first`,
            // and refused when its count is the whole space.
            for first in ids_at_the_edges {
                let span = IdRun::<BlockId>::span(first, id);
                if fresh_id_below(id, first) {
                    assert!(span.is_none(), "span({first}, {id}) is empty");
                } else {
                    let width = id - first;
                    assert_eq!(
                        span.is_some(),
                        fresh_id_has_successor(width),
                        "span({first}, {id})"
                    );
                }
            }
        }
    }

    /// The one fresh-id rule (r11 item 2 root R1): one past the HIGHEST id in
    /// use, refused — never wrapped — at `u32::MAX`, and every run boundary
    /// all-or-nothing. Mutation check (2026-10-01): with `successor`'s read of
    /// [`fresh_id_has_successor`] cut, or that table admitting `u32::MAX`, the
    /// cursor steps from `u32::MAX` onto id 0 and the exhaustion assertions go
    /// red; with `run_last`'s read of [`fresh_run_fits`] cut, a run past the
    /// room is taken and the run assertions go red.
    #[test]
    fn fresh_ids_are_one_past_the_highest_and_never_wrap() {
        let exhausted = IdSpaceExhausted { space: "ValueId" };
        assert_eq!(IdSpaceExhausted::of::<ValueId>(), exhausted);

        // `after`: one past the highest, never the last or a gap.
        assert_eq!(FreshIds::<ValueId>::after([]).peek(), Some(ValueId::new(0)));
        assert_eq!(
            FreshIds::after([ValueId::new(7), ValueId::new(3)]).peek(),
            Some(ValueId::new(8))
        );
        let mut at_max = FreshIds::after([ValueId::new(0), ValueId::new(u32::MAX)]);
        assert!(at_max.is_exhausted());
        assert_eq!(at_max.peek(), None);
        assert_eq!(at_max.take(), Err(exhausted));
        // `u32::MAX` anywhere in the set is absorbing, whatever follows it.
        assert!(FreshIds::after([ValueId::new(u32::MAX), ValueId::new(1)]).is_exhausted());

        // `take` at the cliff: hands out u32::MAX once, then refuses forever.
        let mut ids = FreshIds::after([ValueId::new(u32::MAX - 1)]);
        assert_eq!(ids.take(), Ok(ValueId::new(u32::MAX)));
        assert_eq!(ids.take(), Err(exhausted));
        assert_eq!(ids.take(), Err(exhausted));
        assert_eq!(ids, FreshIds::after([ValueId::new(u32::MAX)]));

        // `take_run`: 0 consumes nothing (even when exhausted), exactly
        // filling succeeds, one past refuses and leaves the cursor unchanged.
        let mut empty_from_exhausted = FreshIds::<ValueId>::after([ValueId::new(u32::MAX)]);
        let mut run = empty_from_exhausted
            .take_run(0)
            .expect("an empty run needs no id");
        assert_eq!(run.remaining(), 0);
        assert_eq!(run.take(), None);
        let mut ids = FreshIds::<ValueId>::after([ValueId::new(u32::MAX - 3)]);
        assert_eq!(ids.take_run(4), Err(exhausted));
        assert_eq!(ids.peek(), Some(ValueId::new(u32::MAX - 2)));
        let mut run = ids.take_run(3).expect("exactly the three ids left");
        assert!(ids.is_exhausted());
        assert_eq!(run.remaining(), 3);
        assert_eq!(run.take(), Some(ValueId::new(u32::MAX - 2)));
        assert_eq!(run.take(), Some(ValueId::new(u32::MAX - 1)));
        assert_eq!(run.take(), Some(ValueId::new(u32::MAX)));
        assert_eq!(run.remaining(), 0);
        assert_eq!(run.take(), None);

        // `take_run_below`: the run must end strictly below the bound.
        let mut ids = FreshIds::<BlockId>::after([BlockId::new(9)]);
        assert_eq!(
            ids.take_run_below(3, 12),
            Err(IdSpaceExhausted { space: "BlockId" })
        );
        assert_eq!(ids.peek(), Some(BlockId::new(10)));
        let mut run = ids
            .take_run_below(2, 12)
            .expect("ids 10 and 11 are below 12");
        assert_eq!(run.take(), Some(BlockId::new(10)));
        assert_eq!(run.take(), Some(BlockId::new(11)));
        assert_eq!(ids.peek(), Some(BlockId::new(12)));
        assert!(ids.take_run_below(1, 12).is_err());
        assert!(ids.take_run_below(0, 12).is_ok());

        // `span`: a fixed range, its end included; empty and full-space
        // ranges are refused by name (`None`), never wrapped.
        let mut span = IdRun::<BlockId>::span(u32::MAX - 1, u32::MAX).expect("two ids");
        assert_eq!(span.remaining(), 2);
        assert_eq!(span.take(), Some(BlockId::new(u32::MAX - 1)));
        assert_eq!(span.take(), Some(BlockId::new(u32::MAX)));
        assert_eq!(span.take(), None);
        assert_eq!(
            IdRun::<BlockId>::span(5, 5).map(|run| run.remaining()),
            Some(1)
        );
        assert!(IdRun::<BlockId>::span(6, 5).is_none());
        assert!(IdRun::<BlockId>::span(0, u32::MAX).is_none());
        assert_eq!(
            IdRun::<BlockId>::span(1, u32::MAX).map(|run| run.remaining()),
            Some(u32::MAX)
        );
    }

    /// T-A7: the table-id rule. The last index `u32::MAX` names an id; one past
    /// it is refused by name, never truncated onto slot 0. Mutation check:
    /// `index as u32` hands out id 0 for `u32::MAX + 1` and the refusal
    /// assertions go red.
    #[test]
    fn table_id_is_the_index_or_a_typed_refusal() {
        assert_eq!(table_index(0, "files"), Ok(0));
        assert_eq!(table_index(u32::MAX as usize, "files"), Ok(u32::MAX));
        assert_eq!(
            table_index(u32::MAX as usize + 1, "files"),
            Err(IdSpaceExhausted { space: "files" })
        );
        assert_eq!(table_id::<TyId>(7), Ok(TyId::new(7)));
        assert_eq!(table_id::<TyId>(u32::MAX as usize), Ok(TyId::new(u32::MAX)));
        assert_eq!(
            table_id::<TyId>(u32::MAX as usize + 1),
            Err(IdSpaceExhausted::of::<TyId>())
        );
        assert_eq!(
            table_id::<ImportId>(usize::MAX),
            Err(IdSpaceExhausted { space: "ImportId" })
        );
    }

    #[test]
    fn source_span_construction() {
        let span = SourceSpan {
            file: 1,
            line: 42,
            col: 10,
        };
        assert_eq!(span.file, 1);
        assert_eq!(span.line, 42);
        assert_eq!(span.col, 10);
    }
}
