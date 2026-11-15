// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Typed effect summaries (roadmap WS1.14, F-013; wire v59).
//!
//! A [`crate::FunctionSummary`] states what a separately compiled caller may
//! ASSUME about a callee's result. Before v59 it said nothing about what the
//! call DOES to memory, so a caller had to havoc the whole world across every
//! call: no fact about any memory survived one. [`EffectSummary`] is the frame
//! half of the contract — the memory a call may read and write, and whether it
//! allocates, frees, unwinds or performs I/O — carried as
//! [`crate::FunctionSummary::effects`].
//!
//! # What a place means
//!
//! [`EffectPlace::ParamPointee`] is the memory reached through a pointer
//! DERIVED from formal parameter `index`'s entry value — by `GEP`, `PtrData`,
//! `Copy`, `Select`, a `PtrToPtr` cast or a borrow — at ANY offset: the
//! allocation that parameter's provenance grants, never a byte range (the
//! reference interpreter's pointers carry their allocation, so an access
//! through a derived pointer reaches that allocation or faults). It is one
//! level deep: memory reached by LOADING a pointer out of that allocation is
//! not in it. [`EffectPlace::Global`] is the storage of one module global,
//! again at any offset.
//!
//! # `None` is never a wildcard
//!
//! `FunctionSummary.effects == None` means UNRECORDED: a caller havocs the
//! world across the call, exactly as before v59. `Some(EffectSummary::pure())`
//! is the affirmative claim "touches no caller-visible memory". The two are
//! never conflated, the same rule `proved` / `backed_by` / `site` follow.
//!
//! # Who checks it
//!
//! `trust-ir` carries the claim; `trust_ir_build::validate_module` decides it.
//! On a DEFINITION the body must be covered by the summary under a syntactic,
//! sound over-approximation (`EffectSummaryViolated`). On a body-less
//! DECLARATION the summary is a claim with no body to check: a caller's frame
//! check may use it only when the declaration's summary is authenticated
//! through `backed_by` by `validate_linked_module` (whose restatement then
//! requires the far effects to be restated exactly); otherwise the caller
//! treats it as `None`.

use crate::value::GlobalId;

mod observed;
mod observed_coverage;

/// One region of caller-visible memory (v59, [`EffectSet::Places`]).
///
/// Variant order is the canonical order of a [`EffectSet::Places`] list
/// (the derived `Ord`): every `ParamPointee` ascending by index, then every
/// `Global` ascending by id. Wire tags: `ParamPointee` 0, `Global` 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum EffectPlace {
    /// The allocation reached through a pointer derived from formal parameter
    /// `index` (the same index space as `FuncTy::params` and
    /// [`crate::proof::ClausePlace::Param`]), at any offset, one level deep.
    ParamPointee { index: u32 },
    /// The storage of module global `id` (this module's `Module::globals`),
    /// at any offset. A global has no identity across an import edge at this
    /// version, so a cross-crate restatement may not name one.
    Global(GlobalId),
}

/// A set of caller-visible memory regions (v59).
///
/// Wire tags: `Nothing` 0, `Places` 1 (a count, then the places), `Everything`
/// 2. There is exactly ONE spelling of each set: `Places` is canonical only
/// when it is non-empty and strictly ascending (no duplicate), so the empty set
/// is `Nothing`. Every decoder refuses any other spelling on read, and the
/// validator refuses one built in memory. That makes structural equality set
/// equality, which the cross-crate restatement relies on.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum EffectSet {
    /// No caller-visible memory.
    Nothing,
    /// At most these regions: non-empty, strictly ascending. Every decoder
    /// (binary, JSON, MessagePack) refuses any other spelling on read.
    Places(
        #[cfg_attr(feature = "serde", serde(deserialize_with = "canonical_places"))]
        Vec<EffectPlace>,
    ),
    /// Any memory at all — the havoc side.
    Everything,
}

impl EffectSet {
    /// A canonical set holding exactly `places`: `Nothing` when empty, else
    /// the places sorted with duplicates removed.
    #[must_use]
    pub fn of(places: impl IntoIterator<Item = EffectPlace>) -> Self {
        let mut places: Vec<EffectPlace> = places.into_iter().collect();
        places.sort_unstable();
        places.dedup();
        if places.is_empty() {
            Self::Nothing
        } else {
            Self::Places(places)
        }
    }

    /// True iff this is the ONE spelling of its set: `Places` non-empty and
    /// strictly ascending. `Nothing` and `Everything` are always canonical.
    #[must_use]
    pub fn is_canonical(&self) -> bool {
        match self {
            Self::Nothing | Self::Everything => true,
            Self::Places(places) => places_are_canonical(places),
        }
    }

    /// Does this set contain every region `other` may name?
    ///
    /// `Everything` covers every set; only `Everything` covers `Everything`;
    /// `Places(a)` covers `Places(b)` iff every place of `b` is in `a`; every
    /// set covers `Nothing`. Correct on non-canonical spellings too (it is a
    /// set comparison, not a structural one).
    #[must_use]
    pub fn covers(&self, other: &EffectSet) -> bool {
        match (self, other) {
            (Self::Everything, _) | (_, Self::Nothing) => true,
            (_, Self::Everything) => false,
            (Self::Nothing, Self::Places(theirs)) => theirs.is_empty(),
            (Self::Places(ours), Self::Places(theirs)) => {
                theirs.iter().all(|place| ours.contains(place))
            }
        }
    }

    /// The places this set names explicitly (empty for `Nothing` and
    /// `Everything`).
    #[must_use]
    pub fn places(&self) -> &[EffectPlace] {
        match self {
            Self::Places(places) => places,
            Self::Nothing | Self::Everything => &[],
        }
    }
}

/// Whether `places` is the ONE spelling of a non-empty set: non-empty and
/// strictly ascending (so no duplicate).
fn places_are_canonical(places: &[EffectPlace]) -> bool {
    !places.is_empty() && places.windows(2).all(|pair| pair[0] < pair[1])
}

/// Serde read of `EffectSet::Places`: a non-canonical place list is refused on
/// read (`docs/SPEC_RATIFICATIONS.md` §3, one spelling per construct), exactly
/// as the binary decoder refuses it — so no decoder hands the validator, a
/// digest or a structural comparison two spellings of one set.
#[cfg(feature = "serde")]
fn canonical_places<'de, D>(de: D) -> Result<Vec<EffectPlace>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    let places = <Vec<EffectPlace> as serde::Deserialize>::deserialize(de)?;
    if !places_are_canonical(&places) {
        return Err(serde::de::Error::custom(format!(
            "non-canonical EffectSet::Places({places:?}): a place list must be non-empty and \
             strictly ascending, and the empty set is spelled EffectSet::Nothing (one-spelling \
             rule, SPEC_RATIFICATIONS §3)"
        )));
    }
    Ok(places)
}

/// What one call may do to the world (v59, [`crate::FunctionSummary::effects`]).
///
/// Every field is an UPPER bound a caller may rely on: the call reads at most
/// `reads`, writes at most `writes`, and performs an allocation, a free, an
/// unwinding exit or an environment interaction only when the matching flag
/// is set. A `true` flag or an `Everything` side is always a sound claim; a
/// tighter one is checked against the body by `trust_ir_build`.
///
/// There is deliberately no `Default`: the all-false, `Nothing`/`Nothing`
/// value is the strongest possible claim, and a derive would make it the
/// accidental one. Spell it [`EffectSummary::pure`], and the havoc summary
/// [`EffectSummary::top`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct EffectSummary {
    /// Memory the call may read (`Load`, `AtomicLoad`, the read half of a
    /// read-modify-write, a copy's source, a callee's reads).
    pub reads: EffectSet,
    /// Memory the call may write (`Store`, `AtomicStore`, `AtomicRMW`,
    /// `CmpXchg`, a copy's or fill's destination, a callee's writes).
    pub writes: EffectSet,
    /// The call may allocate heap memory (`HeapAlloc`).
    pub allocates: bool,
    /// The call may free heap memory (`Dealloc`, `Release`, `Drop`).
    pub frees: bool,
    /// The call may exit by unwinding (`Invoke`, `Resume`, or a callee that
    /// may unwind).
    pub may_unwind: bool,
    /// The call may interact with the environment through code the module
    /// cannot see into (a call to a body-less declaration with no admissible
    /// summary, an indirect call, an opaque dialect op).
    pub io: bool,
}

impl EffectSummary {
    /// The strongest claim: no caller-visible memory read or written, and
    /// no allocation, free, unwinding exit or I/O.
    #[must_use]
    pub fn pure() -> Self {
        Self {
            reads: EffectSet::Nothing,
            writes: EffectSet::Nothing,
            allocates: false,
            frees: false,
            may_unwind: false,
            io: false,
        }
    }

    /// The weakest claim: any memory read and written, and every flag set.
    /// Always a sound summary of any body; what a caller assumes for a callee
    /// whose effects it cannot rely on.
    #[must_use]
    pub fn top() -> Self {
        Self {
            reads: EffectSet::Everything,
            writes: EffectSet::Everything,
            allocates: true,
            frees: true,
            may_unwind: true,
            io: true,
        }
    }

    /// Set `reads`.
    #[must_use]
    pub fn reading(mut self, reads: EffectSet) -> Self {
        self.reads = reads;
        self
    }

    /// Set `writes`.
    #[must_use]
    pub fn writing(mut self, writes: EffectSet) -> Self {
        self.writes = writes;
        self
    }

    /// Does this summary admit every effect `other` states? Side by side:
    /// each set covers the other's, and each flag set in `other` is set here.
    #[must_use]
    pub fn covers(&self, other: &EffectSummary) -> bool {
        self.reads.covers(&other.reads)
            && self.writes.covers(&other.writes)
            && (self.allocates || !other.allocates)
            && (self.frees || !other.frees)
            && (self.may_unwind || !other.may_unwind)
            && (self.io || !other.io)
    }

    /// True iff either side names a module global — which has no identity
    /// across an import edge at this version.
    #[must_use]
    pub fn names_a_global(&self) -> bool {
        self.reads
            .places()
            .iter()
            .chain(self.writes.places())
            .any(|place| matches!(place, EffectPlace::Global(_)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(index: u32) -> EffectPlace {
        EffectPlace::ParamPointee { index }
    }

    #[test]
    fn of_is_the_canonical_spelling() {
        assert_eq!(EffectSet::of([]), EffectSet::Nothing);
        let g = EffectPlace::Global(GlobalId::new(2));
        let set = EffectSet::of([g, p(1), p(0), p(1)]);
        assert_eq!(set, EffectSet::Places(vec![p(0), p(1), g]));
        assert!(set.is_canonical());
        assert!(!EffectSet::Places(vec![]).is_canonical());
        assert!(!EffectSet::Places(vec![p(1), p(0)]).is_canonical());
        assert!(!EffectSet::Places(vec![p(0), p(0)]).is_canonical());
    }

    #[test]
    fn covers_is_set_inclusion() {
        let p0 = EffectSet::of([p(0)]);
        let p01 = EffectSet::of([p(0), p(1)]);
        assert!(EffectSet::Everything.covers(&EffectSet::Everything));
        assert!(EffectSet::Everything.covers(&p01));
        assert!(!p01.covers(&EffectSet::Everything));
        assert!(p01.covers(&p0));
        assert!(!p0.covers(&p01));
        assert!(p0.covers(&EffectSet::Nothing));
        assert!(!EffectSet::Nothing.covers(&p0));
        assert!(EffectSet::Nothing.covers(&EffectSet::Places(vec![])));
    }

    #[test]
    fn summary_cover_is_per_side_and_per_flag() {
        let top = EffectSummary::top();
        let pure = EffectSummary::pure();
        assert!(top.covers(&pure) && top.covers(&top) && pure.covers(&pure));
        assert!(!pure.covers(&top));
        let mut io = EffectSummary::pure();
        io.io = true;
        assert!(!pure.covers(&io));
        assert!(io.covers(&pure));
        let writer = EffectSummary::pure().writing(EffectSet::of([p(0)]));
        assert!(!pure.covers(&writer));
        assert!(!writer.names_a_global());
        let global_writer =
            EffectSummary::pure().writing(EffectSet::of([EffectPlace::Global(GlobalId::new(0))]));
        assert!(global_writer.names_a_global());
    }
}
