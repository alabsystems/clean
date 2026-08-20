// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The **typed value model**: a decidable predicate lattice that lets an
//! encoding CONVENTION live in the type instead of in a producer-side map.
//!
//! # Why this exists
//!
//! trust-ir declares aggregate surfaces (`Set`/`Sequence`/`Record`, binding
//! frames) that a backend may refuse. A consumer that hits that refusal
//! hand-encodes every sum, product, function and set into anonymous integer
//! lanes and records *which convention each lane obeys* in a side map. In such
//! an encoding **the absence of a fact changes MEANING, not precision**:
//! dropping "lane 7 is an INDEX into universe U" does not widen the value to
//! "some index" — it silently REINTERPRETS the integer under the raw member
//! convention. Two shipped miscompiles are that single mechanism:
//!
//! * a union-key row off-by-one — an index used where a raw member was
//!   expected (`n` where `n-1` was meant);
//! * a control-flow join where two carriers over an *identical* universe that
//!   differed only in which proof cited them failed to merge; the shape was
//!   dropped and the value reverted to the raw convention.
//!
//! Proof cannot reach either, because the property "this integer is an INDEX
//! into `U`, not a MEMBER of `U`" was **not statable** in the IR. Proof is
//! downstream of expressiveness.
//!
//! # The thesis
//!
//! Put the encoding convention IN THE TYPE ([`crate::Ty::Refine`]), so that
//! **dropping a fact yields [`Pred::Top`]** — and `Top` implies nothing
//! non-trivial, so the loss surfaces as a *failed implication at the
//! consumption site* rather than a silent reinterpretation.
//!
//! # The two load-bearing design rules
//!
//! 1. **Join is disjunction, and a MISSING predicate is `Top` — never
//!    `Bottom`, never "unknown-but-assume-ok".** Every operation here may only
//!    move *up* the lattice (weaker) when it is unsure. [`Pred::Top`] is where
//!    a lost fact lands.
//! 2. **[`PredTable::implies`] is decidable, total and fast** — interval
//!    containment, finite-set subset, universe+space comparison; microseconds,
//!    no solver. It returns `true` ONLY when the implication genuinely holds;
//!    **when unsure it returns `false`**. A false negative costs a spurious
//!    validation error (loud); a false positive would be a miscompile
//!    (silent). Every arm below is written to pay only the loud cost.
//!
//! # Content interning
//!
//! Predicates and universes live in module-level tables
//! ([`crate::Module::predicates`], [`crate::Module::universes`]) that are
//! **content-interned**: identical content is the identical id, regardless of
//! which proof, pass or frontend minted it. That is the direct, structural fix
//! for the join-drop class — two carriers over the same universe cannot
//! disagree on identity, so the join cannot fail to merge them. The validator
//! ENFORCES the invariant (a duplicate table entry is a hard error), so a
//! hand-built or decoded module cannot smuggle in the un-interned shape.
//!
//! # Representation preservation
//!
//! A `Refine(b, p)` has EXACTLY the representation of `b`. Nothing in this
//! module can move a byte: layout, `bit_width`, interpretation and codegen all
//! delegate to the base type. The predicate is proof surface only.

use crate::constant::Constant;
use crate::value::{PredId, UnivId};

/// How many members a `FiniteSet` / `Universe::Members` extension may carry
/// before the validator calls it a cardinality blowup.
///
/// The lattice is meant to be decided in *microseconds*; an enumeration larger
/// than this is a producer bug (or an attempt to encode a semantic constraint
/// as an extension) and must be spelled as an `Interval`/`IntRange` instead.
pub const MAX_ENUMERATED_MEMBERS: usize = 4096;

/// How many conjuncts/disjuncts a single `Conj`/`Disj` node may carry.
pub const MAX_CONNECTIVE_ARITY: usize = 64;

/// The schema name under which a [`Pred`] travels in the existing
/// [`crate::proof::ProofFormula`] channel.
pub const PRED_FORMULA_SCHEMA: &str = "trust-ir.Pred@1";

/// Recursion cap for the decision procedures.
///
/// The validator enforces that a child id is strictly less than its parent's,
/// which makes the predicate graph acyclic by construction — but `implies` is
/// callable on a not-yet-validated (e.g. freshly decoded, adversarial) module,
/// and a verified IR may not blow the stack on bad input. Past the cap the
/// answer is "undecided", which is `false`/`None`: fail loud, never guess.
const MAX_PRED_DEPTH: u32 = 64;

/// Which **encoding convention** an integer carrier obeys with respect to a
/// universe.
///
/// This is the distinction that makes the index-vs-member miscompile class
/// EXPRESSIBLE. Both spaces are carried by the same machine integer, and that
/// is exactly why the fact must live in the type: nothing about the
/// representation distinguishes them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Space {
    /// The value is a **0-based ordinal INDEX** into the universe's canonical
    /// member ordering: `0 <= self < |U|`. It is NOT a member of `U` (unless
    /// `U` happens to also contain that ordinal, which is a coincidence of
    /// extension, never a fact this space asserts).
    ///
    /// # Denotation, and why the implication rule is stricter than it
    ///
    /// The NUMERIC denotation is exactly `0 <= self < |U|` — that and nothing
    /// more; an index carries no information about the member values. But an
    /// index is only *meaningful* against the ordering it indexes: "the 3rd
    /// entry of `U`" and "the 3rd entry of `V`" are different values whenever
    /// `U != V`, and reading one as the other is the same confusion class as
    /// reading an index as a member.
    ///
    /// [`PredTable::implies`] therefore treats `Index` as **extensional in the
    /// universe**: `InUniverse(U, Index)` entails `InUniverse(V, Index)` only
    /// when `U` and `V` have the SAME extension, never merely when
    /// `|U| <= |V|`. That is a deliberate INCOMPLETENESS with respect to the
    /// numeric denotation above (a cross-universe index implication is
    /// numerically sound and is refused anyway), paid in the loud direction:
    /// a spurious validation error, never a spurious acceptance.
    ///
    /// The numeric content is not lost by that refusal — it is simply spelled
    /// numerically. `InUniverse(U, Index)` still entails
    /// `Interval { lo: 0, hi: |U| - 1 }` and every wider interval, so a site
    /// that genuinely wants only "a number below `n`" says so with an
    /// `Interval` and is satisfied by an index into any universe of at most
    /// `n` members.
    Index,
    /// The value is a **MEMBER** of the universe: `self ∈ U`.
    Member,
}

impl core::fmt::Display for Space {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Space::Index => "index",
            Space::Member => "member",
        })
    }
}

// ---------------------------------------------------------------------------
// Canonical scalar-extension helpers
// ---------------------------------------------------------------------------

/// Total ordering key for the scalar constants a predicate extension may
/// carry. `None` for every non-scalar (aggregate, float, bytes, pointer-ish)
/// constant — those have no canonical total order the lattice can rely on, so
/// the validator rejects them inside an extension and the decision procedures
/// treat them as undecided.
///
/// Floats are deliberately excluded: NaN has no total order, and a lattice
/// that silently ordered it would be unsound at exactly one input.
pub fn constant_key(c: &Constant) -> Option<(u8, i128)> {
    match c {
        Constant::Int(v) => Some((0, *v)),
        Constant::Bool(b) => Some((1, i128::from(*b))),
        _ => None,
    }
}

/// Is `items` a canonical extension: non-empty, in-cap, all-scalar, strictly
/// ascending by [`constant_key`] (hence duplicate-free)?
pub fn members_are_canonical(items: &[Constant]) -> bool {
    if items.is_empty() || items.len() > MAX_ENUMERATED_MEMBERS {
        return false;
    }
    let mut prev: Option<(u8, i128)> = None;
    for c in items {
        let Some(key) = constant_key(c) else {
            return false;
        };
        if let Some(p) = prev
            && key <= p
        {
            return false;
        }
        prev = Some(key);
    }
    true
}

/// Sort + dedup an extension into canonical order. `None` if any element is
/// non-scalar, or the canonical result is empty / over cap.
pub fn canonicalize_members(items: impl IntoIterator<Item = Constant>) -> Option<Vec<Constant>> {
    let mut items: Vec<Constant> = items.into_iter().collect();
    if items.iter().any(|c| constant_key(c).is_none()) {
        return None;
    }
    items.sort_by_key(|c| constant_key(c).expect("scalar checked above"));
    items.dedup_by_key(|c| constant_key(c).expect("scalar checked above"));
    (!items.is_empty() && items.len() <= MAX_ENUMERATED_MEMBERS).then_some(items)
}

/// Membership test over a CANONICAL extension (binary search). Callers must
/// have established canonicality; a non-canonical slice answers `false`.
fn members_contain_key(items: &[Constant], key: (u8, i128)) -> bool {
    items
        .binary_search_by_key(&key, |c| constant_key(c).unwrap_or((u8::MAX, i128::MAX)))
        .is_ok()
}

/// Tightest inclusive integer bounds over an extension, or `None` when it is
/// non-canonical or not purely integral.
fn members_int_bounds(items: &[Constant]) -> Option<(i128, i128)> {
    if !members_are_canonical(items) {
        return None;
    }
    let mut lo = i128::MAX;
    let mut hi = i128::MIN;
    for c in items {
        match constant_key(c) {
            Some((0, v)) => {
                lo = lo.min(v);
                hi = hi.max(v);
            }
            _ => return None,
        }
    }
    (lo <= hi).then_some((lo, hi))
}

/// Is every element of `a` also in `b`? `false` whenever either side is
/// non-canonical (undecided ⇒ no implication).
fn members_subset(a: &[Constant], b: &[Constant]) -> bool {
    if !members_are_canonical(a) || !members_are_canonical(b) {
        return false;
    }
    a.iter().all(|c| match constant_key(c) {
        Some(key) => members_contain_key(b, key),
        None => false,
    })
}

/// Does a canonical extension contain every integer in `[lo, hi]`?
fn members_contain_interval(items: &[Constant], lo: i128, hi: i128) -> bool {
    if lo > hi {
        return true; // vacuous
    }
    if !members_are_canonical(items) {
        return false;
    }
    // Only decided for intervals that cannot exceed the extension's size; a
    // wider interval is answered `false` (undecided) rather than walked.
    let Some(span) = hi.checked_sub(lo) else {
        return false;
    };
    if span >= items.len() as i128 {
        return false;
    }
    (lo..=hi).all(|v| members_contain_key(items, (0, v)))
}

// ---------------------------------------------------------------------------
// Universe
// ---------------------------------------------------------------------------

/// A finite universe: the extension a [`Space`] is interpreted against.
///
/// **Identity is content, and content only.** A universe deliberately carries
/// NO name, no provenance and no citing-proof id: two universes with the same
/// extension are the same universe, which is precisely the property whose
/// absence caused the join-drop miscompile. Adding a descriptive field here
/// would reintroduce that bug, so don't.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Universe {
    /// Inclusive contiguous integer range `{lo, lo+1, ..., hi}`.
    /// Well-formed iff `lo <= hi`.
    IntRange { lo: i128, hi: i128 },
    /// Explicit member list in **canonical order**: strictly ascending by
    /// [`constant_key`], deduplicated, every element scalar, non-empty, within
    /// [`MAX_ENUMERATED_MEMBERS`].
    Members(Vec<Constant>),
}

impl Universe {
    /// Canonical range constructor. `None` for an empty range.
    pub fn range(lo: i128, hi: i128) -> Option<Self> {
        (lo <= hi).then_some(Universe::IntRange { lo, hi })
    }

    /// Canonicalizing member constructor: sorts and dedups.
    pub fn members(items: impl IntoIterator<Item = Constant>) -> Option<Self> {
        canonicalize_members(items).map(Universe::Members)
    }

    /// Number of members. `None` when the count does not fit `u128` (a
    /// structurally legal but practically absurd range) or the universe is
    /// non-canonical.
    pub fn cardinality(&self) -> Option<u128> {
        match self {
            Universe::IntRange { lo, hi } => {
                if lo > hi {
                    return None;
                }
                // `hi - lo` can exceed i128; compute the span in two's
                // complement and read it as u128, which is exact for lo <= hi.
                let span = hi.wrapping_sub(*lo) as u128;
                span.checked_add(1)
            }
            Universe::Members(items) => members_are_canonical(items).then_some(items.len() as u128),
        }
    }

    /// Structural well-formedness: canonical ordering, non-empty, in-cap.
    pub fn is_canonical(&self) -> bool {
        match self {
            Universe::IntRange { lo, hi } => lo <= hi,
            Universe::Members(items) => members_are_canonical(items),
        }
    }

    /// Does this universe contain every integer in the inclusive interval
    /// `[lo, hi]`? `false` whenever undecided.
    pub fn contains_interval(&self, lo: i128, hi: i128) -> bool {
        match self {
            Universe::IntRange { lo: ulo, hi: uhi } => {
                if lo > hi {
                    return true;
                }
                ulo <= uhi && *ulo <= lo && hi <= *uhi
            }
            Universe::Members(items) => members_contain_interval(items, lo, hi),
        }
    }

    /// Is every member of `self` also a member of `other`?
    pub fn is_subset_of(&self, other: &Universe) -> bool {
        if !self.is_canonical() || !other.is_canonical() {
            return false;
        }
        match (self, other) {
            (Universe::IntRange { lo, hi }, Universe::IntRange { lo: olo, hi: ohi }) => {
                olo <= lo && hi <= ohi
            }
            (Universe::IntRange { lo, hi }, Universe::Members(items)) => {
                members_contain_interval(items, *lo, *hi)
            }
            (Universe::Members(items), Universe::IntRange { lo, hi }) => {
                items.iter().all(|c| match constant_key(c) {
                    Some((0, v)) => *lo <= v && v <= *hi,
                    _ => false,
                })
            }
            (Universe::Members(a), Universe::Members(b)) => members_subset(a, b),
        }
    }

    /// Tightest inclusive integer interval containing every member, when the
    /// universe is integral and canonical.
    pub fn integer_bounds(&self) -> Option<(i128, i128)> {
        match self {
            Universe::IntRange { lo, hi } => (lo <= hi).then_some((*lo, *hi)),
            Universe::Members(items) => members_int_bounds(items),
        }
    }
}

impl core::fmt::Display for Universe {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Universe::IntRange { lo, hi } => write!(f, "{lo}..={hi}"),
            Universe::Members(items) => {
                f.write_str("{")?;
                for (i, c) in items.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{c}")?;
                }
                f.write_str("}")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Pred
// ---------------------------------------------------------------------------

/// A decidable predicate over ONE distinguished free variable — `self`, the
/// refined value.
///
/// The lattice order is implication: `a ⊑ b` iff [`PredTable::implies`]
/// `(a, b)`. [`Pred::Top`] is the greatest element ("no information", where a
/// lost fact lands) and [`Pred::Bottom`] the least ("unsatisfiable").
///
/// Children of `Conj`/`Disj` are [`PredId`]s into the module's interned
/// predicate table; because interning is append-only, a child's id is always
/// STRICTLY LESS than its parent's, so the predicate graph is acyclic by
/// construction. The validator enforces that ordering rather than assuming it,
/// and the decision procedures additionally carry a depth cap so an
/// unvalidated module cannot blow the stack.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Pred {
    /// `lo <= self <= hi` (inclusive). Well-formed iff `lo <= hi`.
    ///
    /// This is a RAW NUMERIC fact and deliberately carries no [`Space`]: it
    /// says nothing about which convention the integer obeys. That is the
    /// point — an interval is exactly what a producer knows when it has *not*
    /// recorded a convention, and it must never imply `InUniverse(_, Member)`
    /// by accident.
    Interval { lo: i128, hi: i128 },
    /// `self ∈ {c0, c1, ...}`. Canonical: strictly ascending by
    /// [`constant_key`], deduped, non-empty, scalar elements only.
    FiniteSet(Vec<Constant>),
    /// The convention carrier: `self` is an [`Space::Index`] into, or a
    /// [`Space::Member`] of, universe `u`.
    InUniverse(UnivId, Space),
    /// `self != 0`.
    NonZero,
    /// `self` is not the null pointer.
    NonNull,
    /// All of the listed predicates hold. Canonical: sorted, deduped, arity in
    /// `2..=MAX_CONNECTIVE_ARITY`, every child id strictly less than this
    /// node's own id.
    Conj(Vec<PredId>),
    /// At least one of the listed predicates holds. Same canonicality rules as
    /// [`Pred::Conj`]. This is what [`PredTable::join_pred`] produces when it
    /// can keep a merge exact.
    Disj(Vec<PredId>),
    /// **No information.** Where a dropped fact lands. `Top` implies only
    /// `Top`, which is the whole point: a consumption site that requires
    /// anything non-trivial REJECTS a `Top` carrier instead of reinterpreting
    /// it.
    Top,
    /// Unsatisfiable. Implies everything (vacuously). A producer should not
    /// mint it except as an explicit "this path is dead" marker.
    Bottom,
}

impl Pred {
    /// Canonicalizing finite-set constructor: sorts and dedups.
    pub fn finite_set(items: impl IntoIterator<Item = Constant>) -> Option<Self> {
        canonicalize_members(items).map(Pred::FiniteSet)
    }

    /// Canonical interval constructor. `None` for an empty interval.
    pub fn interval(lo: i128, hi: i128) -> Option<Self> {
        (lo <= hi).then_some(Pred::Interval { lo, hi })
    }

    /// Structural well-formedness of this node ALONE. Child-id range and the
    /// strictly-less-than ordering are checked by the table validator, which
    /// has the surrounding context.
    pub fn is_canonical(&self) -> bool {
        match self {
            Pred::Interval { lo, hi } => lo <= hi,
            Pred::FiniteSet(items) => members_are_canonical(items),
            Pred::Conj(children) | Pred::Disj(children) => {
                children.len() >= 2
                    && children.len() <= MAX_CONNECTIVE_ARITY
                    && children.windows(2).all(|w| w[0] < w[1])
            }
            Pred::InUniverse(_, _) | Pred::NonZero | Pred::NonNull | Pred::Top | Pred::Bottom => {
                true
            }
        }
    }

    /// Is this the "no information" element?
    pub fn is_top(&self) -> bool {
        matches!(self, Pred::Top)
    }

    /// The universe this predicate is stated over, if any.
    pub fn universe(&self) -> Option<UnivId> {
        match self {
            Pred::InUniverse(u, _) => Some(*u),
            _ => None,
        }
    }

    /// The encoding convention this predicate asserts, if any.
    pub fn space(&self) -> Option<Space> {
        match self {
            Pred::InUniverse(_, s) => Some(*s),
            _ => None,
        }
    }
}

impl core::fmt::Display for Pred {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fn list(
            f: &mut core::fmt::Formatter<'_>,
            head: &str,
            children: &[PredId],
        ) -> core::fmt::Result {
            f.write_str(head)?;
            f.write_str("(")?;
            for (i, c) in children.iter().enumerate() {
                if i > 0 {
                    f.write_str(", ")?;
                }
                write!(f, "pred.{}", c.index())?;
            }
            f.write_str(")")
        }
        match self {
            Pred::Interval { lo, hi } => write!(f, "in[{lo}, {hi}]"),
            Pred::FiniteSet(items) => {
                f.write_str("in{")?;
                for (i, c) in items.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{c}")?;
                }
                f.write_str("}")
            }
            Pred::InUniverse(u, space) => write!(f, "in_universe(univ.{}, {space})", u.index()),
            Pred::NonZero => f.write_str("nonzero"),
            Pred::NonNull => f.write_str("nonnull"),
            Pred::Conj(children) => list(f, "and", children),
            Pred::Disj(children) => list(f, "or", children),
            Pred::Top => f.write_str("top"),
            Pred::Bottom => f.write_str("bottom"),
        }
    }
}

// ---------------------------------------------------------------------------
// PredTable — the decision procedures
// ---------------------------------------------------------------------------

/// A read-only view over a module's interned predicate and universe tables.
///
/// Everything decidable about the lattice is a method here rather than a free
/// function, because `Conj`/`Disj`/`InUniverse` are id-indirected and cannot
/// be decided without the tables.
#[derive(Debug, Clone, Copy)]
pub struct PredTable<'a> {
    predicates: &'a [Pred],
    universes: &'a [Universe],
}

impl<'a> PredTable<'a> {
    pub fn new(predicates: &'a [Pred], universes: &'a [Universe]) -> Self {
        Self {
            predicates,
            universes,
        }
    }

    pub fn pred(&self, id: PredId) -> Option<&'a Pred> {
        self.predicates.get(id.as_usize())
    }

    pub fn universe(&self, id: UnivId) -> Option<&'a Universe> {
        self.universes.get(id.as_usize())
    }

    pub fn preds(&self) -> &'a [Pred] {
        self.predicates
    }

    pub fn universes(&self) -> &'a [Universe] {
        self.universes
    }

    /// Render a predicate id for a diagnostic, resolving one level of
    /// indirection so an error reads
    /// `pred.3 (in_universe(univ.0, member) = member of 1..=8)` instead of a
    /// bare integer. **Every consumption-rule failure names both sides through
    /// this**, because "the implication failed" is useless without knowing
    /// which two facts failed to line up.
    pub fn describe(&self, id: PredId) -> String {
        let Some(p) = self.pred(id) else {
            return format!("pred.{} (DANGLING)", id.index());
        };
        let detail = match p {
            Pred::InUniverse(u, space) => match self.universe(*u) {
                Some(univ) => match space {
                    Space::Index => {
                        let card = univ
                            .cardinality()
                            .map(|n| n.to_string())
                            .unwrap_or_else(|| "?".to_string());
                        format!(" = 0-based index into {univ} (|U| = {card})")
                    }
                    Space::Member => format!(" = member of {univ}"),
                },
                None => " = OVER A DANGLING UNIVERSE".to_string(),
            },
            Pred::Conj(children) | Pred::Disj(children) => {
                let inner: Vec<String> = children
                    .iter()
                    .map(|c| match self.pred(*c) {
                        Some(child) => format!("{child}"),
                        None => format!("pred.{} DANGLING", c.index()),
                    })
                    .collect();
                format!(" = [{}]", inner.join(", "))
            }
            _ => String::new(),
        };
        format!("pred.{} ({p}{detail})", id.index())
    }

    /// The interval a predicate pins `self` to, when it pins one at all.
    ///
    /// Sound direction: `Some((lo, hi))` means the predicate ENTAILS
    /// `lo <= self <= hi`. `None` means "no interval fact is available" —
    /// never "unbounded is fine".
    pub fn interval_bound(&self, id: PredId) -> Option<(i128, i128)> {
        self.interval_bound_at(self.pred(id)?, 0)
    }

    /// [`interval_bound`](Self::interval_bound) over an already-resolved node,
    /// for callers holding a DERIVED (not-yet-interned) predicate.
    pub fn interval_bound_of(&self, p: &Pred) -> Option<(i128, i128)> {
        self.interval_bound_at(p, 0)
    }

    fn interval_bound_at(&self, p: &Pred, depth: u32) -> Option<(i128, i128)> {
        if depth > MAX_PRED_DEPTH {
            return None;
        }
        match p {
            Pred::Interval { lo, hi } => (lo <= hi).then_some((*lo, *hi)),
            Pred::FiniteSet(items) => members_int_bounds(items),
            Pred::InUniverse(u, Space::Member) => self.universe(*u)?.integer_bounds(),
            Pred::InUniverse(u, Space::Index) => {
                let card = self.universe(*u)?.cardinality()?;
                if card == 0 {
                    return None;
                }
                Some((0, i128::try_from(card - 1).ok()?))
            }
            // Intersect whatever bounds the conjuncts offer (a conjunct with
            // no bound simply contributes nothing).
            Pred::Conj(children) => {
                let mut acc: Option<(i128, i128)> = None;
                for child in children {
                    let Some(cp) = self.pred(*child) else {
                        continue;
                    };
                    if let Some((clo, chi)) = self.interval_bound_at(cp, depth + 1) {
                        acc = Some(match acc {
                            None => (clo, chi),
                            Some((lo, hi)) => (lo.max(clo), hi.min(chi)),
                        });
                    }
                }
                acc.filter(|(lo, hi)| lo <= hi)
            }
            // A disjunction's hull is sound only if EVERY arm has a bound.
            Pred::Disj(children) => {
                let mut lo = i128::MAX;
                let mut hi = i128::MIN;
                for child in children {
                    let (clo, chi) = self.interval_bound_at(self.pred(*child)?, depth + 1)?;
                    lo = lo.min(clo);
                    hi = hi.max(chi);
                }
                (lo <= hi).then_some((lo, hi))
            }
            // Bottom is unsatisfiable, so it entails every interval; report a
            // degenerate one so containment checks succeed vacuously.
            Pred::Bottom => Some((0, 0)),
            Pred::NonZero | Pred::NonNull | Pred::Top => None,
        }
    }

    /// Does `a` entail `b`?
    ///
    /// **Decidable, total, and sound in the only direction that matters:
    /// `true` is returned ONLY when the implication genuinely holds; every
    /// undecided case answers `false`.** Dangling ids answer `false` — the
    /// validator reports those separately, and a missing fact must never read
    /// as a satisfied one.
    pub fn implies(&self, a: PredId, b: PredId) -> bool {
        // Interning makes syntactic identity the common fast path — and it is
        // also the structural fix for the join-drop class: two carriers over
        // the same universe ARE the same id, so this hits.
        if a == b {
            return self.pred(a).is_some();
        }
        let (Some(pa), Some(pb)) = (self.pred(a), self.pred(b)) else {
            return false;
        };
        self.implies_at(pa, pb, 0)
    }

    /// [`implies`](Self::implies) over already-resolved nodes.
    pub fn implies_pred(&self, a: &Pred, b: &Pred) -> bool {
        self.implies_at(a, b, 0)
    }

    fn implies_at(&self, a: &Pred, b: &Pred, depth: u32) -> bool {
        if depth > MAX_PRED_DEPTH {
            return false;
        }
        // Bottom entails everything; nothing but Bottom entails Bottom.
        if matches!(a, Pred::Bottom) {
            return true;
        }
        if matches!(b, Pred::Bottom) {
            return false;
        }
        // Everything entails Top.
        if matches!(b, Pred::Top) {
            return true;
        }
        if matches!(a, Pred::Top) {
            // b is neither Top nor Bottom (handled above). A Top carrier
            // entails no non-trivial fact — THIS `false` IS THE LOAD-BEARING
            // LINE OF THE WHOLE DESIGN: it is what turns a dropped fact into a
            // loud failure at the consumption site instead of a silent
            // reinterpretation.
            return false;
        }
        if a == b {
            return true;
        }

        // ── Connective rules ───────────────────────────────────────────────
        //
        // ORDER IS COMPLETENESS, NOT SOUNDNESS. Every rule below is
        // individually sound; which one runs first decides only how many TRUE
        // implications get certified. Two of the four are *unconditional
        // returns* (they are complete for their shape given complete
        // sub-answers), so an unconditional rule placed too early can preempt
        // a cheaper one that would have succeeded.
        //
        // The two SUFFICIENT rules (a conjunct on the left suffices; an arm on
        // the right suffices) therefore run FIRST and only ever answer `true`,
        // falling through when they cannot decide. The two EXHAUSTIVE rules
        // run after and may return `false`.

        // Conjunction on the LEFT: any conjunct suffices.
        if let Pred::Conj(children) = a
            && children.iter().any(|c| {
                self.pred(*c)
                    .is_some_and(|p| self.implies_at(p, b, depth + 1))
            })
        {
            return true;
        }
        // Disjunction on the RIGHT: one arm suffices.
        //
        // WP-1B/G4: this MUST precede `Disj`-on-the-left. It used to run last,
        // after an unconditional `Disj`-on-the-left return, so `a` entailing a
        // disjunction that LITERALLY CONTAINS `a` as an arm was not certified
        // whenever `a` was itself a disjunction — the left rule fired first,
        // recursed into a's arms, hit a `Top` arm and answered `false`. Trying
        // the sufficient rule first makes `a ⊑ Disj[.., a, ..]` a one-step
        // syntactic hit.
        if let Pred::Disj(children) = b
            && children.iter().any(|c| {
                self.pred(*c)
                    .is_some_and(|p| self.implies_at(a, p, depth + 1))
            })
        {
            return true;
        }
        // Conjunction on the RIGHT: every conjunct must be entailed.
        if let Pred::Conj(children) = b {
            return children.iter().all(|c| {
                self.pred(*c)
                    .is_some_and(|p| self.implies_at(a, p, depth + 1))
            });
        }
        // Disjunction on the LEFT: every arm must entail the target.
        if let Pred::Disj(children) = a {
            return children.iter().all(|c| {
                self.pred(*c)
                    .is_some_and(|p| self.implies_at(p, b, depth + 1))
            });
        }

        match b {
            // ── The convention rule ────────────────────────────────────────
            Pred::InUniverse(ub, sb) => {
                let Pred::InUniverse(ua, sa) = a else {
                    // No other fact shape entails a universe claim: an
                    // interval is a raw numeric fact and carries no
                    // convention, which is exactly why it must not be
                    // promoted into one.
                    return false;
                };
                // DIFFERENT SPACE OVER THE SAME UNIVERSE IS NOT AN
                // IMPLICATION. This single `false` is what makes the
                // index-vs-member miscompile class statable and catchable.
                if sa != sb {
                    return false;
                }
                let (Some(ua), Some(ub)) = (self.universe(*ua), self.universe(*ub)) else {
                    return false;
                };
                match sa {
                    // MEMBERSHIP IS MONOTONE IN THE UNIVERSE:
                    // U ⊆ V ⇒ (self ∈ U) ⇒ (self ∈ V). Sound *and* meaningful,
                    // because membership is a fact about the VALUE: it
                    // transfers to a larger universe unchanged.
                    Space::Member => ua.is_subset_of(ub),
                    // INDEX-HOOD IS EXTENSIONAL IN THE UNIVERSE (WP-1B/G3).
                    //
                    // This rule used to hold on CARDINALITY alone
                    // (`|U| <= |V|`), which is sound under the numeric
                    // denotation `0 <= self < |U|` — and exactly that soundness
                    // is what made it dangerous. An index is a fact about the
                    // value RELATIVE TO an ordering, not about the value: "the
                    // 3rd entry of U" and "the 3rd entry of V" denote different
                    // things whenever U != V, so letting an index into one
                    // universe satisfy a site stated over another reintroduces
                    // the very confusion class this model exists to prevent —
                    // one table's ordinal read against another table.
                    //
                    // So the rule is now extensional equality of the two
                    // universes. Two spellings of one extension (`1..=8` and
                    // `{1,…,8}`) still entail each other, because the canonical
                    // member ordering is a function of the extension.
                    //
                    // The cost is a documented INCOMPLETENESS, paid loudly: a
                    // numerically-sound cross-universe index implication is
                    // refused. The numeric content stays reachable — an index
                    // still entails `Interval { 0, |U|-1 }` and every wider
                    // interval (see `interval_bound_at`), so a site that wants
                    // only "a number below n" spells it as an `Interval` and is
                    // satisfied.
                    Space::Index => ua.is_subset_of(ub) && ub.is_subset_of(ua),
                }
            }

            // ── Numeric containment ────────────────────────────────────────
            Pred::Interval { lo, hi } => match self.interval_bound_at(a, depth + 1) {
                Some((alo, ahi)) => *lo <= alo && ahi <= *hi,
                None => false,
            },
            Pred::FiniteSet(target) => match a {
                Pred::FiniteSet(src) => members_subset(src, target),
                Pred::Interval { lo, hi } => members_contain_interval(target, *lo, *hi),
                Pred::InUniverse(u, space) => match (self.universe(*u), space) {
                    (Some(Universe::Members(src)), Space::Member) => members_subset(src, target),
                    (Some(Universe::IntRange { lo, hi }), Space::Member) => {
                        members_contain_interval(target, *lo, *hi)
                    }
                    (Some(univ), Space::Index) => match univ.cardinality() {
                        Some(card) if card > 0 => match i128::try_from(card - 1) {
                            Ok(hi) => members_contain_interval(target, 0, hi),
                            Err(_) => false,
                        },
                        _ => false,
                    },
                    (None, _) => false,
                },
                _ => false,
            },

            // ── NonZero / NonNull ──────────────────────────────────────────
            // A numeric fact entails NonZero when 0 is outside its bounds.
            Pred::NonZero => match self.interval_bound_at(a, depth + 1) {
                Some((lo, hi)) => lo > 0 || hi < 0,
                None => false,
            },
            // NonNull is a POINTER fact, not an integer one. It is entailed
            // only by itself (handled by `a == b` above) — deliberately NOT
            // derived from NonZero, because "not the null pointer" and "not
            // the integer zero" coincide only under a provenance assumption
            // this lattice does not make.
            Pred::NonNull => false,

            Pred::Top | Pred::Bottom | Pred::Conj(_) | Pred::Disj(_) => false,
        }
    }

    /// The canonical machine-readable rendering of a predicate, as the
    /// EXISTING [`crate::proof::ProofFormula`] carrier.
    ///
    /// Reuse, not rebuild: `ProofFormula { schema, payload, smtlib, sort }` is
    /// already how every obligation carries a verifier-facing formula, and
    /// `ObligationKind::RefinementType` is already a contract kind — the only
    /// replayable-authority path that exists. The consumption half was never
    /// the gap; the CARRIER was. This renders a `Refine`'s predicate into that
    /// channel so a router or solver indexes it exactly like any other
    /// obligation formula, with no second schema invented for it.
    ///
    /// `payload` is the module-local `pred.N` citation (the identity a
    /// `Ty::Refine` carries); `smtlib` is a self-contained rendering over the
    /// distinguished free variable `self`. Returns `None` for a dangling id.
    pub fn proof_formula(&self, id: PredId) -> Option<crate::proof::ProofFormula> {
        let smtlib = self.smtlib_of(id)?;
        Some(crate::proof::ProofFormula {
            schema: PRED_FORMULA_SCHEMA.to_string(),
            payload: format!("pred.{}", id.index()),
            smtlib: Some(smtlib),
            // The SMT sort is the BASE type's, which a predicate does not
            // know — a `Refine` names it. Left `None` deliberately rather
            // than guessed.
            sort: None,
        })
    }

    /// SMT-LIB2 rendering of a predicate over the free variable `self`.
    pub fn smtlib_of(&self, id: PredId) -> Option<String> {
        self.smtlib_at(id, 0)
    }

    fn smtlib_at(&self, id: PredId, depth: u32) -> Option<String> {
        if depth > MAX_PRED_DEPTH {
            return None;
        }
        let text = match self.pred(id)? {
            Pred::Interval { lo, hi } => {
                format!("(and (<= {lo} self) (<= self {hi}))")
            }
            Pred::FiniteSet(items) => {
                let arms: Vec<String> = items
                    .iter()
                    .map(|c| match constant_key(c) {
                        Some((1, v)) => format!("(= self {})", v != 0),
                        _ => format!("(= self {c})"),
                    })
                    .collect();
                format!("(or {})", arms.join(" "))
            }
            Pred::InUniverse(u, space) => {
                let universe = self.universe(*u)?;
                match space {
                    Space::Member => match universe {
                        Universe::IntRange { lo, hi } => {
                            format!("(and (<= {lo} self) (<= self {hi}))")
                        }
                        Universe::Members(items) => {
                            let arms: Vec<String> =
                                items.iter().map(|c| format!("(= self {c})")).collect();
                            format!("(or {})", arms.join(" "))
                        }
                    },
                    // The convention distinction survives into SMT: an index
                    // constrains the ORDINAL, not the member value.
                    Space::Index => {
                        let card = universe.cardinality()?;
                        format!("(and (<= 0 self) (< self {card}))")
                    }
                }
            }
            Pred::NonZero => "(not (= self 0))".to_string(),
            Pred::NonNull => "(not (= self null))".to_string(),
            Pred::Conj(children) => {
                let arms: Vec<String> = children
                    .iter()
                    .map(|c| self.smtlib_at(*c, depth + 1))
                    .collect::<Option<_>>()?;
                format!("(and {})", arms.join(" "))
            }
            Pred::Disj(children) => {
                let arms: Vec<String> = children
                    .iter()
                    .map(|c| self.smtlib_at(*c, depth + 1))
                    .collect::<Option<_>>()?;
                format!("(or {})", arms.join(" "))
            }
            Pred::Top => "true".to_string(),
            Pred::Bottom => "false".to_string(),
        };
        Some(text)
    }

    /// **The join**: the least upper bound this lattice can compute for two
    /// facts meeting at a control-flow join, as an un-interned node.
    ///
    /// Join is DISJUNCTION, and every fallback is toward [`Pred::Top`] — never
    /// toward `Bottom`, never toward "unknown but assume ok". The result is
    /// always weaker than or equal to both inputs, so a merge can only ever
    /// LOSE information, and losing it makes the consumption site fail rather
    /// than reinterpret.
    ///
    /// Policy, in order:
    ///
    /// 1. `a == b` ⇒ that predicate. Under content-interning this is the case
    ///    that fires for two carriers over the same universe cited by
    ///    different proofs — the direct structural fix for the join-drop
    ///    miscompile.
    /// 2. One side entails the other ⇒ the weaker side (exact).
    /// 3. Two intervals ⇒ their hull (exact, cheap).
    /// 4. Two finite sets ⇒ their union when it stays in cap.
    /// 5. Two `InUniverse` facts over DIFFERENT universes that are not
    ///    comparable ⇒ `Top`. Two different universes share no convention a
    ///    consumer can act on; decaying to `Top` makes the loss loud.
    /// 6. Anything else ⇒ `Disj([a, b])`, or `Top` if either id is dangling.
    pub fn join_pred(&self, a: PredId, b: PredId) -> Pred {
        // A dangling id is not a fact; the merge has no information.
        let (Some(pa), Some(pb)) = (self.pred(a), self.pred(b)) else {
            return Pred::Top;
        };
        if a == b {
            return pa.clone();
        }
        match self.join_nodes(pa, pb) {
            Some(joined) => joined,
            // The lattice has no better *node* for this pair — but we hold two
            // ids, so the exact disjunction is spellable. (The node-only
            // entry point has no ids and weakens to `Top` instead.)
            None => {
                let (lo, hi) = if a < b { (a, b) } else { (b, a) };
                Pred::Disj(vec![lo, hi])
            }
        }
    }

    /// [`join_pred`](Self::join_pred) over already-resolved nodes, for callers
    /// that hold DERIVED (not-yet-interned) predicates — forward propagation,
    /// principally.
    ///
    /// Identical policy, with one difference forced by having no ids: where
    /// [`join_pred`] would spell the exact `Disj([a, b])`, this weakens to
    /// [`Pred::Top`]. That is sound in the only direction that matters — a
    /// join must be an UPPER bound, `Top` is an upper bound of everything, and
    /// the loss then FAILS at the consumption site rather than being
    /// reinterpreted.
    pub fn join_pred_nodes(&self, a: &Pred, b: &Pred) -> Pred {
        self.join_nodes(a, b).unwrap_or(Pred::Top)
    }

    /// The join policy in node space. `None` means "no node expresses it";
    /// callers holding ids may spell the exact `Disj`, callers without ids
    /// must weaken to `Top`.
    fn join_nodes(&self, pa: &Pred, pb: &Pred) -> Option<Pred> {
        if pa == pb {
            return Some(pa.clone());
        }
        if self.implies_pred(pa, pb) {
            return Some(pb.clone());
        }
        if self.implies_pred(pb, pa) {
            return Some(pa.clone());
        }
        match (pa, pb) {
            (Pred::Interval { lo: alo, hi: ahi }, Pred::Interval { lo: blo, hi: bhi }) => {
                Some(Pred::Interval {
                    lo: *alo.min(blo),
                    hi: *ahi.max(bhi),
                })
            }
            (Pred::FiniteSet(x), Pred::FiniteSet(y)) => {
                let merged = x.iter().chain(y.iter()).cloned();
                match canonicalize_members(merged) {
                    Some(items) => Some(Pred::FiniteSet(items)),
                    // Over cap / non-scalar: weaken, do not guess.
                    None => Some(Pred::Top),
                }
            }
            // Incomparable universes (rule 5). Reaching here means neither
            // entails the other, so there is no shared convention to keep.
            (Pred::InUniverse(_, _), Pred::InUniverse(_, _)) => Some(Pred::Top),
            _ => None,
        }
    }

    /// Can the lattice PROVE that `a` and `b` cannot both hold of the same
    /// value?
    ///
    /// **Decidable and one-directional, like [`implies`](Self::implies):**
    /// `true` only when the contradiction genuinely holds; every undecided
    /// case answers `false`. It is used to catch a producer that DECLARES a
    /// refinement which forward propagation contradicts — a frontend bug of
    /// exactly the class this model exists to surface — so a false positive
    /// here would be a spurious hard error and is not acceptable.
    ///
    /// The decided case is disjoint integer bounds. [`Pred::Bottom`] is
    /// deliberately EXEMPT: it is the explicit "this path is dead" marker, and
    /// a dead path contradicting a live fact is a statement, not a bug.
    pub fn contradicts(&self, a: &Pred, b: &Pred) -> bool {
        if matches!(a, Pred::Bottom) || matches!(b, Pred::Bottom) {
            return false;
        }
        match (self.interval_bound_at(a, 0), self.interval_bound_at(b, 0)) {
            (Some((alo, ahi)), Some((blo, bhi))) => ahi < blo || bhi < alo,
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ints(vs: &[i128]) -> Vec<Constant> {
        vs.iter().copied().map(Constant::Int).collect()
    }

    #[test]
    fn space_display_is_stable() {
        assert_eq!(format!("{}", Space::Index), "index");
        assert_eq!(format!("{}", Space::Member), "member");
    }

    #[test]
    fn universe_members_canonicalizes() {
        let u = Universe::members(ints(&[3, 1, 2, 1])).expect("canonical");
        assert_eq!(u, Universe::Members(ints(&[1, 2, 3])));
        assert!(u.is_canonical());
        assert_eq!(u.cardinality(), Some(3));
    }

    #[test]
    fn universe_members_rejects_non_scalar_and_empty() {
        assert!(Universe::members(vec![Constant::Float(1.0)]).is_none());
        assert!(Universe::members(Vec::new()).is_none());
    }

    #[test]
    fn universe_range_cardinality_does_not_overflow() {
        assert_eq!(
            Universe::IntRange {
                lo: i128::MIN,
                hi: i128::MAX
            }
            .cardinality(),
            None,
            "2^128 members does not fit u128; must answer 'unknown', not wrap"
        );
        assert_eq!(Universe::IntRange { lo: -1, hi: 1 }.cardinality(), Some(3));
        assert_eq!(Universe::IntRange { lo: 5, hi: 4 }.cardinality(), None);
    }

    #[test]
    fn top_implies_nothing_but_top() {
        let preds = vec![Pred::Top, Pred::Interval { lo: 0, hi: 7 }];
        let t = PredTable::new(&preds, &[]);
        assert!(t.implies(PredId::new(0), PredId::new(0)));
        assert!(
            !t.implies(PredId::new(0), PredId::new(1)),
            "a dropped fact must not satisfy a consumption site"
        );
        assert!(t.implies(PredId::new(1), PredId::new(0)));
    }

    #[test]
    fn bottom_implies_everything() {
        let preds = vec![Pred::Bottom, Pred::Interval { lo: 0, hi: 7 }];
        let t = PredTable::new(&preds, &[]);
        assert!(t.implies(PredId::new(0), PredId::new(1)));
        assert!(!t.implies(PredId::new(1), PredId::new(0)));
    }

    #[test]
    fn interval_containment_is_decided() {
        let preds = vec![
            Pred::Interval { lo: 2, hi: 5 },
            Pred::Interval { lo: 0, hi: 7 },
        ];
        let t = PredTable::new(&preds, &[]);
        assert!(t.implies(PredId::new(0), PredId::new(1)));
        assert!(!t.implies(PredId::new(1), PredId::new(0)));
    }

    #[test]
    fn finite_set_subset_is_decided() {
        let preds = vec![
            Pred::FiniteSet(ints(&[1, 3])),
            Pred::FiniteSet(ints(&[1, 2, 3])),
        ];
        let t = PredTable::new(&preds, &[]);
        assert!(t.implies(PredId::new(0), PredId::new(1)));
        assert!(!t.implies(PredId::new(1), PredId::new(0)));
    }

    #[test]
    fn index_does_not_imply_member_over_the_same_universe() {
        // U = {1..=8}. An INDEX into U lives in 0..=7; a MEMBER of U lives in
        // 1..=8. Neither entails the other — this is the WP-18 class.
        let univs = vec![Universe::IntRange { lo: 1, hi: 8 }];
        let preds = vec![
            Pred::InUniverse(UnivId::new(0), Space::Index),
            Pred::InUniverse(UnivId::new(0), Space::Member),
        ];
        let t = PredTable::new(&preds, &univs);
        assert!(!t.implies(PredId::new(0), PredId::new(1)));
        assert!(!t.implies(PredId::new(1), PredId::new(0)));
    }

    #[test]
    fn raw_interval_never_promotes_to_a_membership_convention() {
        // Even an interval that NUMERICALLY coincides with the universe does
        // not entail membership: the convention is not derivable from the
        // number. (The reverse direction IS sound and is checked below.)
        let univs = vec![Universe::IntRange { lo: 1, hi: 8 }];
        let preds = vec![
            Pred::Interval { lo: 1, hi: 8 },
            Pred::InUniverse(UnivId::new(0), Space::Member),
        ];
        let t = PredTable::new(&preds, &univs);
        assert!(!t.implies(PredId::new(0), PredId::new(1)));
        assert!(
            t.implies(PredId::new(1), PredId::new(0)),
            "membership DOES entail its numeric bounds"
        );
    }

    #[test]
    fn member_is_monotone_in_the_universe_but_index_is_extensional_in_it() {
        // THE G3 DECISION, pinned with its rationale.
        //
        // MEMBER is monotone: membership is a fact about the VALUE, so it
        // transfers unchanged into any superset universe.
        //
        // INDEX is not, in either direction. `|U| <= |V|` is enough to make a
        // cross-universe index implication NUMERICALLY sound (an index into a
        // 4-element universe is a number in 0..=3, which is also a valid
        // ordinal into an 8-element one) — and it is refused anyway, because an
        // ordinal is only meaningful against the ordering it indexes. Accepting
        // it would let a row index into one table satisfy a site that indexes a
        // DIFFERENT table, which is the confusion class this whole model
        // exists to make unstatable-no-more.
        let univs = vec![
            Universe::IntRange { lo: 1, hi: 4 },
            Universe::IntRange { lo: 1, hi: 8 },
        ];
        let preds = vec![
            Pred::InUniverse(UnivId::new(0), Space::Member),
            Pred::InUniverse(UnivId::new(1), Space::Member),
            Pred::InUniverse(UnivId::new(0), Space::Index),
            Pred::InUniverse(UnivId::new(1), Space::Index),
            // The numeric consequence of "index into a 4-element universe".
            Pred::Interval { lo: 0, hi: 7 },
        ];
        let t = PredTable::new(&preds, &univs);
        assert!(t.implies(PredId::new(0), PredId::new(1)), "member ⊆");
        assert!(!t.implies(PredId::new(1), PredId::new(0)), "member ⊉");
        assert!(
            !t.implies(PredId::new(2), PredId::new(3)),
            "an index into 1..=4 must NOT satisfy a site indexing 1..=8, even \
             though |U| <= |V| makes it numerically sound"
        );
        assert!(
            !t.implies(PredId::new(3), PredId::new(2)),
            "nor the converse"
        );

        // THE ESCAPE HATCH, so the refusal is a spelling requirement and not an
        // expressiveness dead end: the numeric content is still entailed, so a
        // site that genuinely wants only "a number below 8" says `in[0, 7]` and
        // is satisfied by an index into ANY universe of at most 8 members.
        assert!(
            t.implies(PredId::new(2), PredId::new(4)),
            "an index still entails its numeric bound"
        );
        assert!(
            t.implies(PredId::new(3), PredId::new(4)),
            "and so does an index into the larger universe"
        );
    }

    #[test]
    fn index_implication_is_extensional_not_syntactic() {
        // Extensional, not id-equality: two SPELLINGS of one extension have
        // the same canonical member ordering, so they index the same thing and
        // must entail each other. (Interning collapses most of these, but two
        // spellings genuinely are two ids — see the WP-28 acceptance test.)
        let univs = vec![
            Universe::IntRange { lo: 1, hi: 4 },
            Universe::Members(ints(&[1, 2, 3, 4])),
            Universe::Members(ints(&[5, 6, 7, 8])),
        ];
        let preds = vec![
            Pred::InUniverse(UnivId::new(0), Space::Index),
            Pred::InUniverse(UnivId::new(1), Space::Index),
            // Same CARDINALITY (4), different extension.
            Pred::InUniverse(UnivId::new(2), Space::Index),
        ];
        let t = PredTable::new(&preds, &univs);
        assert!(t.implies(PredId::new(0), PredId::new(1)));
        assert!(t.implies(PredId::new(1), PredId::new(0)));
        assert!(
            !t.implies(PredId::new(0), PredId::new(2)),
            "equal cardinality is NOT equal ordering: {{1,2,3,4}} and \
             {{5,6,7,8}} have different 3rd entries"
        );
        assert!(!t.implies(PredId::new(2), PredId::new(0)));
    }

    #[test]
    fn a_disjunction_that_contains_the_antecedent_is_certified() {
        // WP-1B/G4. `a ⊑ Disj[.., a, ..]` is trivially true. Before the arm
        // reorder, `Disj`-on-the-LEFT was an unconditional early return placed
        // ahead of `Disj`-on-the-RIGHT, so when `a` was itself a disjunction
        // the left rule fired, recursed into a's arms, hit the `Top` arm and
        // answered `false`.
        let preds = vec![
            Pred::Top,                                        // 0
            Pred::Bottom,                                     // 1
            Pred::Interval { lo: -2, hi: 1 },                 // 2
            Pred::Interval { lo: 0, hi: 0 },                  // 3
            Pred::Disj(vec![PredId::new(0), PredId::new(1)]), // 4 = a (has a Top arm)
            Pred::Disj(vec![PredId::new(2), PredId::new(3)]), // 5
            Pred::Disj(vec![PredId::new(4), PredId::new(5)]), // 6 = contains both
        ];
        let t = PredTable::new(&preds, &[]);
        assert!(
            t.implies(PredId::new(4), PredId::new(6)),
            "a must entail a disjunction that literally contains it — this is \
             the pair the old arm order missed, because a's `top` arm made the \
             Disj-on-the-left rule answer false first"
        );
        assert!(
            t.implies(PredId::new(5), PredId::new(6)),
            "and so must every other arm"
        );
        assert!(
            t.implies(PredId::new(3), PredId::new(5)),
            "arm ⊑ disjunction"
        );
        // The reorder must not have manufactured the converse: a disjunction
        // does NOT entail one of its arms.
        assert!(
            !t.implies(PredId::new(5), PredId::new(3)),
            "or([-2,1], [0,0]) must not entail [0,0]"
        );
    }

    #[test]
    fn nonzero_is_entailed_only_when_zero_is_excluded() {
        let preds = vec![
            Pred::NonZero,
            Pred::Interval { lo: 1, hi: 4 },
            Pred::Interval { lo: 0, hi: 4 },
        ];
        let t = PredTable::new(&preds, &[]);
        assert!(t.implies(PredId::new(1), PredId::new(0)));
        assert!(!t.implies(PredId::new(2), PredId::new(0)));
    }

    #[test]
    fn nonnull_is_not_derived_from_nonzero() {
        let preds = vec![Pred::NonZero, Pred::NonNull];
        let t = PredTable::new(&preds, &[]);
        assert!(!t.implies(PredId::new(0), PredId::new(1)));
        assert!(!t.implies(PredId::new(1), PredId::new(0)));
    }

    #[test]
    fn dangling_ids_answer_false() {
        let preds = vec![Pred::Top];
        let t = PredTable::new(&preds, &[]);
        assert!(!t.implies(PredId::new(9), PredId::new(0)));
        assert!(!t.implies(PredId::new(0), PredId::new(9)));
        assert!(
            !t.implies(PredId::new(9), PredId::new(9)),
            "a dangling id is not a fact, not even reflexively"
        );
    }

    #[test]
    fn conjunction_and_disjunction_are_decided() {
        let preds = vec![
            Pred::Interval { lo: 0, hi: 3 },                  // 0
            Pred::Interval { lo: 2, hi: 9 },                  // 1
            Pred::Interval { lo: 0, hi: 9 },                  // 2
            Pred::Conj(vec![PredId::new(0), PredId::new(1)]), // 3 => [2,3]
            Pred::Disj(vec![PredId::new(0), PredId::new(1)]), // 4 => [0,9]
        ];
        let t = PredTable::new(&preds, &[]);
        assert!(t.implies(PredId::new(3), PredId::new(0)));
        assert!(t.implies(PredId::new(3), PredId::new(1)));
        assert!(t.implies(PredId::new(4), PredId::new(2)));
        assert!(!t.implies(PredId::new(4), PredId::new(0)));
        assert!(!t.implies(PredId::new(4), PredId::new(1)));
        assert!(t.implies(PredId::new(0), PredId::new(4)));
        assert!(t.implies(PredId::new(1), PredId::new(4)));
    }

    #[test]
    fn cyclic_children_terminate_instead_of_recursing_forever() {
        // Not reachable through the interning API (children are always older
        // than their parent) and rejected by the validator — but `implies` is
        // callable on a freshly decoded blob, so it must be total.
        let preds = vec![
            Pred::Conj(vec![PredId::new(1), PredId::new(2)]),
            Pred::Conj(vec![PredId::new(0), PredId::new(2)]),
            Pred::Interval { lo: 0, hi: 1 },
        ];
        let t = PredTable::new(&preds, &[]);
        assert!(t.implies(PredId::new(0), PredId::new(2)));
        assert!(!t.implies(PredId::new(2), PredId::new(0)));
    }

    #[test]
    fn canonicality_rejects_unsorted_connectives_and_empty_extensions() {
        assert!(!Pred::Conj(vec![PredId::new(1), PredId::new(0)]).is_canonical());
        assert!(!Pred::Conj(vec![PredId::new(0)]).is_canonical());
        assert!(!Pred::FiniteSet(Vec::new()).is_canonical());
        assert!(!Pred::Interval { lo: 5, hi: 4 }.is_canonical());
        assert!(Pred::Interval { lo: 4, hi: 4 }.is_canonical());
    }

    #[test]
    fn describe_resolves_one_level_of_indirection() {
        let univs = vec![Universe::IntRange { lo: 1, hi: 8 }];
        let preds = vec![Pred::InUniverse(UnivId::new(0), Space::Member)];
        let t = PredTable::new(&preds, &univs);
        let text = t.describe(PredId::new(0));
        assert!(text.contains("pred.0"), "{text}");
        assert!(text.contains("member"), "{text}");
        assert!(text.contains("1..=8"), "{text}");
    }

    #[test]
    fn proof_formula_reuses_the_existing_carrier() {
        let univs = vec![Universe::IntRange { lo: 1, hi: 8 }];
        let preds = vec![
            Pred::InUniverse(UnivId::new(0), Space::Member),
            Pred::InUniverse(UnivId::new(0), Space::Index),
            Pred::NonZero,
            Pred::Conj(vec![PredId::new(1), PredId::new(2)]),
        ];
        let t = PredTable::new(&preds, &univs);

        let f = t.proof_formula(PredId::new(0)).expect("rendered");
        assert_eq!(f.schema, PRED_FORMULA_SCHEMA);
        assert_eq!(f.payload, "pred.0");
        assert_eq!(f.smtlib.as_deref(), Some("(and (<= 1 self) (<= self 8))"));
        // The SORT is the base type's and a predicate does not know it — left
        // None rather than guessed.
        assert_eq!(f.sort, None);

        // The convention distinction survives into SMT: an index constrains
        // the ORDINAL, a member constrains the VALUE.
        assert_eq!(
            t.smtlib_of(PredId::new(1)).as_deref(),
            Some("(and (<= 0 self) (< self 8))")
        );
        assert_eq!(
            t.smtlib_of(PredId::new(3)).as_deref(),
            Some("(and (and (<= 0 self) (< self 8)) (not (= self 0)))")
        );
        assert!(t.proof_formula(PredId::new(9)).is_none());
    }

    #[test]
    fn join_of_identical_ids_preserves_the_fact() {
        let univs = vec![Universe::IntRange { lo: 1, hi: 8 }];
        let preds = vec![Pred::InUniverse(UnivId::new(0), Space::Member)];
        let t = PredTable::new(&preds, &univs);
        assert_eq!(t.join_pred(PredId::new(0), PredId::new(0)), preds[0]);
    }

    #[test]
    fn join_keeps_the_weaker_side_when_comparable() {
        let preds = vec![
            Pred::Interval { lo: 2, hi: 5 },
            Pred::Interval { lo: 0, hi: 9 },
        ];
        let t = PredTable::new(&preds, &[]);
        assert_eq!(
            t.join_pred(PredId::new(0), PredId::new(1)),
            Pred::Interval { lo: 0, hi: 9 }
        );
    }

    #[test]
    fn join_of_incomparable_intervals_is_the_hull() {
        let preds = vec![
            Pred::Interval { lo: 0, hi: 3 },
            Pred::Interval { lo: 7, hi: 9 },
        ];
        let t = PredTable::new(&preds, &[]);
        assert_eq!(
            t.join_pred(PredId::new(0), PredId::new(1)),
            Pred::Interval { lo: 0, hi: 9 }
        );
    }

    #[test]
    fn join_of_different_universes_decays_to_top() {
        let univs = vec![
            Universe::Members(ints(&[1, 2])),
            Universe::Members(ints(&[5, 6])),
        ];
        let preds = vec![
            Pred::InUniverse(UnivId::new(0), Space::Member),
            Pred::InUniverse(UnivId::new(1), Space::Member),
        ];
        let t = PredTable::new(&preds, &univs);
        assert_eq!(t.join_pred(PredId::new(0), PredId::new(1)), Pred::Top);
    }

    #[test]
    fn join_with_a_dangling_side_decays_to_top() {
        let preds = vec![Pred::Interval { lo: 0, hi: 3 }];
        let t = PredTable::new(&preds, &[]);
        assert_eq!(t.join_pred(PredId::new(0), PredId::new(7)), Pred::Top);
    }

    #[test]
    fn join_is_an_upper_bound_of_both_inputs() {
        // The soundness property of a join: it must be implied BY each input.
        let univs = vec![Universe::IntRange { lo: 0, hi: 7 }];
        let preds = vec![
            Pred::Interval { lo: 0, hi: 3 },
            Pred::Interval { lo: 7, hi: 9 },
            Pred::FiniteSet(ints(&[1, 2])),
            Pred::NonZero,
            Pred::InUniverse(UnivId::new(0), Space::Index),
            Pred::Top,
            Pred::Bottom,
        ];
        let t = PredTable::new(&preds, &univs);
        for a in 0..preds.len() as u32 {
            for b in 0..preds.len() as u32 {
                let joined = t.join_pred(PredId::new(a), PredId::new(b));
                assert!(
                    t.implies_pred(&preds[a as usize], &joined),
                    "join({a},{b}) = {joined} is not implied by lhs {}",
                    preds[a as usize]
                );
                assert!(
                    t.implies_pred(&preds[b as usize], &joined),
                    "join({a},{b}) = {joined} is not implied by rhs {}",
                    preds[b as usize]
                );
            }
        }
    }
}
