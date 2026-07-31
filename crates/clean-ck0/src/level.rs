// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe [`Level`]s — the Lean 4 lattice, **canonicalized at construction**.
//!
//! `Level = Zero | Succ | Max | IMax | Param(u32)`. Unlike the legacy kernel,
//! `Param` is a **positional index into the declaration's level telescope**
//! (design §2, §4.2), never a [`crate::Name`]: the caller cannot smuggle a
//! free-form universe name in.
//!
//! **Canonical-by-construction.** Every smart constructor returns a level in
//! the canonical normal form (offset-stripped, `Max` operands flattened /
//! sorted / deduped / subsumed, `IMax(_, Zero) = Zero` collapsed, `IMax`
//! reducing to `Max` when the right operand is provably non-zero). Therefore
//! **`==` on canonical levels is exactly definitional equality** — no separate
//! `normalize` pass is needed at use sites. This mirrors Lean's
//! `level.cpp` normalization, restricted to the positional-`Param` lattice.

use std::cmp::Ordering;
use std::sync::Arc;

/// Errors constructing a level (M0 surface is small; positional params can't be
/// out of range at construction — that is a *validation* concern checked in
/// [`crate::validate`] against the declaration arity).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum LevelError {
    /// A level-param index exceeded the declared number of params (raised by the
    /// validation chokepoint, not by construction).
    #[error("level param index {index} >= declared arity {arity}")]
    ParamOutOfRange {
        /// The offending positional index.
        index: u32,
        /// The declaration's level-param count.
        arity: u32,
    },
}

/// A universe level in canonical form.
///
/// The inner representation is private; the only way to build one is via the
/// smart constructors, all of which canonicalize. Two canonical levels are
/// definitionally equal iff they are structurally `==`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Level(Repr);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Repr {
    Zero,
    Succ(Arc<Level>),
    Max(Arc<Level>, Arc<Level>),
    IMax(Arc<Level>, Arc<Level>),
    Param(u32),
}

impl Level {
    // --- smart constructors (all canonicalizing) ---

    /// The zero level (`Prop`'s level).
    #[must_use]
    pub fn zero() -> Self {
        Level(Repr::Zero)
    }

    /// A positional universe parameter (index into the declaration's telescope).
    #[must_use]
    pub fn param(index: u32) -> Self {
        Level(Repr::Param(index))
    }

    /// `succ(l)`, canonicalized. `Succ` distributes over `Max`
    /// (`succ(max(a,b)) = max(succ a, succ b)`), so a raw `Succ(Max(..))` is not
    /// canonical; we normalize to keep the by-construction invariant. `succ` of
    /// a non-`Max` base is already canonical, so this is cheap in the common case.
    #[must_use]
    pub fn succ(l: Level) -> Self {
        if matches!(l.0, Repr::Max(_, _) | Repr::IMax(_, _)) {
            Level(Repr::Succ(Arc::new(l))).normalize()
        } else {
            Level(Repr::Succ(Arc::new(l)))
        }
    }

    /// Raw `succ` without canonicalization — internal use only, for the
    /// normalizer's own offset re-application where the base is already a
    /// canonical non-`Max` leaf.
    fn raw_succ(l: Level) -> Self {
        Level(Repr::Succ(Arc::new(l)))
    }

    /// `n` as a level: `succ^n(zero)`.
    #[must_use]
    pub fn nat(n: u32) -> Self {
        let mut l = Level::zero();
        for _ in 0..n {
            l = Level::succ(l);
        }
        l
    }

    /// `max(l1, l2)`, canonicalized.
    #[must_use]
    pub fn max(l1: Level, l2: Level) -> Self {
        // Build a raw Max then renormalize the whole thing so flatten/sort/dedup
        // run. Both inputs are already canonical, so this is a single pass.
        let raw = Level(Repr::Max(Arc::new(l1), Arc::new(l2)));
        raw.normalize()
    }

    /// `imax(l1, l2)`, canonicalized.
    ///
    /// `imax(l, 0) = 0`; `imax(l, l')=max(l,l')` when `l'` is provably non-zero;
    /// `imax(0,l)=l`; `imax(1,l)=l`; `imax(l,l)=l`; else `IMax(l,l')`.
    #[must_use]
    pub fn imax(l1: Level, l2: Level) -> Self {
        let raw = Level(Repr::IMax(Arc::new(l1), Arc::new(l2)));
        raw.normalize()
    }

    // --- queries ---

    /// True iff *provably* zero (structural; canonical form makes this exact for
    /// closed levels).
    #[must_use]
    pub fn is_zero(&self) -> bool {
        match &self.0 {
            Repr::Zero => true,
            Repr::Succ(_) | Repr::Param(_) => false,
            Repr::Max(a, b) => a.is_zero() && b.is_zero(),
            Repr::IMax(_, b) => b.is_zero(),
        }
    }

    /// True iff *provably* non-zero.
    #[must_use]
    pub fn is_nonzero(&self) -> bool {
        match &self.0 {
            Repr::Zero | Repr::Param(_) => false,
            Repr::Succ(_) => true,
            Repr::Max(a, b) => a.is_nonzero() || b.is_nonzero(),
            Repr::IMax(_, b) => b.is_nonzero(),
        }
    }

    /// The maximum `Param` index appearing in this level, plus one (i.e. the
    /// minimal telescope arity that makes every param in-range), or `0` if no
    /// param appears. Used by [`crate::validate`] to check level-arity.
    #[must_use]
    pub fn max_param_plus_one(&self) -> u32 {
        match &self.0 {
            Repr::Zero => 0,
            Repr::Param(i) => i.saturating_add(1),
            Repr::Succ(l) => l.max_param_plus_one(),
            Repr::Max(a, b) | Repr::IMax(a, b) => {
                a.max_param_plus_one().max(b.max_param_plus_one())
            }
        }
    }

    /// Strip leading `Succ`s: returns `(base, offset)` with `base` not a `Succ`.
    fn get_offset(&self) -> (Level, u32) {
        let mut cur = self.clone();
        let mut off: u32 = 0;
        while let Repr::Succ(inner) = &cur.0 {
            // Index *count*, not a numeric value; saturating is the right
            // overflow behaviour and policy-clean (no value arithmetic).
            off = off.saturating_add(1);
            let next = Level::clone(inner);
            cur = next;
        }
        (cur, off)
    }

    /// Re-apply an offset: `add_offset(l, n) = succ^n(l)`. Used by the
    /// normalizer on already-leaf bases (non-`Max`), so it uses `raw_succ` to
    /// avoid re-triggering normalization.
    fn add_offset(&self, n: u32) -> Level {
        let mut l = self.clone();
        for _ in 0..n {
            l = Level::raw_succ(l);
        }
        l
    }

    /// True iff `succ^n(Zero)` (a literal universe with no params).
    fn is_explicit(&self) -> bool {
        matches!(self.get_offset().0 .0, Repr::Zero)
    }

    // --- canonicalization (idempotent normal form) ---

    /// Produce the canonical form. Public smart constructors call this so that
    /// every `Level` a caller can hold is already canonical; exposed for tests.
    #[must_use]
    pub fn normalize(&self) -> Level {
        let (base, off) = self.get_offset();
        match &base.0 {
            Repr::Zero | Repr::Param(_) => base.add_offset(off),
            Repr::Succ(_) => unreachable!("get_offset strips all Succ"),
            Repr::IMax(l1, l2) => {
                let n1 = l1.normalize();
                let n2 = l2.normalize();
                let reduced = reduce_imax(n1, n2);
                if matches!(reduced.0, Repr::Max(_, _)) {
                    // Distribute the outer offset into the Max and renormalize so
                    // succ(max(a,b)) = max(succ a, succ b). Keeps idempotence.
                    reduced.add_offset(off).normalize()
                } else {
                    reduced.add_offset(off)
                }
            }
            Repr::Max(_, _) => normalize_max(&base, off),
        }
    }

    // --- ordering / def-eq ---

    /// `l1 >= l2` on canonical levels (the lattice partial order). Conservative
    /// over-approximation that is exact on canonical forms for the cases the
    /// kernel needs (Lean `level.cpp:is_geq`).
    #[must_use]
    pub fn is_geq(l1: &Level, l2: &Level) -> bool {
        is_geq_core(&l1.normalize(), &l2.normalize())
    }

    /// `l1 <= l2`.
    #[must_use]
    pub fn leq(l1: &Level, l2: &Level) -> bool {
        Level::is_geq(l2, l1)
    }

    /// Substitute positional `Param(i)` by `subst[i]` (universe instantiation),
    /// re-canonicalizing. A `Param` index out of range for `subst` is left
    /// unchanged — callers (δ-unfold, const-type instantiation) pass a `subst`
    /// of exactly `num_level_params` length, so in-range substitution is total;
    /// the clamp is defensive, never relied on for soundness.
    #[must_use]
    pub fn instantiate_params(&self, subst: &[Level]) -> Level {
        self.subst_raw(subst).normalize()
    }

    fn subst_raw(&self, subst: &[Level]) -> Level {
        match &self.0 {
            Repr::Zero => Level::zero(),
            Repr::Param(i) => match usize::try_from(*i).ok().and_then(|i| subst.get(i)) {
                Some(l) => l.clone(),
                None => self.clone(),
            },
            Repr::Succ(l) => Level(Repr::Succ(Arc::new(l.subst_raw(subst)))),
            Repr::Max(a, b) => Level(Repr::Max(
                Arc::new(a.subst_raw(subst)),
                Arc::new(b.subst_raw(subst)),
            )),
            Repr::IMax(a, b) => Level(Repr::IMax(
                Arc::new(a.subst_raw(subst)),
                Arc::new(b.subst_raw(subst)),
            )),
        }
    }
}

/// `imax` reduction given already-normalized children.
fn reduce_imax(l1: Level, l2: Level) -> Level {
    if l2.is_zero() {
        return Level::zero();
    }
    if l2.is_nonzero() {
        return Level::max(l1, l2);
    }
    if l1.is_zero() {
        return l2;
    }
    if l1 == Level::succ(Level::zero()) {
        return l2;
    }
    if l1 == l2 {
        return l1;
    }
    Level(Repr::IMax(Arc::new(l1), Arc::new(l2)))
}

/// Flatten a (possibly nested) `Max` tree into its leaf args.
fn push_max_args(l: &Level, out: &mut Vec<Level>) {
    match &l.0 {
        Repr::Max(a, b) => {
            push_max_args(a, out);
            push_max_args(b, out);
        }
        _ => out.push(l.clone()),
    }
}

/// Canonicalize a `Max`-rooted level (flatten, normalize children, sort, dedup,
/// subsume, reapply offset). Mirrors Lean `level.cpp` normalize for Max.
fn normalize_max(base: &Level, outer_offset: u32) -> Level {
    let mut todo = Vec::new();
    push_max_args(base, &mut todo);

    let mut args = Vec::new();
    for a in &todo {
        let normed = a.normalize();
        push_max_args(&normed, &mut args);
    }

    args.sort_by(|a, b| {
        if is_norm_lt(a, b) {
            Ordering::Less
        } else if is_norm_lt(b, a) {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    });

    let mut rargs = dedup_max_args(&args);

    if outer_offset > 0 {
        for a in &mut rargs {
            *a = a.add_offset(outer_offset);
        }
    }

    if rargs.is_empty() {
        Level::zero()
    } else {
        mk_max_from_args(&rargs)
    }
}

/// Rebuild a right-associated `Max` from sorted args (len >= 1).
fn mk_max_from_args(args: &[Level]) -> Level {
    debug_assert!(!args.is_empty());
    if args.len() == 1 {
        return args[0].clone();
    }
    let last = args.len().saturating_sub(1);
    let prev = args.len().saturating_sub(2);
    let mut r = Level(Repr::Max(
        Arc::new(args[prev].clone()),
        Arc::new(args[last].clone()),
    ));
    for i in (0..prev).rev() {
        r = Level(Repr::Max(Arc::new(args[i].clone()), Arc::new(r)));
    }
    r
}

/// Dedup sorted `Max` args: drop explicit levels subsumed by a parametric one
/// with >= offset, and merge same-base args keeping the largest offset.
fn dedup_max_args(args: &[Level]) -> Vec<Level> {
    let mut rargs: Vec<Level> = Vec::new();
    let mut i = 0usize;

    if !args.is_empty() && args[i].is_explicit() {
        while i.saturating_add(1) < args.len() && args[i.saturating_add(1)].is_explicit() {
            i = i.saturating_add(1);
        }
        let k = args[i].get_offset().1;
        let mut j = i.saturating_add(1);
        while j < args.len() {
            if args[j].get_offset().1 >= k {
                break;
            }
            j = j.saturating_add(1);
        }
        if j < args.len() {
            i = i.saturating_add(1);
        }
    }

    if i < args.len() {
        rargs.push(args[i].clone());
        let mut prev = args[i].get_offset();
        i = i.saturating_add(1);
        while i < args.len() {
            let cur = args[i].get_offset();
            if prev.0 == cur.0 {
                if prev.1 < cur.1 {
                    prev = cur;
                    rargs.pop();
                    rargs.push(args[i].clone());
                }
            } else {
                prev = cur;
                rargs.push(args[i].clone());
            }
            i = i.saturating_add(1);
        }
    }

    rargs
}

/// Total order used to sort `Max` args during normalization (Lean `is_norm_lt`):
/// order by base, then offset.
fn is_norm_lt(a: &Level, b: &Level) -> bool {
    let (ba, oa) = a.get_offset();
    let (bb, ob) = b.get_offset();
    let bc = base_cmp(&ba, &bb);
    match bc {
        Ordering::Less => true,
        Ordering::Greater => false,
        Ordering::Equal => oa < ob,
    }
}

/// A deterministic total order over level *bases* (post-offset-strip): order by
/// kind tag, then by structural contents.
fn base_cmp(a: &Level, b: &Level) -> Ordering {
    fn tag(l: &Level) -> u8 {
        match &l.0 {
            Repr::Zero => 0,
            Repr::Param(_) => 1,
            Repr::Max(_, _) => 2,
            Repr::IMax(_, _) => 3,
            Repr::Succ(_) => 4,
        }
    }
    let ta = tag(a);
    let tb = tag(b);
    if ta != tb {
        return ta.cmp(&tb);
    }
    match (&a.0, &b.0) {
        (Repr::Zero, Repr::Zero) => Ordering::Equal,
        (Repr::Param(x), Repr::Param(y)) => x.cmp(y),
        (Repr::Max(a1, a2), Repr::Max(b1, b2)) | (Repr::IMax(a1, a2), Repr::IMax(b1, b2)) => {
            base_cmp(a1, b1).then_with(|| base_cmp(a2, b2))
        }
        (Repr::Succ(x), Repr::Succ(y)) => base_cmp(x, y),
        _ => Ordering::Equal,
    }
}

/// `is_geq` on normalized inputs, recursive with the Lean rule order.
fn is_geq_core(l1: &Level, l2: &Level) -> bool {
    if l1 == l2 || l2.is_zero() {
        return true;
    }
    {
        let (base1, off1) = l1.get_offset();
        if off1 > 0 && base1 == *l2 {
            return true;
        }
    }
    if let Repr::Max(a, b) = &l2.0 {
        return is_geq_core(l1, a) && is_geq_core(l1, b);
    }
    if let Repr::Max(a, b) = &l1.0 {
        if is_geq_core(a, l2) || is_geq_core(b, l2) {
            return true;
        }
    }
    if let Repr::IMax(a, b) = &l2.0 {
        return is_geq_core(l1, a) && is_geq_core(l1, b);
    }
    if let Repr::IMax(_, b) = &l1.0 {
        return is_geq_core(b, l2);
    }
    let (base1, off1) = l1.get_offset();
    let (base2, off2) = l2.get_offset();
    if base1 == base2 || base2.is_zero() {
        return off1 >= off2;
    }
    if off1 == off2 && off1 > 0 {
        return is_geq_core(&base1, &base2);
    }
    false
}

impl std::fmt::Display for Level {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            Repr::Zero => write!(f, "0"),
            Repr::Param(i) => write!(f, "u{i}"),
            Repr::Succ(_) => {
                let (base, off) = self.get_offset();
                if matches!(base.0, Repr::Zero) {
                    write!(f, "{off}")
                } else {
                    write!(f, "{base}+{off}")
                }
            }
            Repr::Max(a, b) => write!(f, "max({a}, {b})"),
            Repr::IMax(a, b) => write!(f, "imax({a}, {b})"),
        }
    }
}
