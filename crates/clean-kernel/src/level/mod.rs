// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Universe levels
//!
//! Universe levels form a well-founded partial order used to stratify types
//! and avoid Russell's paradox.
//!
//! Key properties:
//! - `imax(l1, l2) = 0` if `l2 = 0`, otherwise `max(l1, l2)`
//! - This is used for Prop-elimination: `(x : Prop) → T` should have level `imax(0, level(T))`
//!   which is `level(T)` if `T` is a type, but `0` if `T` is also Prop.

use crate::expr::stack_safe;
use crate::name::Name;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

// Type alias for Arc<Level> that avoids CBMC unwinding under Kani.
//
// Under cfg(kani), use ManuallyDrop<Box<Level>> instead of Arc<Level>.
// Box eliminates Arc's atomic refcount operations (Arc::clone, Arc::drop_slow)
// that CBMC must model, reducing solver complexity. ManuallyDrop suppresses
// the drop_in_place code generation entirely. This is the same pattern as
// NameInner (name.rs:161) but with Box replacing Arc to remove the remaining
// CBMC overhead from atomic operations inside ManuallyDrop<Arc<Level>>.
//
// Sound: Kani harnesses verify value semantics, not deallocation or
// thread-safety correctness. Box has identical Deref behavior to Arc.
#[cfg(not(kani))]
/// Stack-safe shared ownership edge used by recursive [`Level`] variants.
///
/// This type is public because it appears in the fields of the public `Level`
/// enum.  Its representation remains private so an empty edge cannot be
/// constructed; use the `Level` constructors rather than constructing
/// recursive variants directly.
pub struct LevelArc(Option<Arc<Level>>);
#[cfg(kani)]
pub type LevelArc = std::mem::ManuallyDrop<Box<Level>>;

#[cfg(not(kani))]
impl Clone for LevelArc {
    fn clone(&self) -> Self {
        Self(Some(
            self.0
                .as_ref()
                .expect("live LevelArc must contain a level")
                .clone(),
        ))
    }
}

#[cfg(not(kani))]
impl std::ops::Deref for LevelArc {
    type Target = Level;

    fn deref(&self) -> &Self::Target {
        self.0
            .as_deref()
            .expect("live LevelArc must contain a level")
    }
}

#[cfg(not(kani))]
impl From<Level> for LevelArc {
    fn from(level: Level) -> Self {
        Self(Some(Arc::new(level)))
    }
}

#[cfg(not(kani))]
impl From<Arc<Level>> for LevelArc {
    fn from(level: Arc<Level>) -> Self {
        Self(Some(level))
    }
}

#[cfg(not(kani))]
impl AsRef<Level> for LevelArc {
    fn as_ref(&self) -> &Level {
        self
    }
}

#[cfg(not(kani))]
impl std::borrow::Borrow<Level> for LevelArc {
    fn borrow(&self) -> &Level {
        self
    }
}

#[cfg(not(kani))]
impl PartialEq for LevelArc {
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

#[cfg(not(kani))]
impl Eq for LevelArc {}

#[cfg(not(kani))]
impl std::hash::Hash for LevelArc {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (**self).hash(state);
    }
}

#[cfg(not(kani))]
impl std::fmt::Debug for LevelArc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&**self, f)
    }
}

#[cfg(not(kani))]
impl Drop for LevelArc {
    fn drop(&mut self) {
        let Some(level) = self.0.take() else {
            return;
        };
        // Every recursive ownership edge re-enters the growth boundary. The
        // Option lets Drop take ownership without a replacement allocation,
        // while `Level` itself remains a move-friendly public enum.
        stack_safe(move || drop(level));
    }
}

/// Wrap a Level in LevelArc. Under Kani, uses ManuallyDrop<Box<Level>>
/// to eliminate Arc atomic operations from CBMC analysis.
#[inline(always)]
pub(crate) fn level_arc(l: Level) -> LevelArc {
    #[cfg(not(kani))]
    {
        LevelArc::from(l)
    }
    #[cfg(kani)]
    {
        std::mem::ManuallyDrop::new(Box::new(l))
    }
}

/// Universe level for type hierarchy.
///
/// Universe levels form a hierarchy that avoids paradoxes like Russell's paradox.
/// `Prop` is at level 0, `Type` at level 1, `Type 1` at level 2, etc.
///
/// # Example
///
/// ```
/// use clean_kernel::{Level, Name};
///
/// // Prop is Sort 0
/// let prop_level = Level::zero();
///
/// // Type is Sort 1 (succ of 0)
/// let type_level = Level::succ(Level::zero());
///
/// // Type 2 is Sort 3 (add three succs)
/// let type2_level = Level::zero().add_offset(3);
///
/// // Universe polymorphism with parameters
/// let u_name = Name::from_string("u");
/// let u = Level::param(u_name);
/// let succ_u = Level::succ(u);
/// ```
// Under Kani, Serialize/Deserialize are manual impls (ManuallyDrop doesn't
// derive Serialize). PartialEq/Eq are manual impls because derived PartialEq
// recurses through ManuallyDrop<Box<Level>> causing CBMC to unwind
// Level::eq unboundedly. Clone/Debug work via ManuallyDrop's Deref.
// CRYSTAL TAG PIN — the DECLARATION ORDER below is load-bearing.
//
// `Level::is_zero` (the designated crystal target) and `Level::kind_ord` are
// registered chains. Their emitted trust-ir switches on the numeric
// discriminant — `switch %4 [ 0: bb1 1: bb2 4: bb3 2: bb4 default: bb5 ]` for
// `is_zero` — and Clean's side encodes the same numbers in `level_kind_tag`
// (`crates/clean-verify/src/spec/core_spec/eval_ir_kind_ord.rs`), which maps
// Zero/Succ/Max/IMax/Param to 0/1/2/3/4 by DECLARATION INDEX. Reordering these
// variants therefore silently makes both registered modules theorems about a
// body that is no longer shipped, without changing one line of either module.
//
// Unlike `CleanMode`, `SourceSystem` and `ExprPathStep`, this enum carries
// payloads, so it is pinned by `data/crystal_enum_tag_pin.json` +
// `scripts/check_enum_tag_pin.py` and NOT by `#[repr(u8)]`: adding a repr here
// is a layout change to the kernel's hottest type, it can move the emitted
// bytes, and moving them would stale every recorded lineage digest on the
// designated chain (`fixtures/level_is_zero.trust-ir.txt`,
// `fixtures/level_is_zero.a0.json`). That flip needs its own differential
// measurement; the gate closes the reorder hole today without taking it.
// See `docs/CRYSTAL_STATUS.md`.
#[must_use = "levels should be inspected or passed onward"]
#[cfg_attr(not(kani), derive(Clone))]
pub enum Level {
    /// Zero (the lowest level)
    Zero,
    /// Successor: l + 1
    Succ(LevelArc),
    /// Maximum: max(l1, l2)
    Max(LevelArc, LevelArc),
    /// Impredicative maximum: imax(l1, l2) = 0 if l2 = 0, else max(l1, l2)
    IMax(LevelArc, LevelArc),
    /// Universe parameter (polymorphism)
    Param(Name),
}

impl std::fmt::Debug for Level {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Zero => f.write_str("Zero"),
            Self::Succ(child) => f
                .debug_tuple("Succ")
                .field(&LevelChildDebug(child))
                .finish(),
            Self::Max(left, right) => f
                .debug_tuple("Max")
                .field(&LevelChildDebug(left))
                .field(&LevelChildDebug(right))
                .finish(),
            Self::IMax(left, right) => f
                .debug_tuple("IMax")
                .field(&LevelChildDebug(left))
                .field(&LevelChildDebug(right))
                .finish(),
            Self::Param(name) => f.debug_tuple("Param").field(name).finish(),
        }
    }
}

struct LevelChildDebug<'a>(&'a Level);

impl std::fmt::Debug for LevelChildDebug<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Level::Zero => f.write_str("Zero"),
            Level::Succ(_) => f.write_str("Succ(..)"),
            Level::Max(_, _) => f.write_str("Max(..)"),
            Level::IMax(_, _) => f.write_str("IMax(..)"),
            Level::Param(name) => f.debug_tuple("Param").field(name).finish(),
        }
    }
}

// Manual serde keeps the exact derived enum wire format while
// putting every recursive Level edge behind `stack_safe`.  A derived impl
// descends through Arc<Level> on the native thread stack and can abort the
// process before a carrier-level depth limit gets a chance to reject input.
impl Serialize for Level {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeTupleVariant;

        stack_safe(|| match self {
            Level::Zero => serializer.serialize_unit_variant("Level", 0, "Zero"),
            // `Succ` and `Param` are newtype variants in the derived serde
            // contract. A one-field tuple variant happens to match bincode,
            // but changes self-describing formats such as JSON and cannot be
            // decoded by the derived mirror. Preserve the exact variant shape.
            Level::Succ(l) => serializer.serialize_newtype_variant("Level", 1, "Succ", &**l),
            Level::Max(l1, l2) => {
                let mut tv = serializer.serialize_tuple_variant("Level", 2, "Max", 2)?;
                tv.serialize_field(&**l1)?;
                tv.serialize_field(&**l2)?;
                tv.end()
            }
            Level::IMax(l1, l2) => {
                let mut tv = serializer.serialize_tuple_variant("Level", 3, "IMax", 2)?;
                tv.serialize_field(&**l1)?;
                tv.serialize_field(&**l2)?;
                tv.end()
            }
            Level::Param(name) => serializer.serialize_newtype_variant("Level", 4, "Param", name),
        })
    }
}

#[cfg(not(kani))]
impl<'de> Deserialize<'de> for Level {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let _decode_node = crate::serde_budget::enter_decode_node::<D::Error>("universe level")?;
        // Box and Arc have the same transparent serde representation.  Using
        // Box here lets the wire helper call this custom Level impl for every
        // child, then we restore the kernel's Arc representation without
        // running simplifying constructors (which would change the decoded
        // structural value).
        #[derive(Deserialize)]
        #[serde(rename = "Level")]
        enum LevelWire {
            Zero,
            Succ(Box<Level>),
            Max(Box<Level>, Box<Level>),
            IMax(Box<Level>, Box<Level>),
            Param(Name),
        }

        stack_safe(|| {
            Ok(match LevelWire::deserialize(deserializer)? {
                LevelWire::Zero => Level::Zero,
                LevelWire::Succ(l) => Level::Succ(level_arc(*l)),
                LevelWire::Max(l1, l2) => Level::Max(level_arc(*l1), level_arc(*l2)),
                LevelWire::IMax(l1, l2) => Level::IMax(level_arc(*l1), level_arc(*l2)),
                LevelWire::Param(name) => Level::Param(name),
            })
        })
    }
}

// Production Hash: matches derived behavior (discriminant + recursive field hashing).
// Separated from derive to allow cfg(kani) override below.
#[cfg(not(kani))]
impl std::hash::Hash for Level {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Preserve derived Hash's pre-order sequence without recursive
        // Arc<Level>::hash descent.
        let mut pending = vec![self];
        while let Some(level) = pending.pop() {
            std::mem::discriminant(level).hash(state);
            match level {
                Level::Zero => {}
                Level::Succ(child) => pending.push(child),
                Level::Max(left, right) | Level::IMax(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                Level::Param(name) => name.hash(state),
            }
        }
    }
}

// Kani Hash: shallow discriminant-only hash to avoid CBMC unwinding through
// recursive Arc<Level> trees. The derived Hash recurses into Succ/Max/IMax
// children causing unbounded unwinding (observed as "Level::hash::<KaniHasher>
// iteration 6+" timeouts). This is sound because: (1) Hash only requires that
// equal values hash equally, (2) discriminant-only hashing satisfies this
// (it's just less discriminating), (3) harnesses verify value semantics not
// hash distribution quality.
#[cfg(kani)]
impl std::hash::Hash for Level {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        // Don't recurse into Arc<Level> children — CBMC can't bound the depth.
        // For Param, Name::hash is O(1) via cached_hash so it's safe.
        if let Level::Param(n) = self {
            n.hash(state);
        }
    }
}

// Structural comparison is iterative in every build. Besides keeping Kani's
// model finite, this protects native callers comparing attacker-deep levels.
impl PartialEq for Level {
    fn eq(&self, other: &Self) -> bool {
        // Fully iterative comparison using an explicit stack to eliminate
        // all function recursion from CBMC's analysis.
        let mut stack: Vec<(&Level, &Level)> = vec![(self, other)];
        while let Some((a, b)) = stack.pop() {
            match (a, b) {
                (Level::Zero, Level::Zero) => {}
                (Level::Succ(la), Level::Succ(lb)) => {
                    stack.push((la, lb));
                }
                (Level::Max(la1, la2), Level::Max(lb1, lb2))
                | (Level::IMax(la1, la2), Level::IMax(lb1, lb2)) => {
                    stack.push((la1, lb1));
                    stack.push((la2, lb2));
                }
                (Level::Param(na), Level::Param(nb)) => {
                    if na != nb {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }
}

impl Eq for Level {}

/// Iterative Clone for CBMC: strips Succ chain with get_offset, clones the
/// base, then rebuilds Succ layers in a loop. Avoids recursive
/// ManuallyDrop<Box<Level>>::clone chains that generate exponential SAT formulas.
#[cfg(kani)]
impl Clone for Level {
    fn clone(&self) -> Self {
        let (base, offset) = self.get_offset();
        let cloned_base = match base {
            Level::Zero => Level::Zero,
            Level::Param(n) => Level::Param(n.clone()),
            Level::Max(a, b) => Level::Max(level_arc(Level::clone(a)), level_arc(Level::clone(b))),
            Level::IMax(a, b) => {
                Level::IMax(level_arc(Level::clone(a)), level_arc(Level::clone(b)))
            }
            Level::Succ(_) => unreachable!("get_offset strips all Succ layers"),
        };
        let mut result = cloned_base;
        for _ in 0..offset {
            result = Level::succ(result);
        }
        result
    }
}

// Previous cfg(kani) Level Drop (mem::replace + mem::forget) removed:
// With ManuallyDrop<Box<Level>> in Succ/Max/IMax (LevelArc), the compiler
// no longer generates drop_in_place code. The field drop glue sees
// ManuallyDrop (no-op drop) instead of Box (heap dealloc). Box replaces Arc
// to also eliminate atomic refcount operations from CBMC analysis. Name (in
// Param) uses ManuallyDrop internally via NameInner, so its drop is lightweight.

// Manual Deserialize for cfg(kani) Level: never called by Kani harnesses.
#[cfg(kani)]
impl<'de> Deserialize<'de> for Level {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let _ = deserializer;
        Ok(Level::Zero)
    }
}

impl Level {
    /// Create zero level.
    ///
    /// # Contract
    ///
    /// ENSURES: `result.is_zero() == true`
    pub fn zero() -> Self {
        Level::Zero
    }

    /// Create successor level.
    ///
    /// # Contract
    ///
    /// ENSURES: `result.is_nonzero() == true`
    /// ENSURES: `result.get_offset().1 == l.get_offset().1 + 1`
    pub fn succ(l: Level) -> Self {
        Level::Succ(level_arc(l))
    }

    /// Create max level, simplifying if possible.
    ///
    /// # Contract
    ///
    /// ENSURES: `max(a, b) == max(b, a)` (commutative)
    /// ENSURES: `max(a, a) == a` (idempotent)
    /// ENSURES: `max(0, a) == a` (identity)
    /// ENSURES: `is_geq(&max(a, b), &a) && is_geq(&max(a, b), &b)`
    pub fn max(l1: Level, l2: Level) -> Self {
        // Simplifications:
        // max(l, l) = l
        // max(0, l) = l
        // max(l, 0) = l
        if l1 == l2 {
            return l1;
        }
        if l1.is_zero() {
            return l2;
        }
        if l2.is_zero() {
            return l1;
        }
        // Under cfg(kani), skip is_geq subsumption to break mutual recursion:
        // max → is_geq → normalize → imax → max. The normalize step handles
        // subsumption during canonicalization, so this only produces less-simplified
        // intermediate Max nodes. Correctness is preserved.
        #[cfg(not(kani))]
        {
            // Check if one is definitely >= the other
            if Level::is_geq(&l1, &l2) {
                return l1;
            }
            if Level::is_geq(&l2, &l1) {
                return l2;
            }
        }
        Level::Max(level_arc(l1), level_arc(l2))
    }

    /// Create imax level, simplifying if possible.
    ///
    /// `imax(l1, l2) = 0` if `l2 = 0`, else `max(l1, l2)`.
    /// Used for Prop-elimination: `(x : Prop) → T` has level `imax(0, level(T))`.
    ///
    /// # Contract
    ///
    /// ENSURES: `l2.is_zero() ==> result.is_zero()` (key property)
    /// ENSURES: `l2.is_nonzero() ==> result == max(l1, l2)`
    /// ENSURES: `(l1.is_zero() || l1 == Succ(Zero)) && !l2.is_zero() ==> result == l2`
    /// ENSURES: `l1 == l2 ==> result == l1`
    /// ENSURES: Otherwise, `result` is an `IMax` with `(l1, l2)`
    pub fn imax(l1: Level, l2: Level) -> Self {
        // imax(l, 0) = 0
        if l2.is_zero() {
            return Level::Zero;
        }
        // imax(l, l') = max(l, l') when l' is definitely nonzero
        // Lean 4 parity: mk_imax uses is_not_zero(l2) which recurses into Max/IMax,
        // not just a syntactic Succ check. E.g. imax(u, max(v, succ(w))) reduces to
        // max(u, max(v, succ(w))) because max(v, succ(w)) is semantically nonzero.
        if l2.is_nonzero() {
            return Level::max(l1, l2);
        }
        // imax(0, l) = l (if l != 0, which we handled above)
        if l1.is_zero() {
            return l2;
        }
        // imax(1, l) = l (Lean 4 parity: is_one(l1))
        // Proof: imax(1, 0) = 0 (handled above), imax(1, l) = max(1, l) = l when l > 0.
        if l1 == Level::succ(Level::zero()) {
            return l2;
        }
        // imax(l, l) = l
        if l1 == l2 {
            return l1;
        }
        Level::IMax(level_arc(l1), level_arc(l2))
    }

    /// Create parameter level.
    ///
    /// # Contract
    ///
    /// ENSURES: `result.has_params() == true`
    pub fn param(name: Name) -> Self {
        Level::Param(name)
    }

    /// Check if this is definitely zero.
    ///
    /// # Contract
    ///
    /// ENSURES: `is_zero() && is_nonzero()` is false (mutual exclusion)
    /// ENSURES: `Zero.is_zero() == true`
    pub fn is_zero(&self) -> bool {
        match self {
            Level::Zero => true,
            Level::Succ(_) | Level::Param(_) => false, // Succ always > 0; Params might be 0 at runtime
            Level::Max(l1, l2) => l1.is_zero() && l2.is_zero(),
            Level::IMax(_, l2) => l2.is_zero(), // imax(_, 0) = 0
        }
    }

    /// Check if this is definitely nonzero (i.e., definitely > 0).
    ///
    /// # Contract
    ///
    /// ENSURES: `is_zero() && is_nonzero()` is false (mutual exclusion)
    /// ENSURES: `Succ(_).is_nonzero() == true`
    pub(crate) fn is_nonzero(&self) -> bool {
        match self {
            Level::Zero | Level::Param(_) => false, // Zero is 0; Params might be 0
            Level::Succ(_) => true,                 // succ(l) > 0 for all l
            Level::Max(l1, l2) => l1.is_nonzero() || l2.is_nonzero(),
            Level::IMax(_, l2) => l2.is_nonzero(), // If l2 > 0, imax reduces to max
        }
    }

    /// Get the base level and offset (number of Succ applications).
    ///
    /// Example: `succ(succ(u))` => `(u, 2)`
    ///
    /// # Contract
    ///
    /// ENSURES: If `self` is not `Succ`, then `result == (self, 0)`
    /// ENSURES: For `Succ(inner)`, `result.1 == inner.get_offset().1 + 1`
    pub(crate) fn get_offset(&self) -> (&Level, u32) {
        // Iterative implementation to avoid stack overflow on deeply nested Succs
        let mut current = self;
        let mut offset = 0u32;
        while let Level::Succ(inner) = current {
            offset = offset.saturating_add(1);
            current = inner;
        }
        (current, offset)
    }

    /// Add an offset to a level.
    ///
    /// # Contract
    ///
    /// ENSURES: `result.get_offset().1 == self.get_offset().1.saturating_add(n)`
    /// ENSURES: `add_offset(0) == self` (identity)
    pub fn add_offset(&self, n: u32) -> Level {
        // Iterative implementation to avoid stack overflow on large n
        let mut result = self.clone();
        for _ in 0..n {
            result = Level::succ(result);
        }
        result
    }

    /// Normalize the level to a canonical form.
    ///
    /// # Contract
    ///
    /// ENSURES: `normalize(normalize(l)) == normalize(l)` (idempotent)
    /// ENSURES: `is_def_eq(l, normalize(l))` (preserves semantics)
    ///
    /// Uses stack_safe for stack overflow protection on deeply nested levels.
    pub fn normalize(&self) -> Level {
        stack_safe(|| self.normalize_impl())
    }

    /// Ordering key for level kind, matching Lean 4's level_kind enum order.
    /// Used by `is_norm_lt` for canonical sorting.
    /// Lean 4: Zero=0, Succ=1, Max=2, IMax=3, Param=4, MVar=5
    /// (clean has no MVar)
    fn kind_ord(&self) -> u8 {
        match self {
            Level::Zero => 0,
            Level::Succ(_) => 1,
            Level::Max(_, _) => 2,
            Level::IMax(_, _) => 3,
            Level::Param(_) => 4,
        }
    }

    /// Total ordering on normalized level expressions, matching Lean 4's `is_norm_lt`.
    /// After `get_offset`, bases are compared by kind then by structure;
    /// for equal bases, offsets are compared.
    ///
    /// Reference: lean4/src/kernel/level.cpp:380-403
    fn is_norm_lt(a: &Level, b: &Level) -> bool {
        // Under cfg(kani), use iterative tail-call conversion to eliminate
        // function recursion that causes CBMC exponential unwinding.
        #[cfg(kani)]
        {
            let mut a = a;
            let mut b = b;
            loop {
                if a == b {
                    return false;
                }
                let (base1, off1) = a.get_offset();
                let (base2, off2) = b.get_offset();
                if base1 != base2 {
                    if base1.kind_ord() != base2.kind_ord() {
                        return base1.kind_ord() < base2.kind_ord();
                    }
                    match (base1, base2) {
                        (Level::Param(n1), Level::Param(n2)) => return n1 < n2,
                        (Level::Max(a1, b1), Level::Max(a2, b2))
                        | (Level::IMax(a1, b1), Level::IMax(a2, b2)) => {
                            if a1 != a2 {
                                a = a1;
                                b = a2;
                                continue;
                            } else {
                                a = b1;
                                b = b2;
                                continue;
                            }
                        }
                        _ => return false,
                    }
                } else {
                    return off1 < off2;
                }
            }
        }
        #[cfg(not(kani))]
        {
            if a == b {
                return false;
            }
            let (base1, off1) = a.get_offset();
            let (base2, off2) = b.get_offset();
            if base1 != base2 {
                if base1.kind_ord() != base2.kind_ord() {
                    return base1.kind_ord() < base2.kind_ord();
                }
                match (base1, base2) {
                    // Structural ordering matching Lean 4's cmp_core (#1316)
                    (Level::Param(n1), Level::Param(n2)) => n1 < n2,
                    (Level::Max(a1, b1), Level::Max(a2, b2))
                    | (Level::IMax(a1, b1), Level::IMax(a2, b2)) => {
                        if a1 != a2 {
                            stack_safe(|| Self::is_norm_lt(a1, a2))
                        } else {
                            stack_safe(|| Self::is_norm_lt(b1, b2))
                        }
                    }
                    // Zero and Succ are unreachable as bases after get_offset
                    _ => false,
                }
            } else {
                off1 < off2
            }
        }
    }

    /// Flatten a `Max` tree into a buffer of non-Max arguments.
    /// Reference: lean4/src/kernel/level.cpp:405-412
    fn push_max_args(l: &Level, buf: &mut Vec<Level>) {
        // Under cfg(kani), use an explicit stack to avoid function recursion
        // that causes CBMC exponential unwinding.
        #[cfg(kani)]
        {
            let mut stack: Vec<&Level> = vec![l];
            while let Some(current) = stack.pop() {
                match current {
                    Level::Max(a, b) => {
                        // Push right first so left is processed first (preserves order)
                        stack.push(b);
                        stack.push(a);
                    }
                    _ => buf.push(current.clone()),
                }
            }
        }
        #[cfg(not(kani))]
        {
            match l {
                Level::Max(a, b) => {
                    stack_safe(|| Self::push_max_args(a, buf));
                    stack_safe(|| Self::push_max_args(b, buf));
                }
                _ => buf.push(l.clone()),
            }
        }
    }

    /// Rebuild a right-associated Max tree from a list of args.
    /// Reference: lean4/src/kernel/level.cpp:414-429
    fn mk_max_from_args(args: &[Level]) -> Level {
        debug_assert!(!args.is_empty());
        if args.len() == 1 {
            return args[0].clone();
        }
        // Build right-to-left: max(args[0], max(args[1], max(...)))
        let mut r = Level::Max(
            level_arc(args[args.len() - 2].clone()),
            level_arc(args[args.len() - 1].clone()),
        );
        for i in (0..args.len() - 2).rev() {
            r = Level::Max(level_arc(args[i].clone()), level_arc(r));
        }
        r
    }

    /// Check if this level is "explicit" (i.e., succ^n(Zero) with no params).
    /// Uses iterative `get_offset` to avoid stack overflow on deep Succ chains.
    /// Reference: lean4/src/kernel/level.cpp:54-64
    fn is_explicit(&self) -> bool {
        matches!(self.get_offset().0, Level::Zero)
    }

    /// Implementation of normalize (called via stack_safe)
    ///
    /// Matches Lean 4's approach: first strip outer offset with `get_offset`,
    /// then dispatch on the base kind. For Max bases, performs full
    /// canonicalization (flatten/sort/dedup/subsume) and distributes the
    /// outer offset into each arg.
    ///
    /// # Contract
    ///
    /// ENSURES: `normalize_impl(l) == normalize(l)`
    ///
    /// Reference: lean4/src/kernel/level.cpp:439-499
    fn normalize_impl(&self) -> Level {
        let (base, outer_offset) = self.get_offset();

        match base {
            // Zero and Param are already normal; just re-wrap with offset.
            // Under cfg(kani), reconstruct iteratively instead of recursive clone
            // to avoid deep Box<Level>::clone chains that exhaust CBMC.
            Level::Zero | Level::Param(_) => {
                #[cfg(kani)]
                {
                    let mut result = match base {
                        Level::Zero => Level::Zero,
                        Level::Param(n) => Level::Param(n.clone()),
                        _ => unreachable!(),
                    };
                    for _ in 0..outer_offset {
                        result = Level::succ(result);
                    }
                    result
                }
                #[cfg(not(kani))]
                {
                    self.clone()
                }
            }
            // Succ is unreachable as a base after get_offset
            Level::Succ(_) => unreachable!("get_offset strips all Succ layers"),

            Level::IMax(l1, l2) => {
                let l1_norm = stack_safe(|| l1.normalize_impl());
                let l2_norm = stack_safe(|| l2.normalize_impl());
                // Rebuild imax with normalized children (smart constructor handles
                // reduction to max/zero), then re-wrap with outer offset.
                let result = Level::imax(l1_norm, l2_norm);
                // If imax reduced to a Max, add offset first then re-normalize
                // so that Succ distributes over Max (Succ(Max(a,b)) → Max(Succ(a),Succ(b))).
                // This ensures idempotent normalization (#1436).
                if matches!(result, Level::Max(_, _)) {
                    stack_safe(|| result.add_offset(outer_offset).normalize_impl())
                } else {
                    result.add_offset(outer_offset)
                }
            }

            Level::Max(_, _) => Self::normalize_max(base, outer_offset),
        }
    }

    /// Normalize a Max-based level: flatten, normalize children, sort, dedup, subsume.
    /// Extracted from normalize_impl to keep function sizes under 80 lines.
    /// Reference: lean4/src/kernel/level.cpp:455-499
    fn normalize_max(base: &Level, outer_offset: u32) -> Level {
        // Step 1: Flatten the Max tree into individual args
        let mut todo = Vec::new();
        Self::push_max_args(base, &mut todo);

        // Step 2: Normalize each arg, then re-flatten
        // (normalization may produce new Max nodes from IMax reduction)
        let mut args = Vec::new();
        for a in &todo {
            let normed = stack_safe(|| a.normalize_impl());
            Self::push_max_args(&normed, &mut args);
        }

        // Step 3: Sort with is_norm_lt
        args.sort_by(|a, b| {
            if Self::is_norm_lt(a, b) {
                std::cmp::Ordering::Less
            } else if Self::is_norm_lt(b, a) {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        });

        // Step 4: Deduplicate same-base args (keep largest offset) + explicit
        // subsumption.
        let deduped = Self::dedup_max_args(&args);

        // Step 5: Semantic subsumption — drop any arg dominated by another
        // retained arg (e.g. `u_1` dominated by `imax(u, u_1)`). This closes
        // the `max k (imax a b)` / nested-max canonicalization gap that the
        // structural same-base dedup misses. See `subsume_max_args`.
        let mut rargs = Self::subsume_max_args(&deduped);

        // Step 6: Reapply outer offset
        if outer_offset > 0 {
            for a in &mut rargs {
                *a = a.add_offset(outer_offset);
            }
        }

        if rargs.is_empty() {
            Level::Zero
        } else {
            Self::mk_max_from_args(&rargs)
        }
    }

    /// Semantic subsumption pass over normalized Max args: drop any arg `x` that
    /// is dominated (`>=`) by another retained arg `y`, since `max(x, y) = y`
    /// when `y >= x` for all parameter assignments; then drop any arg dominated
    /// by the JOIN (`max`) of the OTHER retained args (join-subsumption).
    ///
    /// SOUNDNESS: an arg is dropped ONLY when `is_geq_core(dominator, x)` returns
    /// true, and `is_geq` is a CONSERVATIVE under-approximation — it returns true
    /// only when `dominator >= x` holds for EVERY assignment (it never claims a
    /// `>=` that is not semantically valid). This holds for BOTH the single-arg
    /// dominator `y` and the join dominator `mk_max(others)`: since
    /// `eval(mk_max(others)) = max_i eval(others_i)`, `is_geq_core(mk_max(others),
    /// x) == true` implies `max_i eval(others_i) >= eval(x)` at every assignment,
    /// so `max(others, x) = max(others)` — dropping `x` preserves the level's
    /// denotation EXACTLY. Therefore neither pass can equate two unequal levels
    /// (no false-accept). The exhaustive differential harness
    /// (`level::soundness_harness`) machine-checks this: zero false-accepts over
    /// the full depth-3 / 3-param enumeration (10.5M ordered pairs) and a
    /// bounded depth-5 enumeration, and it EXERCISES the join rule (adversarial
    /// imax shapes where a naive join drop would be unsound are guarded because
    /// `is_geq_core` correctly returns false for them).
    ///
    /// Inputs are already normalized (callers normalize each arg before this),
    /// so `is_geq_core` is invoked directly — it does NOT re-normalize, so there
    /// is no recursion back into `normalize` / `normalize_max` and termination
    /// is guaranteed (`is_geq_core` recurses only on strict subterms; the join
    /// pass is a strictly-shrinking fixpoint, so it terminates in `<= k` rounds).
    ///
    /// For mutually-dominating (semantically equal) args, exactly one is kept:
    /// an arg is dropped only if dominated by an arg at a STRICTLY EARLIER index
    /// among the retained set, or by a strictly-later arg that does not itself
    /// get dropped — implemented as "keep `x` unless some other retained `y`
    /// dominates it", scanning a stable retained prefix so a tie keeps the
    /// earlier-indexed arg and never drops both.
    ///
    /// COST: the relevant candidate dominators are restricted to the COMPOSITE
    /// args (those whose `get_offset` base is `Max`/`IMax`). A SIMPLE arg (base
    /// `Zero`/`Param`, possibly with a `Succ` offset) can only be `is_geq`-
    /// dominated by a same-base arg — and `dedup_max_args` already merged all
    /// same-base args (one per base) — or by a composite arg. So checking simple
    /// args only against composites is EXACT, and the common case (no composite
    /// args, e.g. a wide `max` of distinct params) costs O(k) instead of O(k^2).
    /// `is_geq_core(p_i, p_j)` for distinct param bases is always false, so the
    /// skipped simple-vs-simple pairs could never have subsumed.
    fn subsume_max_args(args: &[Level]) -> Vec<Level> {
        if args.len() <= 1 {
            return args.to_vec();
        }
        // A composite arg can absorb a simpler arg; a simple arg cannot absorb a
        // different-base simple arg (and same-base were merged by dedup).
        let is_composite =
            |l: &Level| matches!(l.get_offset().0, Level::Max(_, _) | Level::IMax(_, _));
        // Fast path: with NO composite arg, no arg can subsume another beyond the
        // same-base dedup already performed. A simple arg `p_i` is `is_geq`-
        // dominated only by a same-base arg (merged) or a composite (none here),
        // and the join `max(p_j...)` of distinct-base simple args never dominates
        // a fresh simple `p_i` (`is_geq_core(max(others), p_i)` requires some
        // `others_k >= p_i`, impossible for distinct param bases). So nothing to
        // do — keep the common wide-`max`-of-params case at O(k).
        if !args.iter().any(is_composite) {
            return args.to_vec();
        }

        // Unified subsumption fixpoint. Each round, drop the FIRST arg `x` that
        // is dominated by the JOIN (`max`) of ALL OTHER currently-retained args:
        //   is_geq_core(mk_max(kept \ {x}), x) == true.
        // This uniformly captures BOTH single-arg subsumption (a lone dominator
        // makes the join dominate) AND join-subsumption where `x` is covered only
        // by the max of several others — e.g. WF-recursion constants emit
        // `imax (succ u) (imax (succ u) u_2)`, dominated by `max(succ u, u_2)`
        // (the join of two siblings) but by no single sibling.
        //
        // SOUNDNESS: `is_geq_core` is a conservative under-approximation, so a
        // drop fires only when `max(others) >= x` at EVERY assignment; then
        // `max(others, x) = max(others)` and removing `x` preserves the
        // denotation EXACTLY. Every single removal is denotation-preserving, so
        // the whole fixpoint is (regardless of which order args are dropped in).
        //
        // COMPLETENESS/ORDER: when several args are simultaneously droppable, we
        // prefer to drop a COMPOSITE arg. A composite dominated by the join of
        // simpler siblings is the redundant, re-expressible one; dropping a
        // SIMPLE sibling first could consume the witness the composite needs and
        // get stuck (e.g. dropping `u_2` would leave `imax(succ u,imax(succ u,
        // u_2))` un-droppable — its `u_2` witness gone). Preferring composites
        // yields the minimal normal form. Order never affects soundness.
        //
        // TIE-SAFETY: two mutually-equal args are each dominated by the other
        // alone; we drop only ONE per round, then re-check the survivor against
        // the SHRUNK set — if its only dominator was the dropped arg it is now
        // kept, so we never drop both.
        //
        // TERMINATION: each round removes exactly one arg (strictly shrinking) or
        // returns; `is_geq_core` recurses only on strict subterms of already-
        // normalized inputs, so there is no recursion back into `normalize`.
        let mut kept: Vec<Level> = args.to_vec();
        loop {
            if kept.len() <= 1 {
                return kept;
            }
            // Find droppable args this round, preferring a composite.
            let mut drop_idx: Option<usize> = None;
            let mut drop_simple_idx: Option<usize> = None;
            for i in 0..kept.len() {
                // Join of all OTHER retained args (order preserved). With
                // kept.len() >= 2 this is either a single arg (single-arg
                // subsumption) or a real Max node (join subsumption).
                let others: Vec<Level> = kept
                    .iter()
                    .enumerate()
                    .filter_map(|(j, l)| if j == i { None } else { Some(l.clone()) })
                    .collect();
                let join = Self::mk_max_from_args(&others);
                if stack_safe(|| Self::is_geq_core(&join, &kept[i])) {
                    if is_composite(&kept[i]) {
                        drop_idx = Some(i);
                        break; // composite: highest drop priority.
                    } else if drop_simple_idx.is_none() {
                        drop_simple_idx = Some(i); // remember, keep scanning.
                    }
                }
            }
            match drop_idx.or(drop_simple_idx) {
                Some(i) => {
                    let _dropped = kept.remove(i);
                }
                None => return kept,
            }
        }
    }

    /// Deduplicate and subsume sorted Max args: remove explicit levels subsumed
    /// by parametric ones, and merge same-base args keeping the largest offset.
    /// Reference: lean4/src/kernel/level.cpp:463-494
    fn dedup_max_args(args: &[Level]) -> Vec<Level> {
        let mut rargs: Vec<Level> = Vec::new();
        let mut i = 0;

        // Handle explicit level subsumption (Lean 4 lines 463-478)
        if args[i].is_explicit() {
            // Find the largest explicit universe
            while i + 1 < args.len() && args[i + 1].is_explicit() {
                i += 1;
            }
            // args[i] is now the largest explicit level
            let k = args[i].get_offset().1;
            // Check if it's subsumed by a non-explicit arg with offset >= k
            let mut j = i + 1;
            while j < args.len() {
                if args[j].get_offset().1 >= k {
                    break;
                }
                j += 1;
            }
            if j < args.len() {
                // Explicit universe was subsumed
                i += 1;
            }
        }

        // Process remaining args: deduplicate same-base (keep largest offset)
        if i < args.len() {
            rargs.push(args[i].clone());
            let mut prev_offset = args[i].get_offset();
            i += 1;
            while i < args.len() {
                let curr_offset = args[i].get_offset();
                if prev_offset.0 == curr_offset.0 {
                    // Same base — keep larger offset
                    if prev_offset.1 < curr_offset.1 {
                        prev_offset = curr_offset;
                        rargs.pop();
                        rargs.push(args[i].clone());
                    }
                } else {
                    prev_offset = curr_offset;
                    rargs.push(args[i].clone());
                }
                i += 1;
            }
        }

        rargs
    }

    /// Check if l1 ≥ l2 (l1 is greater than or equal to l2).
    ///
    /// This is a conservative approximation - returns true only if definitely ≥.
    /// Both sides are normalized before comparison, matching Lean 4 behavior.
    ///
    /// # Contract
    ///
    /// ENSURES: `is_geq(l, l) == true` (reflexive)
    /// ENSURES: `l2.is_zero() ==> is_geq(l1, l2) == true` (zero is minimum)
    /// ENSURES: If result is true, then semantically l1 >= l2
    ///
    /// Uses stack_safe for stack overflow protection on deeply nested levels.
    ///
    /// Reference: lean4/src/kernel/level.cpp:527-529
    pub(crate) fn is_geq(l1: &Level, l2: &Level) -> bool {
        let n1 = l1.normalize();
        let n2 = l2.normalize();
        stack_safe(|| Self::is_geq_core(&n1, &n2))
    }

    /// Core implementation of is_geq on normalized inputs.
    /// Matches Lean 4's `is_geq_core` rule order with unconditional IMax handling.
    ///
    /// Under cfg(kani), delegates to an iterative worklist implementation to
    /// eliminate function recursion that causes CBMC exponential unwinding.
    ///
    /// Uses memoization to prevent O(2^d) worst case on deep Max/IMax nesting
    /// where the same (l1, l2) subproblems appear repeatedly (#1781).
    ///
    /// Reference: lean4/src/kernel/level.cpp:508-526
    fn is_geq_core(l1: &Level, l2: &Level) -> bool {
        #[cfg(kani)]
        {
            Self::is_geq_core_iter(l1, l2)
        }
        #[cfg(not(kani))]
        {
            let mut cache = hashbrown::HashMap::new();
            Self::is_geq_core_cached(l1, l2, &mut cache)
        }
    }

    /// Iterative is_geq_core for CBMC: conjunction worklist eliminates recursion.
    /// Max/IMax on right → push sub-goals. Max on left → conservative leaf check.
    #[cfg(kani)]
    fn is_geq_core_iter(l1: &Level, l2: &Level) -> bool {
        let mut worklist: Vec<(&Level, &Level)> = vec![(l1, l2)];
        while let Some((l1, l2)) = worklist.pop() {
            if l1 == l2 || l2.is_zero() {
                continue;
            }
            let (base1, offset1) = l1.get_offset();
            if offset1 > 0 && *base1 == *l2 {
                continue;
            }
            if let Level::Max(a, b) = l2 {
                worklist.push((l1, a));
                worklist.push((l1, b));
                continue;
            }
            if let Level::Max(a, b) = l1 {
                if Self::is_geq_leaf(a, l2) || Self::is_geq_leaf(b, l2) {
                    continue;
                }
                return false;
            }
            if let Level::IMax(a, b) = l2 {
                worklist.push((l1, a));
                worklist.push((l1, b));
                continue;
            }
            if let Level::IMax(_, b) = l1 {
                worklist.push((b, l2));
                continue;
            }
            let (base2, offset2) = l2.get_offset();
            if base1 == base2 || base2.is_zero() {
                if offset1 >= offset2 {
                    continue;
                }
                return false;
            }
            if offset1 == offset2 && offset1 > 0 {
                worklist.push((base1, base2));
                continue;
            }
            return false;
        }
        true
    }

    /// Non-recursive leaf check for is_geq disjunction (max(a,b) >= l).
    /// Conservative: returns false for complex nested Max/IMax structures.
    #[cfg(kani)]
    fn is_geq_leaf(l1: &Level, l2: &Level) -> bool {
        if l1 == l2 || l2.is_zero() {
            return true;
        }
        let (base1, offset1) = l1.get_offset();
        if offset1 > 0 && *base1 == *l2 {
            return true;
        }
        let (base2, offset2) = l2.get_offset();
        (base1 == base2 || base2.is_zero()) && offset1 >= offset2
    }

    /// Memoized recursive is_geq_core for production use with stack_safe protection.
    ///
    /// The cache maps `(Level, Level) -> bool` to avoid re-evaluating the same
    /// subproblem. This converts O(2^d) worst case into O(d^2) for deep Max/IMax
    /// nesting where both sides share substructure (#1781).
    ///
    /// Level clones are cheap (Arc refcount bump) so cache key construction is O(1).
    #[cfg(not(kani))]
    fn is_geq_core_cached(
        l1: &Level,
        l2: &Level,
        cache: &mut hashbrown::HashMap<(Level, Level), bool>,
    ) -> bool {
        // Fast path: no cache lookup needed for trivially decidable cases
        if l1 == l2 || l2.is_zero() {
            return true;
        }
        // succ^n(x) >= x for any n > 0 (#1319 completeness improvement)
        {
            let (base1, offset1) = l1.get_offset();
            if offset1 > 0 && *base1 == *l2 {
                return true;
            }
        }

        // Check memoization cache
        let key = (l1.clone(), l2.clone());
        if let Some(&result) = cache.get(&key) {
            return result;
        }

        let result = Self::is_geq_core_compute(l1, l2, cache);
        cache.insert(key, result);
        result
    }

    /// Inner computation for memoized is_geq_core. Separated from cache
    /// lookup/store to keep the logic readable.
    ///
    /// Uses sequential let bindings for short-circuit logic to avoid
    /// simultaneous mutable borrows of `cache` in `&&`/`||` closure arms.
    #[cfg(not(kani))]
    fn is_geq_core_compute(
        l1: &Level,
        l2: &Level,
        cache: &mut hashbrown::HashMap<(Level, Level), bool>,
    ) -> bool {
        if let Level::Max(a, b) = l2 {
            let lhs = stack_safe(|| Self::is_geq_core_cached(l1, a, cache));
            return lhs && stack_safe(|| Self::is_geq_core_cached(l1, b, cache));
        }
        if let Level::Max(a, b) = l1 {
            let lhs = stack_safe(|| Self::is_geq_core_cached(a, l2, cache));
            if lhs || stack_safe(|| Self::is_geq_core_cached(b, l2, cache)) {
                return true;
            }
        }
        // l >= imax(a, b) iff l >= a && l >= b (unconditional — #1307 fix)
        if let Level::IMax(a, b) = l2 {
            let lhs = stack_safe(|| Self::is_geq_core_cached(l1, a, cache));
            return lhs && stack_safe(|| Self::is_geq_core_cached(l1, b, cache));
        }
        // imax(a, b) >= l iff b >= l (unconditional — #1307 fix)
        if let Level::IMax(_, b) = l1 {
            return stack_safe(|| Self::is_geq_core_cached(b, l2, cache));
        }
        let (base1, offset1) = l1.get_offset();
        let (base2, offset2) = l2.get_offset();
        if base1 == base2 || base2.is_zero() {
            return offset1 >= offset2;
        }
        if offset1 == offset2 && offset1 > 0 {
            return stack_safe(|| Self::is_geq_core_cached(base1, base2, cache));
        }
        false
    }

    /// Check if l1 ≤ l2.
    ///
    /// # Contract
    ///
    /// ENSURES: `leq(l, l) == true` (reflexive)
    /// ENSURES: `leq(a, b) == is_geq(b, a)` (definition)
    pub fn leq(l1: &Level, l2: &Level) -> bool {
        Level::is_geq(l2, l1)
    }

    /// Check if two levels are definitionally equal.
    ///
    /// # Contract
    ///
    /// ENSURES: `is_def_eq(l, l) == true` (reflexive)
    /// ENSURES: `is_def_eq(a, b) == is_def_eq(b, a)` (symmetric)
    /// ENSURES: `is_def_eq(a, b) && is_def_eq(b, c) ==> is_def_eq(a, c)` (transitive)
    pub fn is_def_eq(l1: &Level, l2: &Level) -> bool {
        // Short-circuit: structurally equal levels are definitionally equal
        // without expensive normalization.
        if l1 == l2 {
            return true;
        }
        l1.normalize() == l2.normalize()
    }

    /// Substitute universe parameters.
    ///
    /// # Contract
    ///
    /// ENSURES: If `subst` maps each param to itself, `result == self` (identity subst)
    /// ENSURES: If `self.has_params() == false`, `result == self`
    ///
    /// Uses stack_safe for stack overflow protection on deeply nested levels.
    pub fn substitute(&self, subst: &[(Name, Level)]) -> Level {
        stack_safe(|| self.substitute_impl(subst))
    }

    /// Substitute universe parameters from parallel name/level slices.
    ///
    /// This avoids building an intermediate `(Name, Level)` vector when the
    /// caller already has separate parameter and replacement slices.
    ///
    /// # Contract
    ///
    /// REQUIRES: `params.len() == levels.len()`
    /// ENSURES: If `self.has_params() == false`, `result == self`
    /// ENSURES: `params[i]` is replaced with `levels[i]` for all `i`
    pub(crate) fn substitute_slice(&self, params: &[Name], levels: &[Level]) -> Level {
        debug_assert_eq!(params.len(), levels.len());
        stack_safe(|| self.substitute_slice_impl(params, levels))
    }

    /// Implementation of substitute (called via stack_safe)
    ///
    /// # Contract
    ///
    /// ENSURES: `substitute_impl(subst) == substitute(subst)`
    fn substitute_impl(&self, subst: &[(Name, Level)]) -> Level {
        self.substitute_impl_opt(subst)
            .unwrap_or_else(|| self.clone())
    }

    /// Sharing-preserving substitution helper.
    ///
    /// Returns `None` when the subtree is structurally unchanged so callers can
    /// reuse the original node instead of rebuilding through smart constructors.
    fn substitute_impl_opt(&self, subst: &[(Name, Level)]) -> Option<Level> {
        match self {
            Level::Zero => None,
            Level::Succ(l) => stack_safe(|| l.substitute_impl_opt(subst)).map(Level::succ),
            Level::Max(l1, l2) => {
                let new_l1 = stack_safe(|| l1.substitute_impl_opt(subst));
                let new_l2 = stack_safe(|| l2.substitute_impl_opt(subst));
                match (new_l1, new_l2) {
                    (None, None) => None,
                    (Some(level1), None) => Some(Level::max(level1, Level::clone(&**l2))),
                    (None, Some(level2)) => Some(Level::max(Level::clone(&**l1), level2)),
                    (Some(level1), Some(level2)) => Some(Level::max(level1, level2)),
                }
            }
            Level::IMax(l1, l2) => {
                let new_l1 = stack_safe(|| l1.substitute_impl_opt(subst));
                let new_l2 = stack_safe(|| l2.substitute_impl_opt(subst));
                match (new_l1, new_l2) {
                    (None, None) => None,
                    (Some(level1), None) => Some(Level::imax(level1, Level::clone(&**l2))),
                    (None, Some(level2)) => Some(Level::imax(Level::clone(&**l1), level2)),
                    (Some(level1), Some(level2)) => Some(Level::imax(level1, level2)),
                }
            }
            Level::Param(name) => {
                for (n, level) in subst {
                    if n == name {
                        return if level == self {
                            None
                        } else {
                            Some(level.clone())
                        };
                    }
                }
                None
            }
        }
    }

    /// Implementation of `substitute_slice` (called via `stack_safe`).
    fn substitute_slice_impl(&self, params: &[Name], levels: &[Level]) -> Level {
        self.substitute_slice_impl_opt(params, levels)
            .unwrap_or_else(|| self.clone())
    }

    /// Sharing-preserving helper for `substitute_slice`.
    fn substitute_slice_impl_opt(&self, params: &[Name], levels: &[Level]) -> Option<Level> {
        match self {
            Level::Zero => None,
            Level::Succ(l) => {
                stack_safe(|| l.substitute_slice_impl_opt(params, levels)).map(Level::succ)
            }
            Level::Max(l1, l2) => {
                let new_l1 = stack_safe(|| l1.substitute_slice_impl_opt(params, levels));
                let new_l2 = stack_safe(|| l2.substitute_slice_impl_opt(params, levels));
                match (new_l1, new_l2) {
                    (None, None) => None,
                    (Some(level1), None) => Some(Level::max(level1, Level::clone(&**l2))),
                    (None, Some(level2)) => Some(Level::max(Level::clone(&**l1), level2)),
                    (Some(level1), Some(level2)) => Some(Level::max(level1, level2)),
                }
            }
            Level::IMax(l1, l2) => {
                let new_l1 = stack_safe(|| l1.substitute_slice_impl_opt(params, levels));
                let new_l2 = stack_safe(|| l2.substitute_slice_impl_opt(params, levels));
                match (new_l1, new_l2) {
                    (None, None) => None,
                    (Some(level1), None) => Some(Level::imax(level1, Level::clone(&**l2))),
                    (None, Some(level2)) => Some(Level::imax(Level::clone(&**l1), level2)),
                    (Some(level1), Some(level2)) => Some(Level::imax(level1, level2)),
                }
            }
            Level::Param(name) => {
                for (param, level) in params.iter().zip(levels.iter()) {
                    if param == name {
                        return if level == self {
                            None
                        } else {
                            Some(level.clone())
                        };
                    }
                }
                None
            }
        }
    }

    /// Substitute universe parameters using a HashMap for O(1) lookup.
    ///
    /// This is the performance-optimized version of `substitute` for hot paths.
    /// Use this when the same substitution is applied to many levels.
    ///
    /// # Contract
    ///
    /// ENSURES: If `subst` maps each param to itself, `result == self` (identity subst)
    /// ENSURES: If `self.has_params() == false`, `result == self`
    ///
    /// Uses stack_safe for stack overflow protection on deeply nested levels.
    pub(crate) fn substitute_map(&self, subst: &std::collections::HashMap<Name, Level>) -> Level {
        stack_safe(|| self.substitute_map_impl(subst))
    }

    /// Implementation of substitute_map (called via stack_safe)
    ///
    /// # Contract
    ///
    /// ENSURES: `substitute_map_impl(subst) == substitute_map(subst)`
    fn substitute_map_impl(&self, subst: &std::collections::HashMap<Name, Level>) -> Level {
        self.substitute_map_impl_opt(subst)
            .unwrap_or_else(|| self.clone())
    }

    /// Sharing-preserving helper for `substitute_map`.
    fn substitute_map_impl_opt(
        &self,
        subst: &std::collections::HashMap<Name, Level>,
    ) -> Option<Level> {
        match self {
            Level::Zero => None,
            Level::Succ(l) => stack_safe(|| l.substitute_map_impl_opt(subst)).map(Level::succ),
            Level::Max(l1, l2) => {
                let new_l1 = stack_safe(|| l1.substitute_map_impl_opt(subst));
                let new_l2 = stack_safe(|| l2.substitute_map_impl_opt(subst));
                match (new_l1, new_l2) {
                    (None, None) => None,
                    (Some(level1), None) => Some(Level::max(level1, Level::clone(&**l2))),
                    (None, Some(level2)) => Some(Level::max(Level::clone(&**l1), level2)),
                    (Some(level1), Some(level2)) => Some(Level::max(level1, level2)),
                }
            }
            Level::IMax(l1, l2) => {
                let new_l1 = stack_safe(|| l1.substitute_map_impl_opt(subst));
                let new_l2 = stack_safe(|| l2.substitute_map_impl_opt(subst));
                match (new_l1, new_l2) {
                    (None, None) => None,
                    (Some(level1), None) => Some(Level::imax(level1, Level::clone(&**l2))),
                    (None, Some(level2)) => Some(Level::imax(Level::clone(&**l1), level2)),
                    (Some(level1), Some(level2)) => Some(Level::imax(level1, level2)),
                }
            }
            Level::Param(name) => subst.get(name).and_then(|level| {
                if level == self {
                    None
                } else {
                    Some(level.clone())
                }
            }),
        }
    }

    /// Check if this level contains any parameters.
    ///
    /// # Contract
    ///
    /// ENSURES: `Zero.has_params() == false`
    /// ENSURES: `Param(_).has_params() == true`
    ///
    /// Uses stack_safe for stack overflow protection on deeply nested levels.
    #[cfg(not(kani))]
    pub fn has_params(&self) -> bool {
        stack_safe(|| self.has_params_impl())
    }

    /// Implementation of has_params (called via stack_safe)
    ///
    /// # Contract
    ///
    /// ENSURES: `has_params_impl() == has_params()`
    #[cfg(not(kani))]
    fn has_params_impl(&self) -> bool {
        match self {
            Level::Zero => false,
            Level::Succ(l) => stack_safe(|| l.has_params_impl()),
            Level::Max(l1, l2) | Level::IMax(l1, l2) => {
                stack_safe(|| l1.has_params_impl()) || stack_safe(|| l2.has_params_impl())
            }
            Level::Param(_) => true,
        }
    }

    /// Kani override: conservative has_params that avoids recursive Arc<Level>
    /// unwinding. Returns exact result for Zero and Param; returns true
    /// (conservative over-approximation) for Succ/Max/IMax since we can't
    /// recurse into children without causing CBMC unwinding.
    /// Sound: has_params=true when actually false only causes unnecessary
    /// level param substitution attempts, which correctly return the original.
    #[cfg(kani)]
    pub fn has_params(&self) -> bool {
        match self {
            Level::Zero => false,
            Level::Param(_) => true,
            // Conservative: non-trivial levels might contain Param children.
            Level::Succ(_) | Level::Max(_, _) | Level::IMax(_, _) => true,
        }
    }

    /// Collect all parameter names in this level.
    ///
    /// # Contract
    ///
    /// ENSURES: No duplicate names are added to `params`
    /// ENSURES: All collected names satisfy `Param(n)` somewhere in `self`
    /// ENSURES: O(n) where n = nodes in self (uses HashSet for O(1) deduplication)
    ///
    /// Uses stack_safe for stack overflow protection on deeply nested levels.
    pub fn collect_params(&self, params: &mut Vec<Name>) {
        use std::collections::HashSet;
        // Use HashSet for O(1) lookup during collection
        let mut seen: HashSet<Name> = params.iter().cloned().collect();
        stack_safe(|| self.collect_params_impl(params, &mut seen));
    }

    /// Implementation of collect_params (called via stack_safe)
    ///
    /// # Contract
    ///
    /// ENSURES: `params` contains all Param names from `self`, deduplicated with `seen`
    fn collect_params_impl(
        &self,
        params: &mut Vec<Name>,
        seen: &mut std::collections::HashSet<Name>,
    ) {
        match self {
            Level::Zero => {}
            Level::Succ(l) => stack_safe(|| l.collect_params_impl(params, seen)),
            Level::Max(l1, l2) | Level::IMax(l1, l2) => {
                stack_safe(|| l1.collect_params_impl(params, seen));
                stack_safe(|| l2.collect_params_impl(params, seen));
            }
            Level::Param(name) => {
                if seen.insert(name.clone()) {
                    params.push(name.clone());
                }
            }
        }
    }
}

impl std::fmt::Display for Level {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        stack_safe(|| self.fmt_impl(f))
    }
}

impl Level {
    /// Stack-safe Display implementation. Each recursive call goes through
    /// `stack_safe` via `Display::fmt` to prevent overflow on deep Max/IMax trees.
    fn fmt_impl(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Level::Zero => write!(f, "0"),
            Level::Succ(l) => {
                // Count successive Succs for prettier output (iterative)
                let mut count = 1u64;
                let mut inner: &Level = l;
                while let Level::Succ(next) = inner {
                    count += 1;
                    inner = next;
                }
                if inner.is_zero() {
                    write!(f, "{count}")
                } else {
                    // inner.fmt via Display will call stack_safe
                    write!(f, "{inner} + {count}")
                }
            }
            // Explicit &Level references for cfg(kani) compatibility:
            // LevelArc = ManuallyDrop<Box<Level>> under Kani, which doesn't
            // impl Display. Deref coercion to &Level resolves this.
            Level::Max(l1, l2) => {
                let l1: &Level = l1;
                let l2: &Level = l2;
                write!(f, "max({l1}, {l2})")
            }
            Level::IMax(l1, l2) => {
                let l1: &Level = l1;
                let l2: &Level = l2;
                write!(f, "imax({l1}, {l2})")
            }
            Level::Param(name) => write!(f, "{name}"),
        }
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod soundness_harness;

#[cfg(kani)]
mod kani_proofs;
