// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Small types used by the expression system.
//!
//! Contains: BinderInfo, BigNat, Literal, MDataValue, MDataMap, FVarId,
//! LevelVec, AppArgs, AppArgsIter.

use super::{Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use std::sync::Arc;

/// Type alias for universe level lists in ExprKind::Const.
///
/// Most constants have 0-2 universe levels (97.1% in Init.Prelude),
/// so we use SmallVec to avoid heap allocation for the common case.
/// This reduces allocation overhead during .olean loading.
pub type LevelVec = SmallVec<[Level; 2]>;

/// Binder information (how a variable is bound)
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BinderInfo {
    /// Regular explicit binding
    #[default]
    Default,
    /// Implicit binding (inferred by unification) `{x : T}`
    Implicit,
    /// Strict implicit (must be inferrable) `{{x : T}}`
    StrictImplicit,
    /// Instance implicit (resolved by type class) `[x : T]`
    InstImplicit,
}

/// Quantitative Type Theory multiplicities (Atkey 2018, Brady 2021).
///
/// Forms a semiring (Mult, +, Zero, *, One) where:
///   Zero + Zero = Zero,  Zero + One = One,  One + One = Many,  Many + _ = Many
///   Zero * _ = Zero,     One * x = x,       Many * Many = Many
///
/// The `Zero` multiplicity is essential for dependent types with linearity:
/// it allows variables to appear in type annotations without being "used"
/// computationally, resolving the dependency-linearity conflict.
///
/// References:
///   - Atkey 2018, "Syntax and Semantics of Quantitative Type Theory"
///   - Brady 2021, "Idris 2: Quantitative Type Theory in Practice"
///   - Orchard et al. 2019, "Quantitative Program Reasoning with Graded Modal Types"
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Multiplicity {
    /// Erased: appears only in types/proofs, not computed at runtime.
    /// Essential for dependent types referencing linear variables.
    Zero,
    /// Linear: used exactly once at runtime.
    One,
    /// Unrestricted: used any number of times (standard Lean 4 behavior).
    #[default]
    Many,
}

impl Multiplicity {
    /// Semiring addition: combine two usage counts.
    #[inline]
    #[allow(clippy::should_implement_trait)]
    pub fn add(self, other: Self) -> Self {
        match (self, other) {
            (Multiplicity::Zero, m) | (m, Multiplicity::Zero) => m,
            _ => Multiplicity::Many,
        }
    }

    /// Semiring multiplication: scale a usage by a context multiplicity.
    //
    // NOTE: the Trust verification ledger 2026-06-10 flagged this match as
    // "assertion: unreachable code reached" (expr::types::Multiplicity::mul,
    // types.rs:78:4-84:5). FALSE POSITIVE: the match is exhaustive over
    // Multiplicity x Multiplicity (all 9 combinations, rustc-checked, no
    // wildcard arm), so the MIR SwitchInt otherwise-edge `unreachable` only
    // fires for an invalid enum discriminant — unconstructible in safe Rust
    // (this crate is #![forbid(unsafe_code)]). The vcgen models the
    // discriminant as an unconstrained integer instead of applying the enum
    // validity invariant. Deliberately NOT adding a wildcard arm: that would
    // trade a vcgen artifact for the loss of compile-time exhaustiveness
    // checking on future variants. See test_multiplicity_mul_semiring_table
    // in expr/tests.rs.
    #[inline]
    #[allow(clippy::should_implement_trait)]
    pub fn mul(self, other: Self) -> Self {
        match (self, other) {
            (Multiplicity::Zero, _) | (_, Multiplicity::Zero) => Multiplicity::Zero,
            (Multiplicity::One, m) | (m, Multiplicity::One) => m,
            (Multiplicity::Many, Multiplicity::Many) => Multiplicity::Many,
        }
    }

    /// Check if this multiplicity allows zero uses (erased or unrestricted).
    #[inline]
    pub fn allows_zero(self) -> bool {
        matches!(self, Multiplicity::Zero | Multiplicity::Many)
    }

    /// Check if this multiplicity allows multiple uses.
    #[inline]
    pub fn allows_many(self) -> bool {
        matches!(self, Multiplicity::Many)
    }
}

/// Binder annotation combining implicit/explicit info with resource multiplicity.
///
/// Wraps `BinderInfo` (how a variable is bound syntactically) with `Multiplicity`
/// (how many times the variable may be used, per QTT). This is the type stored
/// in `ExprKind::Lam` and `ExprKind::Pi` variants.
///
/// All existing code defaults to `Multiplicity::Many` (unrestricted), preserving
/// standard Lean 4 semantics.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BinderData {
    /// How the variable is bound (explicit, implicit, instance, etc.)
    pub info: BinderInfo,
    /// Resource multiplicity (Zero, One, Many) per QTT.
    pub mult: Multiplicity,
}

impl BinderData {
    /// Create a new BinderData with the given info and multiplicity.
    #[inline]
    pub fn new(info: BinderInfo, mult: Multiplicity) -> Self {
        BinderData { info, mult }
    }

    /// Create a BinderData with unrestricted multiplicity.
    #[inline]
    pub fn unrestricted(info: BinderInfo) -> Self {
        BinderData {
            info,
            mult: Multiplicity::Many,
        }
    }
}

impl From<BinderInfo> for BinderData {
    #[inline]
    fn from(info: BinderInfo) -> Self {
        BinderData {
            info,
            mult: Multiplicity::Many,
        }
    }
}

/// A big natural number that can hold arbitrary-precision values.
///
/// Lean 4 uses GMP for big integers. This type handles both small values
/// (fitting in u64) and arbitrarily large values (multiple 64-bit limbs).
///
/// # Implementation Note
///
/// This matches Lean 4's dual representation:
/// - **Small nat** (unboxed scalar): Values up to ~2^63-1
/// - **Big nat** (heap MPZ): Multi-limb GMP integers for larger values
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BigNat {
    /// Small value that fits in u64.
    Small(u64),
    /// Large value with multiple limbs (little-endian, lowest limb first).
    Big(Vec<u64>),
}

impl PartialOrd for BigNat {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BigNat {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let a_limbs = self.limbs();
        let b_limbs = other.limbs();
        // Compare by number of significant limbs first (more limbs = larger)
        match a_limbs.len().cmp(&b_limbs.len()) {
            std::cmp::Ordering::Equal => {
                // Same number of limbs: compare from most significant to least
                for (a, b) in a_limbs.iter().rev().zip(b_limbs.iter().rev()) {
                    match a.cmp(b) {
                        std::cmp::Ordering::Equal => continue,
                        ord => return ord,
                    }
                }
                std::cmp::Ordering::Equal
            }
            ord => ord,
        }
    }
}

impl BigNat {
    /// Create a BigNat from a u64 value.
    #[inline]
    pub fn from_u64(val: u64) -> Self {
        BigNat::Small(val)
    }

    /// Create a BigNat from a vector of limbs (little-endian).
    pub fn from_limbs(limbs: Vec<u64>) -> Self {
        match limbs.len() {
            0 => BigNat::Small(0),
            1 => BigNat::Small(limbs[0]),
            _ => {
                let mut limbs = limbs;
                while limbs.len() > 1 && limbs.last() == Some(&0) {
                    limbs.pop();
                }
                if limbs.len() == 1 {
                    BigNat::Small(limbs[0])
                } else {
                    BigNat::Big(limbs)
                }
            }
        }
    }

    /// Parse a natural number from its digit string in the given `radix`
    /// (2..=16). Underscores are ignored (Lean digit-group separators, e.g.
    /// `FF_FF`). Digits are folded exactly via multi-limb `self * radix + d`,
    /// so the resulting value is exact and arbitrary-precision.
    ///
    /// Returns `None` when the string has no digits, contains a character that
    /// is not a valid digit for `radix`, or the value would exceed the
    /// 256-limb multiplication cap (a ~16384-bit ceiling shared with
    /// `checked_mul_big` — pathological literals are declined, never truncated).
    pub fn from_radix_str(digits: &str, radix: u32) -> Option<BigNat> {
        let radix_big = BigNat::Small(u64::from(radix));
        let mut acc = BigNat::Small(0);
        let mut saw_digit = false;
        for ch in digits.chars() {
            if ch == '_' {
                continue;
            }
            let d = ch.to_digit(radix)?;
            saw_digit = true;
            acc = acc.checked_mul_big(&radix_big)?;
            acc = acc.checked_add_big(&BigNat::Small(u64::from(d)));
        }
        if saw_digit {
            Some(acc)
        } else {
            None
        }
    }

    /// Try to convert to u64, returning None if too large.
    #[inline]
    pub fn to_u64(&self) -> Option<u64> {
        match self {
            BigNat::Small(v) => Some(*v),
            BigNat::Big(_) => None,
        }
    }

    /// Get the limbs (little-endian).
    pub fn limbs(&self) -> &[u64] {
        match self {
            BigNat::Small(v) => std::slice::from_ref(v),
            BigNat::Big(limbs) => limbs,
        }
    }

    /// Check if this BigNat is zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        match self {
            BigNat::Small(0) => true,
            BigNat::Small(_) => false,
            BigNat::Big(limbs) => limbs.iter().all(|&l| l == 0),
        }
    }

    /// Multi-limb addition: self + other.
    ///
    /// Returns a new BigNat. Never overflows (grows limbs as needed).
    pub fn checked_add_big(&self, other: &BigNat) -> BigNat {
        let a = self.limbs();
        let b = other.limbs();
        let max_len = a.len().max(b.len());
        let mut result = Vec::with_capacity(max_len + 1);
        let mut carry = 0u64;
        for i in 0..max_len {
            let av = if i < a.len() { a[i] } else { 0 };
            let bv = if i < b.len() { b[i] } else { 0 };
            let (sum1, c1) = av.overflowing_add(bv);
            let (sum2, c2) = sum1.overflowing_add(carry);
            result.push(sum2);
            carry = (c1 as u64) + (c2 as u64);
        }
        if carry > 0 {
            result.push(carry);
        }
        BigNat::from_limbs(result)
    }

    /// Multi-limb saturating subtraction: self - other, clamped to 0.
    ///
    /// Lean Nat subtraction is floored at zero.
    pub fn saturating_sub_big(&self, other: &BigNat) -> BigNat {
        if self <= other {
            return BigNat::Small(0);
        }
        let a = self.limbs();
        let b = other.limbs();
        let mut result = Vec::with_capacity(a.len());
        let mut borrow = 0u64;
        for i in 0..a.len() {
            let bv = if i < b.len() { b[i] } else { 0 };
            let (diff1, b1) = a[i].overflowing_sub(bv);
            let (diff2, b2) = diff1.overflowing_sub(borrow);
            result.push(diff2);
            borrow = (b1 as u64) + (b2 as u64);
        }
        BigNat::from_limbs(result)
    }

    /// Multi-limb multiplication: self * other.
    ///
    /// Returns None if the result would have more than 256 limbs (16384 bits)
    /// to avoid unbounded allocation in pathological cases. Raised from 16 →
    /// 256 so `norm_num` closed-literal certificates over LARGE naturals reduce
    /// (e.g. `Mathlib.Meta.NormNum.IsNatPowT` cross-products in
    /// `Real.eulerMascheroniSeq'_six_lt_two_thirds` reach ~28-53 limbs). SOUND:
    /// the product is EXACT schoolbook multi-limb arithmetic — a larger cap only
    /// lets MORE closed products reduce (a def-eq COMPLETENESS gain), never
    /// changes a computed value, so it cannot accept a non-def-eq. Allocation
    /// stays bounded (a 256-limb result is 2 KiB; the O(n²) mul is ~64K
    /// limb-multiplies).
    pub fn checked_mul_big(&self, other: &BigNat) -> Option<BigNat> {
        self.mul_big_capped(other, 256)
    }

    /// Multi-limb multiplication with an explicit limb cap on the result.
    ///
    /// `self * other`, declining (returning `None`) if the product would exceed
    /// `max_limbs` 64-bit limbs. Generalizes `checked_mul_big` (which fixes the
    /// cap at 16) so callers that must reduce LARGER closed literals — notably
    /// the arbitrary-precision `Int.*` native reducers handling `Rat.le`
    /// cross-products at the binary64 floored-ulp scale `2^1074` (≈17 limbs per
    /// operand, ≈34-limb products) — can raise the bound while still keeping
    /// allocation strictly bounded.
    pub fn mul_big_capped(&self, other: &BigNat, max_limbs: usize) -> Option<BigNat> {
        if self.is_zero() || other.is_zero() {
            return Some(BigNat::Small(0));
        }
        let a = self.limbs();
        let b = other.limbs();
        let result_len = a.len() + b.len();
        // Cap result size to prevent pathological allocation.
        if result_len > max_limbs {
            return None;
        }
        let mut result = vec![0u64; result_len];
        for i in 0..a.len() {
            let mut carry = 0u128;
            for j in 0..b.len() {
                let prod = (a[i] as u128) * (b[j] as u128) + (result[i + j] as u128) + carry;
                result[i + j] = prod as u64;
                carry = prod >> 64;
            }
            if carry > 0 {
                result[i + b.len()] += carry as u64;
            }
        }
        Some(BigNat::from_limbs(result))
    }

    /// Compute the predecessor (self - 1), returning `None` for zero.
    ///
    /// Handles both small and big representations with borrow propagation.
    /// Normalizes multi-limb results back to `Small` when they fit.
    pub fn pred(&self) -> Option<BigNat> {
        match self {
            BigNat::Small(0) => None,
            BigNat::Small(v) => Some(BigNat::Small(v - 1)),
            BigNat::Big(limbs) => {
                let mut new_limbs = limbs.clone();
                let mut borrow = 1u64;
                for limb in &mut new_limbs {
                    let (new_val, did_borrow) = limb.overflowing_sub(borrow);
                    *limb = new_val;
                    borrow = if did_borrow { 1 } else { 0 };
                    if borrow == 0 {
                        break;
                    }
                }
                while new_limbs.len() > 1 && new_limbs.last() == Some(&0) {
                    new_limbs.pop();
                }
                Some(if new_limbs.len() == 1 {
                    BigNat::Small(new_limbs[0])
                } else {
                    BigNat::Big(new_limbs)
                })
            }
        }
    }
}

impl Default for BigNat {
    fn default() -> Self {
        BigNat::Small(0)
    }
}

impl From<u64> for BigNat {
    fn from(val: u64) -> Self {
        BigNat::Small(val)
    }
}

impl std::fmt::Display for BigNat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BigNat::Small(v) => write!(f, "{}", v),
            BigNat::Big(limbs) => {
                write!(f, "0x")?;
                for limb in limbs.iter().rev() {
                    write!(f, "{:016x}", limb)?;
                }
                Ok(())
            }
        }
    }
}

/// Literal values
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Literal {
    /// Natural number literal (arbitrary precision)
    Nat(BigNat),
    /// String literal
    String(Arc<str>),
}

impl Literal {
    /// Create a natural number literal.
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `Literal::Nat(BigNat::Small(n))`
    /// ENSURES: Deterministic - same input yields same output
    pub fn nat(n: u64) -> Self {
        Literal::Nat(BigNat::Small(n))
    }
}

/// Metadata value for MData expressions
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum MDataValue {
    /// Boolean metadata
    Bool(bool),
    /// Natural number metadata
    Nat(u64),
    /// String metadata
    String(Arc<str>),
    /// Name metadata
    Name(Name),
}

/// Key-value metadata map for MData expressions
pub type MDataMap = Vec<(Name, MDataValue)>;

/// Unique identifier for free variables
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct FVarId(pub(crate) u64);

impl FVarId {
    /// Start of the sentinel FVarId range.
    ///
    /// FVarIds at or above this value are reserved for proof reconstruction
    /// witnesses (negated-goal assumptions, compound clause witnesses).
    /// Kernel-allocated FVarIds must stay below this threshold.
    ///
    /// The range covers 65536 values: `[SENTINEL_RANGE_START, u64::MAX]`.
    pub const SENTINEL_RANGE_START: u64 = u64::MAX - 65536;

    /// Create a new free variable identifier.
    #[inline]
    pub fn new(id: u64) -> Self {
        FVarId(id)
    }

    /// Return the underlying `u64` value.
    #[inline]
    pub fn as_u64(self) -> u64 {
        self.0
    }

    /// Check whether this FVarId is in the sentinel range reserved for
    /// proof reconstruction witnesses.
    #[inline]
    pub fn is_sentinel(self) -> bool {
        self.0 >= Self::SENTINEL_RANGE_START
    }
}

/// Inline-friendly buffer for application arguments.
pub type AppArgs<'a> = SmallVec<[&'a Expr; 8]>;

/// Iterator over application arguments (zero allocation).
///
/// Yields arguments in application order (innermost first).
/// For `f a b c`, yields `c, b, a`.
#[derive(Debug, Clone)]
pub struct AppArgsIter<'a> {
    pub(super) curr: &'a Expr,
}

impl<'a> Iterator for AppArgsIter<'a> {
    type Item = &'a Expr;

    fn next(&mut self) -> Option<Self::Item> {
        match &self.curr.kind {
            ExprKind::App(f, a) => {
                self.curr = f.as_ref();
                Some(a.as_ref())
            }
            _ => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // Could count but that's O(n), so we don't provide upper bound
        (0, None)
    }
}
