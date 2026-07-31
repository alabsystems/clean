// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native, kernel-checked **exact** float→rational decomposition.
//!
//! This is "real floats in Clean", Stage A: it turns the per-concrete-float
//! rounding AXIOM (`NNVerify.FloatRational.float_to_rational_exact`) into a
//! kernel-CHECKED computation. Clean already evaluates binary64 bit-exactly in
//! kernel (`native_reducers_float.rs`); here we decompose the IEEE-754 bit
//! pattern into the EXACT rational `(-1)^s · m · 2^e` using only the bit access
//! that `Float.val` already provides plus pure integer mask/shift arithmetic.
//! No host float is used in the decomposition — `f64` never appears in this
//! module's value path (only the raw `u64` bit pattern is read).
//!
//! Two reducers are provided:
//!
//! - `Float.toRatExact : Float → Rat` — the EXACT rational value of a finite
//!   float, emitted as `Rat.mk <Int> <Nat>` where the denominator is a power of
//!   two. This is exact: every finite binary64 is a dyadic rational.
//! - `Float.ulpExact : Float → Rat` — the unit in the last place, also a power
//!   of two, **floored at the denormal ulp** `2^(emin - p + 1)`. That floor is
//!   the fact whose ABSENCE let ny's softmax underflow through; it is enforced
//!   here by clamping the biased exponent to at least 1 before forming the ulp
//!   quantum exponent.
//!
//! ## The three IEEE-754 regimes (binary64: p = 53, emin = −1022, bias = 1023)
//!
//! For bit pattern with sign `s`, biased exponent `E` (11 bits), trailing
//! significand `T` (52 bits):
//!
//! | regime              | condition       | significand `m` | value exp `e`        |
//! |---------------------|-----------------|-----------------|----------------------|
//! | normal              | `1 ≤ E ≤ 2046`  | `2^52 + T`      | `E − bias − (p−1)`   |
//! | subnormal / denormal| `E = 0, T ≠ 0`  | `T`             | `emin − (p−1)`       |
//! | zero                | `E = 0, T = 0`  | `0`             | (value is exactly 0) |
//!
//! The ulp quantum exponent is `max(E, 1) − bias − (p−1)`: clamping `E` to at
//! least 1 is exactly the denormal-ulp FLOOR.
//!
//! The decomposition is parameterized by `(p, emin, bias, exp_bits)` via
//! [`IeeeFormat`], so the SAME code covers binary32 and binary64. Only binary64
//! (`Float = f64`) is wired into the kernel as a native reducer right now; the
//! binary32 path is exercised by unit tests on the pure helpers.
//!
//! Part of #3185.

use crate::env::Environment;
use crate::expr::{BigNat, Expr, ExprKind, Literal};
use crate::name::Name;

/// Well-known names for the float→rational native reducers.
pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    macro_rules! name {
        ($vis:vis $ident:ident = $value:literal) => {
            $vis static $ident: LazyLock<Name> = LazyLock::new(|| Name::from_string($value));
        };
    }

    name!(pub(crate) FLOAT_TO_RAT_EXACT = "Float.toRatExact");
    name!(pub(crate) FLOAT_ULP_EXACT = "Float.ulpExact");
    name!(pub(crate) FLOAT_MK = "Float.mk");
    name!(pub(crate) RAT_ROUND_TO_NEAREST_EVEN = "Rat.roundToNearestEven");
}

/// An IEEE-754 binary interchange format, parameterized so the SAME
/// decomposition covers binary32 and binary64.
#[derive(Clone, Copy, Debug)]
pub(crate) struct IeeeFormat {
    /// Total width in bits (32 or 64).
    pub width: u32,
    /// Number of trailing-significand (mantissa) bits (binary32: 23, binary64: 52).
    pub mantissa_bits: u32,
    /// Number of biased-exponent bits (binary32: 8, binary64: 11).
    pub exp_bits: u32,
    /// Exponent bias (binary32: 127, binary64: 1023).
    pub bias: i64,
}

impl IeeeFormat {
    /// IEEE-754 binary64 (`f64`): p = 53, emin = −1022, bias = 1023.
    pub(crate) const BINARY64: IeeeFormat = IeeeFormat {
        width: 64,
        mantissa_bits: 52,
        exp_bits: 11,
        bias: 1023,
    };

    /// IEEE-754 binary32 (`f32`): p = 24, emin = −126, bias = 127.
    #[cfg(test)]
    pub(crate) const BINARY32: IeeeFormat = IeeeFormat {
        width: 32,
        mantissa_bits: 23,
        exp_bits: 8,
        bias: 127,
    };

    /// Precision `p = mantissa_bits + 1` (counting the implicit leading bit).
    #[inline]
    fn precision(&self) -> i64 {
        self.mantissa_bits as i64 + 1
    }

    /// Minimum normal exponent `emin = 1 − bias`.
    #[inline]
    fn emin(&self) -> i64 {
        1 - self.bias
    }

    /// The maximal biased exponent (all-ones) — flags Inf/NaN.
    #[inline]
    fn max_biased_exp(&self) -> u64 {
        (1u64 << self.exp_bits) - 1
    }
}

/// A finite IEEE-754 value decomposed into the EXACT dyadic rational
/// `(-1)^sign · num_mag · 2^exp` (num_mag ≥ 0, exp ∈ ℤ).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DyadicValue {
    /// `true` iff the sign bit is set. Note `-0.0` keeps `sign = true` with
    /// `num_mag = 0`; the resulting rational is `0` either way.
    pub sign: bool,
    /// The (non-negative) significand magnitude `m` as a big natural.
    pub num_mag: BigNat,
    /// The base-2 exponent `e`, so the value is `±m · 2^e`.
    pub exp: i64,
}

/// Classification of a bit pattern's regime, used by the tests and to reject
/// non-finite inputs (Inf/NaN have no exact rational value).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FloatClass {
    Zero,
    Subnormal,
    Normal,
    /// Infinity or NaN — `toRatExact` / `ulpExact` decline (no exact rational).
    NonFinite,
}

/// Build `2^k` as a `BigNat` (k ≥ 0). `2^k` has bit `k` set: limb `k / 64`,
/// in-limb bit `k % 64`. `pub(crate)` so the half-ulp discharge can build the
/// power-of-two denominators it cross-multiplies.
pub(crate) fn pow2_bignat(k: u64) -> BigNat {
    let limb = (k / 64) as usize;
    let bit = k % 64;
    let mut limbs = vec![0u64; limb + 1];
    limbs[limb] = 1u64 << bit;
    BigNat::from_limbs(limbs)
}

/// Left-shift a `BigNat` by `k` bits (multiply by `2^k`), k ≥ 0. `pub(crate)`
/// so the half-ulp discharge can place magnitudes over a common denominator.
pub(crate) fn shl_bignat(n: &BigNat, k: u64) -> BigNat {
    if n.is_zero() || k == 0 {
        return n.clone();
    }
    let limb_shift = (k / 64) as usize;
    let bit_shift = (k % 64) as u32;
    let src = n.limbs();
    // Worst case: one extra limb for the carried-out high bits.
    let mut out = vec![0u64; src.len() + limb_shift + 1];
    for (i, &word) in src.iter().enumerate() {
        if bit_shift == 0 {
            out[i + limb_shift] |= word;
        } else {
            out[i + limb_shift] |= word << bit_shift;
            out[i + limb_shift + 1] |= word >> (64 - bit_shift);
        }
    }
    BigNat::from_limbs(out)
}

/// Logical right-shift a `BigNat` by `k` bits (floor-divide by `2^k`), k ≥ 0.
/// This is `⌊n / 2^k⌋` exactly — the quotient of `n` by the power-of-two grid.
fn shr_bignat(n: &BigNat, k: u64) -> BigNat {
    if n.is_zero() || k == 0 {
        return n.clone();
    }
    let limb_shift = (k / 64) as usize;
    let bit_shift = (k % 64) as u32;
    let src = n.limbs();
    if limb_shift >= src.len() {
        return BigNat::Small(0);
    }
    let out_len = src.len() - limb_shift;
    let mut out = vec![0u64; out_len];
    for i in 0..out_len {
        let lo = src[i + limb_shift] >> bit_shift;
        let hi = if bit_shift == 0 {
            0
        } else if i + limb_shift + 1 < src.len() {
            src[i + limb_shift + 1] << (64 - bit_shift)
        } else {
            0
        };
        out[i] = lo | hi;
    }
    BigNat::from_limbs(out)
}

/// Whether bit `k` of `n` is set (i.e. `n` has a `2^k` term in its binary
/// expansion). Used to read the round/guard bits of the rounding grid.
fn test_bit_bignat(n: &BigNat, k: u64) -> bool {
    let limb = (k / 64) as usize;
    let bit = k % 64;
    let limbs = n.limbs();
    limb < limbs.len() && (limbs[limb] >> bit) & 1 == 1
}

/// Whether the low `k` bits of `n` are ALL zero (i.e. `2^k | n`). Equivalently
/// `n mod 2^k == 0` — the "sticky bits are zero" test used to detect an exact
/// half-way (tie) versus a strictly-greater remainder.
fn low_bits_zero_bignat(n: &BigNat, k: u64) -> bool {
    if k == 0 {
        return true;
    }
    let full_limbs = (k / 64) as usize;
    let rem_bits = (k % 64) as u32;
    let limbs = n.limbs();
    for (i, &w) in limbs.iter().enumerate() {
        if i < full_limbs {
            if w != 0 {
                return false;
            }
        } else if i == full_limbs {
            if rem_bits != 0 && (w & ((1u64 << rem_bits) - 1)) != 0 {
                return false;
            }
        } else {
            break;
        }
    }
    true
}

/// Round a non-negative `BigNat` magnitude `n` (in units of `1/2^scale`) to the
/// nearest multiple of the grid spacing `2^g` (in the same `1/2^scale` units),
/// **ties to even**. Returns the rounded numerator (a multiple of `2^g`), still
/// in `1/2^scale` units, as a `BigNat`.
///
/// This is `Nat.roundHalfEvenMod n (2^g)` computed by bit inspection:
///   `q = n >> g`, `r = n mod 2^g`. Compare `2r` to `2^g`:
///   - `2r < 2^g`  (round bit clear)              → round down to `q·2^g`.
///   - `2r > 2^g`  (round bit set, sticky nonzero) → round up   to `(q+1)·2^g`.
///   - `2r = 2^g`  (round bit set, sticky zero — a TIE): keep `q·2^g` if `q`
///     is even, else round up to `(q+1)·2^g`.
/// For `g = 0` the grid is the integers' unit and `n` is already on-grid.
fn round_half_even_pow2(n: &BigNat, g: u64) -> BigNat {
    if g == 0 || n.is_zero() {
        return n.clone();
    }
    let q = shr_bignat(n, g); // ⌊n / 2^g⌋
    let down = shl_bignat(&q, g); // q · 2^g
                                  // The round bit is bit (g-1) of n; sticky = any bit below (g-1) set.
    let round_bit = test_bit_bignat(n, g - 1);
    if !round_bit {
        // 2r < 2^g (remainder below half) → round down.
        return down;
    }
    let sticky_nonzero = !low_bits_zero_bignat(n, g - 1);
    let round_up = || shl_bignat(&q.checked_add_big(&BigNat::Small(1)), g);
    if sticky_nonzero {
        // 2r > 2^g (remainder above half) → round up.
        round_up()
    } else {
        // Exact tie (2r = 2^g): ties-to-even keeps q·2^g when q is even.
        let q_even = !test_bit_bignat(&q, 0);
        if q_even {
            down
        } else {
            round_up()
        }
    }
}

/// Classify a width-`width` bit pattern into its IEEE-754 regime.
pub(crate) fn classify(bits: u64, fmt: &IeeeFormat) -> FloatClass {
    let biased_exp = (bits >> fmt.mantissa_bits) & fmt.max_biased_exp();
    let mantissa = bits & ((1u64 << fmt.mantissa_bits) - 1);
    if biased_exp == fmt.max_biased_exp() {
        FloatClass::NonFinite
    } else if biased_exp == 0 {
        if mantissa == 0 {
            FloatClass::Zero
        } else {
            FloatClass::Subnormal
        }
    } else {
        FloatClass::Normal
    }
}

/// Decompose a finite bit pattern into its EXACT dyadic value `±m · 2^e`.
///
/// Returns `None` for Inf/NaN (no exact rational). Handles the THREE finite
/// regimes:
/// - **normal**  (`1 ≤ E ≤ max−1`): implicit leading 1, `m = 2^mb + T`,
///   `e = E − bias − (p−1)`.
/// - **subnormal** (`E = 0, T ≠ 0`): NO implicit 1, `m = T`,
///   `e = emin − (p−1)`.
/// - **zero**    (`E = 0, T = 0`): `m = 0`, value exactly `0`.
pub(crate) fn decompose_exact(bits: u64, fmt: &IeeeFormat) -> Option<DyadicValue> {
    let sign = (bits >> (fmt.width - 1)) & 1 == 1;
    let biased_exp = (bits >> fmt.mantissa_bits) & fmt.max_biased_exp();
    let mantissa = bits & ((1u64 << fmt.mantissa_bits) - 1);

    match classify(bits, fmt) {
        FloatClass::NonFinite => None,
        FloatClass::Zero => Some(DyadicValue {
            sign,
            num_mag: BigNat::Small(0),
            // Exponent is irrelevant for a zero magnitude; pin it at the
            // denormal quantum so the dyadic is well-defined.
            exp: fmt.emin() - (fmt.precision() - 1),
        }),
        FloatClass::Subnormal => Some(DyadicValue {
            sign,
            // No implicit leading 1: m = T.
            num_mag: BigNat::Small(mantissa),
            // e = emin − (p − 1).
            exp: fmt.emin() - (fmt.precision() - 1),
        }),
        FloatClass::Normal => {
            // Implicit leading 1: m = 2^mb + T (a p-bit significand).
            let m = (1u64 << fmt.mantissa_bits) | mantissa;
            // e = E − bias − (p − 1).
            let exp = biased_exp as i64 - fmt.bias - (fmt.precision() - 1);
            Some(DyadicValue {
                sign,
                num_mag: BigNat::Small(m),
                exp,
            })
        }
    }
}

/// The ulp quantum exponent for a finite bit pattern, **floored at the
/// denormal ulp** `emin − (p − 1)`.
///
/// `ulp = 2^q` with `q = max(E, 1) − bias − (p − 1)`. Clamping `E` to at least
/// 1 IS the denormal-ulp floor: for the entire subnormal range (and zero),
/// `q = emin − (p − 1)`, never smaller. Omitting this floor is exactly the bug
/// that let ny's softmax underflow through. Returns `None` for Inf/NaN.
pub(crate) fn ulp_quantum_exp(bits: u64, fmt: &IeeeFormat) -> Option<i64> {
    if classify(bits, fmt) == FloatClass::NonFinite {
        return None;
    }
    let biased_exp = (bits >> fmt.mantissa_bits) & fmt.max_biased_exp();
    // FLOOR: treat the denormal/zero regime (E = 0) as E = 1.
    let eff_e = biased_exp.max(1) as i64;
    Some(eff_e - fmt.bias - (fmt.precision() - 1))
}

// === Expr construction: emit `Rat.mk <Int> <Nat>` ===

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `Int.ofNat <nat>` for a non-negative magnitude.
fn int_of_nat(n: BigNat) -> Expr {
    Expr::app(const_("Int.ofNat"), Expr::bignat_lit(n))
}

/// Build `Rat.mk <int_num> <nat_den>`.
fn rat_mk(num: Expr, den: BigNat) -> Expr {
    Expr::apps(const_("Rat.mk"), [num, Expr::bignat_lit(den)])
}

/// Emit the EXACT rational `±num_mag · 2^exp` as a `Rat.mk <Int> <Nat>` whose
/// denominator is a power of two.
///
/// - `exp ≥ 0`: numerator `± (num_mag << exp)`, denominator `1`.
/// - `exp < 0`: numerator `± num_mag`,           denominator `2^(−exp)`.
///
/// A negative numerator is spelt with `Int.ofNat`/`Int.negSucc` exactly as the
/// `Int` inductive requires (`negSucc k` ≡ `−(k+1)`). A zero magnitude always
/// produces `Rat.mk (Int.ofNat 0) 1` regardless of sign (so `+0.0` and `−0.0`
/// both convert to the rational `0`).
fn emit_dyadic_rat(value: &DyadicValue) -> Expr {
    if value.num_mag.is_zero() {
        return rat_mk(int_of_nat(BigNat::Small(0)), BigNat::Small(1));
    }
    let (num_mag, den): (BigNat, BigNat) = if value.exp >= 0 {
        (
            shl_bignat(&value.num_mag, value.exp as u64),
            BigNat::Small(1),
        )
    } else {
        (value.num_mag.clone(), pow2_bignat((-value.exp) as u64))
    };
    let num = if value.sign {
        // Negative: −num_mag = Int.negSucc (num_mag − 1).
        let pred = num_mag.pred().unwrap_or(BigNat::Small(0)); // num_mag > 0 here, so pred is Some.
        Expr::app(const_("Int.negSucc"), Expr::bignat_lit(pred))
    } else {
        int_of_nat(num_mag)
    };
    rat_mk(num, den)
}

/// The non-negative magnitude of a dyadic value as a fraction `num / 2^den_exp`
/// (`num ≥ 0`, `den_exp ≥ 0`), i.e. `|±num_mag · 2^exp|`. `pub(crate)` so the
/// half-ulp discharge can cross-multiply two such magnitudes exactly.
///
/// - `exp ≥ 0`: `num = num_mag << exp`, `den_exp = 0`.
/// - `exp < 0`: `num = num_mag`,        `den_exp = −exp`.
#[cfg(any(test, feature = "math-overlays"))]
pub(crate) fn dyadic_nonneg_fraction(value: &DyadicValue) -> (BigNat, u64) {
    if value.num_mag.is_zero() {
        return (BigNat::Small(0), 0);
    }
    if value.exp >= 0 {
        (shl_bignat(&value.num_mag, value.exp as u64), 0)
    } else {
        (value.num_mag.clone(), (-value.exp) as u64)
    }
}

/// Emit `ulp = 2^q` (with the denormal floor already applied to `q`) as a
/// `Rat.mk <Int> <Nat>` power of two.
fn emit_ulp_rat(q: i64) -> Expr {
    if q >= 0 {
        rat_mk(int_of_nat(pow2_bignat(q as u64)), BigNat::Small(1))
    } else {
        rat_mk(int_of_nat(BigNat::Small(1)), pow2_bignat((-q) as u64))
    }
}

/// Extract the underlying bit-pattern `Nat` of a `Float` argument, accepting
/// both the bare `Lit(Nat)` intermediate form and the `Float.mk (Lit Nat)`
/// surface constructor form (ι-reduction of the `val` projection — sound).
fn get_float_bits(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, _) = f.kind() {
                if *name == *names::FLOAT_MK {
                    if let ExprKind::Lit(Literal::Nat(n)) = arg.kind() {
                        return n.to_u64();
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// A concrete dyadic rational `(-1)^sign · mag · 2^exp` parsed back OUT of a
/// `Rat.mk <Int> <Nat>` expression whose denominator is a power of two.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ParsedDyadic {
    pub sign: bool,
    pub mag: BigNat,
    /// Base-2 exponent: value is `±mag · 2^exp`.
    pub exp: i64,
}

/// `log2` of a `BigNat` that is exactly a power of two; `None` if it is not a
/// power of two (or is zero). Used to read a power-of-two denominator/grid back
/// as an exponent.
fn log2_exact(n: &BigNat) -> Option<u64> {
    if n.is_zero() {
        return None;
    }
    let limbs = n.limbs();
    let mut found: Option<u64> = None;
    for (i, &w) in limbs.iter().enumerate() {
        if w == 0 {
            continue;
        }
        if w & (w - 1) != 0 {
            return None; // more than one bit set in this limb
        }
        if found.is_some() {
            return None; // a set bit was already found in a lower limb
        }
        found = Some((i as u64) * 64 + w.trailing_zeros() as u64);
    }
    found
}

/// Extract a `Nat` literal (`BigNat`) from an `Expr` that is a `Lit(Nat)`.
fn get_bignat(e: &Expr) -> Option<BigNat> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => Some(n.clone()),
        _ => None,
    }
}

/// Parse a concrete `Rat.mk <Int> <Nat>` expression into a `ParsedDyadic`.
///
/// Accepts the numerator as `Int.ofNat <Nat>` (non-negative) or
/// `Int.negSucc <Nat>` (the negative `-(k+1)`), and REQUIRES the denominator to
/// be a power of two. Returns `None` for any other shape (so the reducer
/// declines and stays stuck rather than producing a wrong value).
fn parse_rat_mk(e: &Expr) -> Option<ParsedDyadic> {
    let args = e.get_app_args();
    if args.len() != 2 {
        return None;
    }
    if let ExprKind::Const(name, _) = e.get_app_fn().kind() {
        if name.to_string() != "Rat.mk" {
            return None;
        }
    } else {
        return None;
    }
    let den = get_bignat(args[1])?;
    let den_exp = log2_exact(&den)? as i64;

    // Numerator: Int.ofNat <Nat>  |  Int.negSucc <Nat>.
    let num_fn = args[0].get_app_fn();
    let num_args = args[0].get_app_args();
    let head = match num_fn.kind() {
        ExprKind::Const(n, _) => n.to_string(),
        _ => return None,
    };
    let (sign, mag) = match head.as_str() {
        "Int.ofNat" => (false, get_bignat(num_args.first()?)?),
        "Int.negSucc" => {
            // negSucc k = -(k+1).
            let k = get_bignat(num_args.first()?)?;
            (true, k.checked_add_big(&BigNat::Small(1)))
        }
        _ => return None,
    };
    Some(ParsedDyadic {
        sign,
        mag,
        exp: -den_exp,
    })
}

/// Round a dyadic value `q = ±mag·2^exp` to the nearest grid point of spacing
/// `V = 2^grid_exp`, ties-to-even, returning the rounded value as a
/// `DyadicValue` `±rounded_mag · 2^(−scale)`. The sign is preserved
/// (round-to-nearest is symmetric about 0; we round the magnitude and re-attach
/// the sign). `pub(crate)` so the half-ulp DISCHARGE can compute the rounded
/// value with the SAME arithmetic the native reducer uses.
pub(crate) fn round_dyadic_components(q: &ParsedDyadic, grid_exp: i64) -> DyadicValue {
    if q.mag.is_zero() {
        return DyadicValue {
            sign: false,
            num_mag: BigNat::Small(0),
            exp: 0,
        };
    }
    // Put |q| over a common denominator 2^scale with scale = max(-q.exp, -grid_exp, 0)
    // so that BOTH |q| and the grid spacing are integers in 1/2^scale units.
    let scale = (-q.exp).max(-grid_exp).max(0) as u64;
    // |q| = mag · 2^q.exp ; in 1/2^scale units the numerator is mag · 2^(scale + q.exp).
    let n_shift = (scale as i64 + q.exp) as u64; // ≥ 0 by choice of scale
    let n = shl_bignat(&q.mag, n_shift);
    // grid spacing in 1/2^scale units is 2^(scale + grid_exp).
    let g = (scale as i64 + grid_exp) as u64; // ≥ 0 by choice of scale
    let rounded_mag = round_half_even_pow2(&n, g); // a multiple of 2^g, in 1/2^scale units.
    DyadicValue {
        sign: q.sign,
        num_mag: rounded_mag,
        exp: -(scale as i64),
    }
}

/// Round a parsed dyadic value `q` to the nearest grid point of spacing `V =
/// 2^grid_exp`, ties-to-even, returning the rounded value as an emitted
/// `Rat.mk`.
fn round_dyadic_to_grid(q: &ParsedDyadic, grid_exp: i64) -> Expr {
    emit_dyadic_rat(&round_dyadic_components(q, grid_exp))
}

/// Native reducer for `Rat.roundToNearestEven : Rat → Rat → Rat`.
///
/// `Rat.roundToNearestEven q V` rounds the rational `q` to the nearest integer
/// multiple of the grid spacing `V` (a positive power-of-two `Rat`, the ulp),
/// **ties-to-even**, and emits the rounded value as a `Rat.mk` the kernel can
/// compare. This is the Rat-level counterpart of `Nat.roundHalfEvenMod`: on the
/// magnitude it computes `roundHalfEvenMod |q| V` over the shared dyadic grid,
/// which is exactly the IEEE-754 round-to-nearest-even at grid spacing `V`. In
/// the DENORMAL regime `V` is the FLOORED ulp `2^(emin−p+1)`, and the grid is
/// uniform at that spacing — so the same computation (and the same Nat bound)
/// covers subnormals. Declines (stays stuck) unless both args are concrete
/// power-of-two-denominator `Rat.mk`s with `V` a power of two.
pub(crate) fn reduce_rat_round_to_nearest_even(args: &[&Expr]) -> Option<Expr> {
    let q = parse_rat_mk(args.first()?)?;
    let v = parse_rat_mk(args.get(1)?)?;
    // V must be a positive power of two: magnitude exactly 1 (so value 2^v.exp),
    // non-negative. (mag == 1 ∧ ¬sign.)
    if v.sign || v.mag != BigNat::Small(1) {
        return None;
    }
    Some(round_dyadic_to_grid(&q, v.exp))
}

/// Native reducer for `Float.toRatExact : Float → Rat` (binary64).
///
/// Reduces `Float.toRatExact (Float.mk <bits>)` to the EXACT rational value of
/// the binary64 with that bit pattern, as a `Rat.mk <Int> <Nat>` (denominator a
/// power of two). Declines (returns `None`) for Inf/NaN bit patterns, which
/// have no exact rational value, so the kernel falls back to the opaque
/// placeholder (never unfolds → stays stuck, never produces a wrong value).
pub(crate) fn reduce_float_to_rat_exact(args: &[&Expr]) -> Option<Expr> {
    let bits = get_float_bits(args.first()?)?;
    let value = decompose_exact(bits, &IeeeFormat::BINARY64)?;
    Some(emit_dyadic_rat(&value))
}

/// Native reducer for `Float.ulpExact : Float → Rat` (binary64).
///
/// Reduces to `2^q`, the unit in the last place, with the denormal-ulp floor
/// applied (`q = max(E,1) − bias − (p−1)`). Declines for Inf/NaN.
pub(crate) fn reduce_float_ulp_exact(args: &[&Expr]) -> Option<Expr> {
    let bits = get_float_bits(args.first()?)?;
    let q = ulp_quantum_exp(bits, &IeeeFormat::BINARY64)?;
    Some(emit_ulp_rat(q))
}

impl Environment {
    /// Register the `Float.toRatExact` / `Float.ulpExact` native reducers.
    ///
    /// Idempotent insofar as `register_native_reducer` overwrites; called
    /// alongside the other Float reducers in the prelude setup.
    pub(crate) fn init_float_to_rat_native_reducers(&mut self) {
        self.register_native_reducer(names::FLOAT_TO_RAT_EXACT.clone(), reduce_float_to_rat_exact);
        self.register_native_reducer(names::FLOAT_ULP_EXACT.clone(), reduce_float_ulp_exact);
        self.register_native_reducer(
            names::RAT_ROUND_TO_NEAREST_EVEN.clone(),
            reduce_rat_round_to_nearest_even,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk_float(bits: u64) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Float.mk"), vec![]),
            Expr::nat_lit(bits),
        )
    }

    /// Pretty-print an emitted `Rat.mk (Int...) (Nat)` as `(sign num)/den` so
    /// reduction outputs are legible in test output.
    fn show_rat(e: &Expr) -> String {
        // Expect: App(App(Const "Rat.mk", num), den)
        let den = match e.get_app_args().get(1).map(|d| d.kind()) {
            Some(ExprKind::Lit(Literal::Nat(n))) => format!("{n:?}"),
            other => format!("{other:?}"),
        };
        let num = match e.get_app_args().first().map(|n| n.kind()) {
            Some(ExprKind::App(f, a)) => {
                let head = match f.kind() {
                    ExprKind::Const(name, _) => name.to_string(),
                    _ => "?".into(),
                };
                let mag = match a.kind() {
                    ExprKind::Lit(Literal::Nat(n)) => format!("{n:?}"),
                    other => format!("{other:?}"),
                };
                format!("{head}({mag})")
            }
            other => format!("{other:?}"),
        };
        format!("Rat.mk {num} {den}")
    }

    // --- classification across the three regimes ---

    #[test]
    fn test_classify_all_regimes() {
        let f = IeeeFormat::BINARY64;
        assert_eq!(classify(1.0f64.to_bits(), &f), FloatClass::Normal);
        assert_eq!(classify(0.0f64.to_bits(), &f), FloatClass::Zero);
        assert_eq!(classify((-0.0f64).to_bits(), &f), FloatClass::Zero);
        assert_eq!(classify(1u64, &f), FloatClass::Subnormal); // smallest subnormal
        assert_eq!(classify(0x000F_FFFF_FFFF_FFFF, &f), FloatClass::Subnormal); // largest
        assert_eq!(classify(f64::INFINITY.to_bits(), &f), FloatClass::NonFinite);
        assert_eq!(classify(f64::NAN.to_bits(), &f), FloatClass::NonFinite);
    }

    // --- exact decomposition: normal ---

    #[test]
    fn test_decompose_one() {
        let d = decompose_exact(1.0f64.to_bits(), &IeeeFormat::BINARY64).unwrap();
        // 1.0 = 2^52 · 2^-52.
        assert!(!d.sign);
        assert_eq!(d.num_mag, BigNat::Small(1u64 << 52));
        assert_eq!(d.exp, -52);
    }

    #[test]
    fn test_decompose_point_one() {
        let d = decompose_exact(0.1f64.to_bits(), &IeeeFormat::BINARY64).unwrap();
        // 0.1 stored as 7205759403792794 / 2^56.
        assert!(!d.sign);
        assert_eq!(d.num_mag, BigNat::Small(7205759403792794));
        assert_eq!(d.exp, -56);
    }

    #[test]
    fn test_decompose_power_of_two_boundary() {
        // 2.0 = 2^52 · 2^-51 ; 0.5 = 2^52 · 2^-53. Boundary across the exponent.
        let two = decompose_exact(2.0f64.to_bits(), &IeeeFormat::BINARY64).unwrap();
        assert_eq!(
            (two.num_mag.clone(), two.exp),
            (BigNat::Small(1u64 << 52), -51)
        );
        let half = decompose_exact(0.5f64.to_bits(), &IeeeFormat::BINARY64).unwrap();
        assert_eq!((half.num_mag, half.exp), (BigNat::Small(1u64 << 52), -53));
    }

    // --- exact decomposition: subnormal / zero (the underflow-relevant regime) ---

    #[test]
    fn test_decompose_smallest_subnormal() {
        // f64::from_bits(1) = 2^-1074 (smallest positive subnormal, ≈ 5e-324).
        let d = decompose_exact(1u64, &IeeeFormat::BINARY64).unwrap();
        assert!(!d.sign);
        assert_eq!(d.num_mag, BigNat::Small(1));
        assert_eq!(d.exp, -1074); // emin - (p-1) = -1022 - 52
    }

    #[test]
    fn test_decompose_signed_zero() {
        let pz = decompose_exact(0.0f64.to_bits(), &IeeeFormat::BINARY64).unwrap();
        let nz = decompose_exact((-0.0f64).to_bits(), &IeeeFormat::BINARY64).unwrap();
        assert!(pz.num_mag.is_zero() && nz.num_mag.is_zero());
        assert!(!pz.sign && nz.sign); // sign bit preserved...
                                      // ...but both emit the rational 0.
        assert_eq!(
            show_rat(&emit_dyadic_rat(&pz)),
            "Rat.mk Int.ofNat(Small(0)) Small(1)"
        );
        assert_eq!(
            show_rat(&emit_dyadic_rat(&nz)),
            "Rat.mk Int.ofNat(Small(0)) Small(1)"
        );
    }

    #[test]
    fn test_decompose_inf_nan_declines() {
        assert!(decompose_exact(f64::INFINITY.to_bits(), &IeeeFormat::BINARY64).is_none());
        assert!(decompose_exact(f64::NAN.to_bits(), &IeeeFormat::BINARY64).is_none());
        assert!(ulp_quantum_exp(f64::NAN.to_bits(), &IeeeFormat::BINARY64).is_none());
    }

    // --- the DENORMAL ULP FLOOR ---

    #[test]
    fn test_ulp_floor_at_denormal() {
        let f = IeeeFormat::BINARY64;
        // Every subnormal AND zero floors at q = emin - (p-1) = -1074.
        assert_eq!(ulp_quantum_exp(0.0f64.to_bits(), &f), Some(-1074));
        assert_eq!(ulp_quantum_exp((-0.0f64).to_bits(), &f), Some(-1074));
        assert_eq!(ulp_quantum_exp(1u64, &f), Some(-1074)); // smallest subnormal
        assert_eq!(ulp_quantum_exp(0x000F_FFFF_FFFF_FFFF, &f), Some(-1074)); // largest subnormal
                                                                             // The smallest NORMAL (bits 0x0010...0, E=1) also has q = -1074 — the
                                                                             // floor and the normal formula coincide exactly at the boundary.
        assert_eq!(ulp_quantum_exp(0x0010_0000_0000_0000, &f), Some(-1074));
        // A normal value's ulp tracks its exponent: ulp(1.0) = 2^-52.
        assert_eq!(ulp_quantum_exp(1.0f64.to_bits(), &f), Some(-52));
    }

    // --- binary32 instantiation (parameterized format) ---

    #[test]
    fn test_binary32_subnormal_and_one() {
        let f = IeeeFormat::BINARY32;
        // f32 smallest subnormal (bits 0x1) = 2^-149.
        let sub = decompose_exact(1u64, &f).unwrap();
        assert_eq!((sub.num_mag, sub.exp), (BigNat::Small(1), -149));
        assert_eq!(ulp_quantum_exp(1u64, &f), Some(-149)); // floor at emin-(p-1) = -126-23
                                                           // f32 1.0 (bits 0x3F800000): m = 2^23, e = -23.
        let one = decompose_exact(0x3F80_0000, &f).unwrap();
        assert_eq!((one.num_mag, one.exp), (BigNat::Small(1u64 << 23), -23));
    }

    // --- emitted Rat.mk form ---

    #[test]
    fn test_emit_negative_uses_neg_succ() {
        // -1.0 : sign set, m=2^52, e=-52 -> num Int.negSucc (2^52 - 1), den 2^52.
        let d = decompose_exact((-1.0f64).to_bits(), &IeeeFormat::BINARY64).unwrap();
        let e = emit_dyadic_rat(&d);
        let head = match e.get_app_args().first().unwrap().get_app_fn().kind() {
            ExprKind::Const(name, _) => name.to_string(),
            _ => "?".into(),
        };
        assert_eq!(head, "Int.negSucc");
    }

    // --- end-to-end reducers ---

    #[test]
    fn test_reduce_to_rat_exact_point_one() {
        let out = reduce_float_to_rat_exact(&[&mk_float(0.1f64.to_bits())]).unwrap();
        // 7205759403792794 / 2^56.
        assert_eq!(
            show_rat(&out),
            "Rat.mk Int.ofNat(Small(7205759403792794)) Small(72057594037927936)"
        );
    }

    #[test]
    fn test_reduce_ulp_exact_subnormal_floor() {
        // ulp of the smallest subnormal is 2^-1074 (the denormal floor).
        let out = reduce_float_ulp_exact(&[&mk_float(1u64)]).unwrap();
        // 2^-1074 = Rat.mk (Int.ofNat 1) (2^1074). 2^1074 is a Big nat — just
        // assert the numerator is 1 and the denominator is non-`Small` (huge).
        let num_mag = match out
            .get_app_args()
            .first()
            .unwrap()
            .get_app_args()
            .first()
            .map(|a| a.kind())
        {
            Some(ExprKind::Lit(Literal::Nat(n))) => n.clone(),
            other => panic!("unexpected numerator {other:?}"),
        };
        assert_eq!(num_mag, BigNat::Small(1));
        let den = match out.get_app_args().get(1).map(|d| d.kind()) {
            Some(ExprKind::Lit(Literal::Nat(n))) => n.clone(),
            other => panic!("unexpected denominator {other:?}"),
        };
        // 2^1074 needs ceil(1075/64) = 17 limbs — definitely a Big.
        assert!(matches!(den, BigNat::Big(_)), "2^1074 must be a Big nat");
    }

    #[test]
    fn test_reducers_decline_on_inf_nan() {
        assert!(reduce_float_to_rat_exact(&[&mk_float(f64::INFINITY.to_bits())]).is_none());
        assert!(reduce_float_to_rat_exact(&[&mk_float(f64::NAN.to_bits())]).is_none());
        assert!(reduce_float_ulp_exact(&[&mk_float(f64::NAN.to_bits())]).is_none());
    }

    // --- round-to-nearest-even helpers ---

    #[test]
    fn test_shr_and_bits_bignat() {
        // 0b1011 = 11. >>1 = 5, >>2 = 2.
        assert_eq!(shr_bignat(&BigNat::Small(11), 1), BigNat::Small(5));
        assert_eq!(shr_bignat(&BigNat::Small(11), 2), BigNat::Small(2));
        assert_eq!(shr_bignat(&BigNat::Small(11), 4), BigNat::Small(0));
        // cross-limb: (3<<64) >> 64 = 3.
        assert_eq!(
            shr_bignat(&BigNat::from_limbs(vec![0, 3]), 64),
            BigNat::Small(3)
        );
        assert!(test_bit_bignat(&BigNat::Small(0b1010), 1));
        assert!(!test_bit_bignat(&BigNat::Small(0b1010), 0));
        assert!(test_bit_bignat(&BigNat::Small(0b1010), 3));
        // low 1 bit of 0b1010 is zero; low 2 bits of 0b1010 are not.
        assert!(low_bits_zero_bignat(&BigNat::Small(0b1010), 1));
        assert!(!low_bits_zero_bignat(&BigNat::Small(0b1010), 2));
    }

    #[test]
    fn test_round_half_even_pow2_cases() {
        // Round to nearest multiple of 2^2 = 4, ties-to-even.
        // 5 = 4+1 → round bit (bit1) = 0 → down → 4.
        assert_eq!(round_half_even_pow2(&BigNat::Small(5), 2), BigNat::Small(4));
        // 7 = 4+3 → 2r = 6 > 4 → up → 8.
        assert_eq!(round_half_even_pow2(&BigNat::Small(7), 2), BigNat::Small(8));
        // 6 = exact tie (2r = 4) ; q = 1 (odd) → round up → 8.
        assert_eq!(round_half_even_pow2(&BigNat::Small(6), 2), BigNat::Small(8));
        // 2 = exact tie (2r = 4) ; q = 0 (even) → keep → 0.
        assert_eq!(round_half_even_pow2(&BigNat::Small(2), 2), BigNat::Small(0));
        // 10 = exact tie (2r = 4) at q = 2 (even) → keep → 8.
        assert_eq!(
            round_half_even_pow2(&BigNat::Small(10), 2),
            BigNat::Small(8)
        );
        // g = 0: already on grid.
        assert_eq!(round_half_even_pow2(&BigNat::Small(7), 0), BigNat::Small(7));
    }

    #[test]
    fn test_log2_exact() {
        assert_eq!(log2_exact(&BigNat::Small(1)), Some(0));
        assert_eq!(log2_exact(&BigNat::Small(1 << 52)), Some(52));
        assert_eq!(log2_exact(&pow2_bignat(1074)), Some(1074));
        assert_eq!(log2_exact(&BigNat::Small(3)), None); // not a power of two
        assert_eq!(log2_exact(&BigNat::Small(0)), None);
    }

    #[test]
    fn test_parse_rat_mk_roundtrip() {
        // +0.1 dyadic emitted then re-parsed.
        let d = decompose_exact(0.1f64.to_bits(), &IeeeFormat::BINARY64).unwrap();
        let e = emit_dyadic_rat(&d);
        let p = parse_rat_mk(&e).unwrap();
        assert!(!p.sign);
        assert_eq!(p.mag, BigNat::Small(7205759403792794));
        assert_eq!(p.exp, -56);
        // -1.0 → negSucc form.
        let dn = decompose_exact((-1.0f64).to_bits(), &IeeeFormat::BINARY64).unwrap();
        let en = emit_dyadic_rat(&dn);
        let pn = parse_rat_mk(&en).unwrap();
        assert!(pn.sign);
        assert_eq!(pn.mag, BigNat::Small(1u64 << 52));
        assert_eq!(pn.exp, -52);
    }

    /// A rational already on-grid rounds to itself (error 0).
    #[test]
    fn test_round_to_grid_exact_is_fixed_point() {
        // q = 3/4 = 3·2^-2 ; grid V = 2^-2. Already a multiple → unchanged.
        let q = ParsedDyadic {
            sign: false,
            mag: BigNat::Small(3),
            exp: -2,
        };
        let out = round_dyadic_to_grid(&q, -2);
        let p = parse_rat_mk(&out).unwrap();
        // 3/4 = 6/8 emitted as 3·2^-2; magnitude·2^exp must equal 3/4.
        // Re-parsed exp is -scale = -2, mag = 3.
        assert!(!p.sign);
        assert_eq!(p.mag, BigNat::Small(3));
        assert_eq!(p.exp, -2);
    }

    /// A tie at an odd grid index rounds up; the reducer end-to-end.
    #[test]
    fn test_reduce_round_tie_to_even() {
        // q = 3/4 = 3·2^-2 ; grid V = 2^-1 (= 1/2). Multiples of 1/2: …,1/2,1,…
        // 3/4 is the exact midpoint of 1/2 and 1. Nearest-even: 1/2 has index 1
        // (odd), 1 has index 2 (even) → ties-to-even rounds to 1 = 1/1.
        let q = rat_mk(int_of_nat(BigNat::Small(3)), pow2_bignat(2)); // 3/4
        let v = rat_mk(int_of_nat(BigNat::Small(1)), pow2_bignat(1)); // 1/2
        let out = reduce_rat_round_to_nearest_even(&[&q, &v]).unwrap();
        let p = parse_rat_mk(&out).unwrap();
        // Result should be 1 = 1·2^0 (after common-scale, mag=2, exp=-1 i.e. 2/2=1).
        // Value = mag · 2^exp must equal 1.
        let val_num = p.mag.clone();
        let val_den = pow2_bignat((-p.exp) as u64);
        assert_eq!(
            val_num, val_den,
            "rounded value must equal 1; got {val_num:?}/{val_den:?}"
        );
    }

    /// The reducer declines when the grid is not a power of two.
    #[test]
    fn test_reduce_round_declines_nonpow2_grid() {
        let q = rat_mk(int_of_nat(BigNat::Small(3)), pow2_bignat(2));
        // V = 3/4 (mag 3, not a power of two as a *value*; mag != 1).
        let v = rat_mk(int_of_nat(BigNat::Small(3)), pow2_bignat(2));
        assert!(reduce_rat_round_to_nearest_even(&[&q, &v]).is_none());
    }

    #[test]
    fn test_pow2_and_shl_bignat() {
        assert_eq!(pow2_bignat(0), BigNat::Small(1));
        assert_eq!(pow2_bignat(52), BigNat::Small(1u64 << 52));
        assert_eq!(pow2_bignat(63), BigNat::Small(1u64 << 63));
        // 2^64 crosses the limb boundary.
        assert_eq!(pow2_bignat(64), BigNat::from_limbs(vec![0, 1]));
        // shl: 3 << 64 = 3 * 2^64.
        assert_eq!(
            shl_bignat(&BigNat::Small(3), 64),
            BigNat::from_limbs(vec![0, 3])
        );
        // shl by a non-multiple of 64 with carry across limbs: (2^63) << 1 = 2^64.
        assert_eq!(
            shl_bignat(&BigNat::Small(1u64 << 63), 1),
            BigNat::from_limbs(vec![0, 1])
        );
    }
}
