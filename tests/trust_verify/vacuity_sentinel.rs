// Trust verification SOUNDNESS canaries.
//
// Each function below contains a Level-0 safety obligation that is *genuinely
// false* — the code really does fault at runtime. A SOUND Trust verifier must
// therefore report each obligation as `failed` (counterexample found) or
// `unknown` (could not decide) — but NEVER `proved`.
//
// These are the negative half of the twin verification ratchet
// (see data/trust_verify_ratchet.json + scripts/trust_verify_ratchet.sh).
// If a trust-vcgen change — e.g. the recursive-datatype encoding (Lever A) —
// ever makes one of these come back `proved`, the SMT context has gone
// vacuously UNSAT and the verifier is unsound (it would false-prove
// everything). That is a soundness regression and blocks unconditionally; it
// can never be baselined away.
//
// Compiled standalone by the ratchet with the Trust toolchain:
//   trustc --edition 2021 --crate-type lib -Ztrust-verify-output=human \
//          tests/trust_verify/vacuity_sentinel.rs
// No dependencies — keep it that way so the canary is fast and self-contained.

#![allow(unconditional_panic, unused)]

/// Guaranteed out-of-bounds: `a[a.len()]` indexes one past the end. The slice
/// obligation is `a.len() < a.len()`, which is false. MUST NOT be proved.
#[inline(never)]
pub fn sentinel_oob_index_must_not_prove(a: &[u8]) -> u8 {
    a[a.len()] // TRUST_FALSE_CANARY: slice#bounds_check:0
}

/// Guaranteed division by zero: `n - n` is always 0. The divisor-nonzero
/// obligation is `0 != 0`, which is false. MUST NOT be proved.
#[inline(never)]
pub fn sentinel_div_by_zero_must_not_prove(x: u64, n: u64) -> u64 {
    x / (n - n) // TRUST_FALSE_CANARY: divzero#arithmetic_safety:0
}

/// Guaranteed OOB produced through a LOSSY narrowing cast. Integer `as` itself is
/// defined Rust behavior, so it deliberately carries no panic obligation. Here
/// `(x << 8) | 1` always truncates to the u8 value 1; indexing a one-element array
/// at that value is genuinely out of bounds. The bounds obligation MUST NOT prove,
/// which pins the verifier's target-type/truncation tracking without fabricating a
/// losslessness requirement Rust does not have.
///
/// This replaces the obsolete pre-9f4b2c8417 canary that treated truncation itself
/// as a safety failure, contradicting the repository's defined-cast policy.
#[inline(never)]
pub fn sentinel_lossy_narrowing_cast_must_not_prove(x: u64) -> u8 {
    let narrowed = ((x << 8) | 1) as u8;
    [0u8; 1][narrowed as usize] // TRUST_FALSE_CANARY: bounds#bounds_check:0
}

/// Guaranteed arithmetic OVERFLOW (clean-kernel is compiled overflow-checks=ON, so a
/// plain `+` lowers to a checked add with a real no-overflow obligation): `x + u32::MAX`
/// overflows for every `x >= 1`. Its no-overflow obligation is genuinely false. MUST NOT
/// be proved — guards against an over-broad "treat arithmetic as total" lever.
#[inline(never)]
pub fn sentinel_unguarded_add_overflow_must_not_prove(x: u32) -> u32 {
    x + u32::MAX // TRUST_FALSE_CANARY: overflow:add#arithmetic_safety:0
}

/// Guaranteed REMAINDER-by-zero: `x % (n - n)` takes the remainder modulo 0. Its
/// divisor-nonzero obligation is genuinely false. MUST NOT be proved.
#[inline(never)]
pub fn sentinel_remainder_by_zero_must_not_prove(x: u64, n: u64) -> u64 {
    x % (n - n) // TRUST_FALSE_CANARY: remzero#arithmetic_safety:0
}

/// Guaranteed subtraction UNDERFLOW (overflow-checks ON): `(x & 0) - 1` computes `0 - 1`
/// on u32, which underflows. Its no-underflow obligation is genuinely false. MUST NOT be
/// proved.
#[inline(never)]
pub fn sentinel_sub_underflow_must_not_prove(x: u32) -> u32 {
    (x & 0) - 1 // TRUST_FALSE_CANARY: overflow:sub#arithmetic_safety:0
}

/// Guaranteed multiplication OVERFLOW: `big * big` with `big >= 2^20` is `>= 2^40 > u32::MAX`.
/// Its no-overflow obligation is genuinely false. MUST NOT be proved.
#[inline(never)]
pub fn sentinel_mul_overflow_must_not_prove(x: u32) -> u32 {
    let big = x | (1u32 << 20); // big >= 2^20
    big * big // TRUST_FALSE_CANARY: overflow:mul#arithmetic_safety:0
}

/// Guaranteed slice-range OUT-OF-BOUNDS: `&a[..a.len() + 1]` has an end strictly past the
/// slice length. Its end<=len obligation is genuinely false. MUST NOT be proved.
#[inline(never)]
pub fn sentinel_slice_range_oob_must_not_prove(a: &[u8]) -> &[u8] {
    &a[..a.len() + 1] // TRUST_FALSE_CANARY: slice#bounds_check:0
}

// ---------------------------------------------------------------------------
// TIER-1 canaries closing gaps vs the trust falsification gate (94 mutants):
// classes the gate catches that the 8 above did not. The falsification gate is
// NOT always-on (manual, hours), so these clean canaries are the only ALWAYS-ON
// (pre-push) soundness guard — they must cover the obligation classes a lever
// could falsely certify. Each obligation below is genuinely false → MUST refute.
// ---------------------------------------------------------------------------

/// Guaranteed SHIFT-AMOUNT >= bit-width: `s = x | 64 >= 64 >= 32`, so `1u32 << s`
/// shifts a u32 by at least its bit width (UB). The shift-in-range obligation
/// (`s < 32`) is genuinely false. MUST NOT be proved.
#[inline(never)]
pub fn sentinel_shift_overflow_must_not_prove(x: u32) -> u32 {
    let s = x | 64; // s >= 64 >= 32 (bit width of u32)
    1u32 << s // TRUST_FALSE_CANARY: shift:left#arithmetic_safety:0
}

/// Guaranteed loop OFF-BY-ONE: `for i in 0..=a.len()` includes `i == a.len()`, so
/// `a[i]` indexes one past the end. The index-in-bounds obligation is genuinely
/// false (at the last iteration). MUST NOT be proved.
#[inline(never)]
pub fn sentinel_loop_off_by_one_must_not_prove(a: &[u8]) -> u8 {
    let mut acc = 0u8;
    for i in 0..=a.len() {
        acc = acc.wrapping_add(a[i]); // TRUST_FALSE_CANARY: slice#bounds_check:0
    }
    acc
}

/// Guaranteed CLAMP-still-OOB: `x.min(a.len())` can equal `a.len()` (when x is large),
/// and `a[a.len()]` is out of bounds. The min/clamp does NOT make the index safe —
/// the index-in-bounds obligation is genuinely false. MUST NOT be proved.
#[inline(never)]
pub fn sentinel_clamp_still_oob_must_not_prove(a: &[u8], x: usize) -> u8 {
    let idx = x.min(a.len()); // idx can == a.len()
    a[idx] // TRUST_FALSE_CANARY: slice#bounds_check:0
}

/// Guaranteed MULTI-VARIABLE truncation-to-OOB path. At `a == 129 && b == 128`,
/// the u16 sum is 257 and its defined u8 truncation is 1, which is out of bounds
/// for a one-element array. This pins conjunctive-guard and cast-result reasoning;
/// the bounds obligation is genuinely false and MUST NOT be proved.
#[inline(never)]
pub fn sentinel_multivar_guard_lossy_must_not_prove(a: u16, b: u16) -> u8 {
    if a == 129 && b == 128 {
        let idx = (a + b) as u8;
        [0u8; 1][idx as usize] // TRUST_FALSE_CANARY: bounds#bounds_check:1
    } else {
        0
    }
}

// ---------------------------------------------------------------------------
// TIER-2 canaries (further falsification-gate classes; both confirmed to refute
// cleanly with `[slice] FAILED` on verifier 64311b625).
// ---------------------------------------------------------------------------

/// Guaranteed STALE GUARD: `idx` is bounds-checked, then REASSIGNED to the unbounded
/// `y` before the index — the guard no longer applies. `a[idx]` (= `a[y]`) is OOB.
/// The index-in-bounds obligation is genuinely false (the verifier must track that the
/// guarded value was overwritten). MUST NOT be proved. [falsification: merged_local_index]
#[inline(never)]
pub fn sentinel_stale_guard_must_not_prove(a: &[u8], x: usize, y: usize) -> u8 {
    let mut idx = x;
    if idx < a.len() {
        idx = y; // reassigned AFTER the guard; y is unbounded
        return a[idx]; // TRUST_FALSE_CANARY: slice#bounds_check:0
    }
    0
}

/// Guaranteed INTRINSIC-BOUND miss: `x.leading_zeros()` ranges over `[0, 32]`, which is
/// NOT bounded by `a.len()`. `a[i]` is OOB whenever `a.len() <= i`. The index-in-bounds
/// obligation is genuinely false. MUST NOT be proved. [falsification: external_call_guarded]
#[inline(never)]
pub fn sentinel_intrinsic_bound_must_not_prove(a: &[u8], x: u32) -> u8 {
    let i = x.leading_zeros() as usize; // in [0, 32], not bounded by len
    a[i] // TRUST_FALSE_CANARY: slice#bounds_check:0
}

/// Guaranteed LOOP-ACCUMULATOR overflow: summing an unbounded-length slice of u32 into a
/// u32 accumulator overflows (the verifier must reason about the loop, not just one op).
/// The per-iteration no-overflow obligation is genuinely false. MUST NOT be proved.
/// [falsification: wide_unsigned_accumulator / foreach_slice_sum]
#[inline(never)]
pub fn sentinel_accumulator_overflow_must_not_prove(a: &[u32]) -> u32 {
    let mut s: u32 = 0;
    for &x in a {
        s += x; // TRUST_FALSE_CANARY: overflow:add#arithmetic_safety:0
    }
    s
}
