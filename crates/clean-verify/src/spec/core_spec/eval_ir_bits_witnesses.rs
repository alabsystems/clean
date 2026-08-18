// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — **the differential ladder for [`super::eval_ir_bits`]**.
//!
//! `ir_nat_divmod` is not proved equal to `ir_nat_div` / `ir_nat_rem` and
//! `ir_nat_mulb` is not proved equal to `ir_nat_mul` — those are two different
//! algorithms agreeing, which in this substrate goes through a loop invariant
//! plus uniqueness of quotient and is not attempted. **This file is what stands
//! in for those theorems**: every new operation, run by the KERNEL against the
//! reference definition at every argument where the reference is affordable,
//! plus round-trip witnesses at the widths where the reference does not exist
//! at all.
//!
//! It is the same evidential bar [`super::eval_ir_float`] sets for its tables,
//! and it is not a proof. Split from its module only because
//! `data/paragon_ratchet.json`'s `files_over_500` is shrink-only.
//!
//! `DerivedProved`, empty axiom closures.

/// `(name, source, description)` for every differential witness.
///
/// These are the evidence that stands in for the unattempted agreement
/// theorems, and they are chosen so the reference side is affordable: every
/// `ir_nat_div` here has a small quotient, and every `ir_nat_mul` a small
/// second operand.
pub(in crate::spec::core_spec) const BITS_WITNESSES: &[(&str, &str, &str)] = &[
    (
        "ir_nat_dbl_w",
        "def ir_nat_dbl_w : Eq Nat (ir_nat_dbl 9007199254740991) 18014398509481982 := Eq.refl Nat 18014398509481982",
        "The strict doubling on a 53-bit literal. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_dbl_zero_w",
        "def ir_nat_dbl_zero_w : Eq Nat (ir_nat_dbl Nat.zero) Nat.zero := Eq.refl Nat Nat.zero",
        "2 * 0 = 0, the recursor's base minor. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_dbl_eq_w",
        "def ir_nat_dbl_eq_w : Eq Nat (ir_nat_dbl 7) (Nat.add 7 7) := ir_nat_dbl_eq 7",
        "The doubling agreement theorem, INSTANTIATED — so the general lemma is known to have a \
         satisfiable use and not only a well-typed statement. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_shl_w",
        "def ir_nat_shl_w : Eq Nat (ir_nat_shl 3 10) 3072 := Eq.refl Nat 3072",
        "3 << 10. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_shl_mul_w",
        "def ir_nat_shl_mul_w : Eq Nat (ir_nat_shl 3 10) (ir_nat_mul 3 (ir_nat_pow2 10)) := Eq.refl Nat 3072",
        "*** DIFFERENTIAL: the left shift IS `ir_nat_mul m (2^k)`, run by the kernel. *** The \
         reference side is affordable here because ir_nat_mul recurses on its second argument and \
         2^10 is 1024 additions. At the shifts binary64 alignment needs (up to 2045) the \
         reference side is 2^2045 additions and this witness cannot be written — which is the \
         whole reason ir_nat_shl exists. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_shl_zero_w",
        "def ir_nat_shl_zero_w : Eq Nat (ir_nat_shl 9007199254740991 Nat.zero) 9007199254740991 := Eq.refl Nat 9007199254740991",
        "A shift by zero is the identity. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_bitlen_w",
        "def ir_nat_bitlen_w : Eq Nat (ir_nat_bitlen 9007199254740991) 53 := Eq.refl Nat 53",
        "2^53 - 1 has 53 bits. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_bitlen_zero_w",
        "def ir_nat_bitlen_zero_w : Eq Nat (ir_nat_bitlen Nat.zero) Nat.zero := Eq.refl Nat Nat.zero",
        "Zero has no bits — the case that makes the renormalising shift maximal, and the input \
         the scope document's cost anomaly was wrongly attributed to. DerivedProved, zero \
         axiom_deps.",
    ),
    (
        "ir_nat_bitlen_wide_w",
        "def ir_nat_bitlen_wide_w : Eq Nat (ir_nat_bitlen (ir_nat_shl 9007199254740991 2045)) 2098 := Eq.refl Nat 2098",
        "THE WIDEST INTERMEDIATE binary64 addition can build: a 53-bit significand aligned across \
         the maximum exponent distance, 2098 bits, scanned. Both the shift and the scan are \
         O(bits) and this runs. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_divmod_q_w",
        "def ir_nat_divmod_q_w : Eq Nat (ir_dm_quot (ir_nat_divmod 17 5)) (ir_nat_div 17 5) := Eq.refl Nat 3",
        "*** DIFFERENTIAL: the restoring quotient IS ir_nat_div's quotient. *** Run by the \
         kernel, both sides computed. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_divmod_r_w",
        "def ir_nat_divmod_r_w : Eq Nat (ir_dm_rem (ir_nat_divmod 17 5)) (ir_nat_rem 17 5) := Eq.refl Nat 2",
        "*** DIFFERENTIAL: the restoring remainder IS ir_nat_rem. *** DerivedProved, zero \
         axiom_deps.",
    ),
    (
        "ir_nat_divmod_exact_w",
        "def ir_nat_divmod_exact_w : Eq Nat (ir_dm_rem (ir_nat_divmod 4096 256)) (ir_nat_rem 4096 256) := Eq.refl Nat Nat.zero",
        "An exact division: remainder zero on both sides. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_divmod_one_w",
        "def ir_nat_divmod_one_w : Eq Nat (ir_dm_quot (ir_nat_divmod 9007199254740991 (Nat.succ Nat.zero))) 9007199254740991 := Eq.refl Nat 9007199254740991",
        "Division by one at a 53-bit dividend. The reference `ir_nat_div 9007199254740991 1` has \
         a 2^53 quotient and is roughly 39,700 years, so this row has NO reference column — it is \
         precisely the wall this module removes. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_divpow2_w",
        "def ir_nat_divpow2_w : Eq Nat (ir_dm_quot (ir_nat_divpow2 9218868437227405312 52)) 2047 := Eq.refl Nat 2047",
        "The binary64 exponent-field extract: 0x7FF0000000000000 / 2^52 = 2047. The reference \
         `ir_nat_div` computes the same 2047 in 0.428 s where this is 0.011 s. DerivedProved, \
         zero axiom_deps.",
    ),
    (
        "ir_nat_divpow2_ref_w",
        "def ir_nat_divpow2_ref_w : Eq Nat (ir_dm_quot (ir_nat_divpow2 9218868437227405312 52)) (ir_nat_div 9218868437227405312 (ir_nat_pow2 52)) := Eq.refl Nat 2047",
        "*** DIFFERENTIAL at the widest quotient the reference can still reach. *** Both sides \
         run by the kernel on a 9.2e18 dividend; the reference costs 2047 loop iterations and \
         this costs 53 steps. One doubling of the quotient doubles the reference and leaves this \
         unchanged. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_divpow2_rem_w",
        "def ir_nat_divpow2_rem_w : Eq Nat (ir_dm_rem (ir_nat_divpow2 9007199254740991 (Nat.succ Nat.zero))) (Nat.succ Nat.zero) := Eq.refl Nat (Nat.succ Nat.zero)",
        "(2^53 - 1) mod 2 = 1 — the ODDNESS test the ties-to-even rule turns on, at the full \
         significand width. Through ir_nat_rem this is a 2^52 quotient, i.e. unreachable. \
         DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_mulb_w",
        "def ir_nat_mulb_w : Eq Nat (ir_nat_mulb 12 34) (ir_nat_mul 12 34) := Eq.refl Nat 408",
        "*** DIFFERENTIAL: shift-and-add multiplication IS ir_nat_mul. *** Affordable on the \
         reference side because 34 repeated additions is 34 steps. DerivedProved, zero \
         axiom_deps.",
    ),
    (
        "ir_nat_mulb_zero_w",
        "def ir_nat_mulb_zero_w : Eq Nat (ir_nat_mulb 9007199254740991 Nat.zero) (ir_nat_mul 9007199254740991 Nat.zero) := Eq.refl Nat Nat.zero",
        "Multiplication by zero, both sides. The driver's ascent stops immediately because \
         `hi = 0 < 1`, so the accumulator is never touched. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_mulb_wide_w",
        "def ir_nat_mulb_wide_w : Eq Nat (ir_nat_mulb 9007199254740991 9007199254740991) 81129638414606663681390495662081 := Eq.refl Nat 81129638414606663681390495662081",
        "THE PRODUCT A BINARY64 MULTIPLY NEEDS: (2^53 - 1)^2, a 106-bit exact integer, in 0.042 s. \
         `ir_nat_mul` on the same operands is 2^53 additions and has no reference column here for \
         the same reason ir_nat_divmod_one_w has none. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_mulb_roundtrip_w",
        "def ir_nat_mulb_roundtrip_w : Eq Nat (ir_dm_quot (ir_nat_divmod 81129638414606663681390495662081 9007199254740991)) 9007199254740991 := Eq.refl Nat 9007199254740991",
        "…and dividing that 106-bit product back by one factor returns the other, so the \
         multiplication and the division are checked AGAINST EACH OTHER at the width the float \
         path actually uses, where neither has a reference column. DerivedProved, zero \
         axiom_deps.",
    ),
    (
        "ir_nat_shl_divpow2_w",
        "def ir_nat_shl_divpow2_w : Eq Nat (ir_dm_quot (ir_nat_divpow2 (ir_nat_shl 9007199254740991 2045) 2045)) 9007199254740991 := Eq.refl Nat 9007199254740991",
        "THE ALIGNMENT ROUND TRIP AT THE EXTREME: shift a 53-bit significand up by 2045 — the \
         maximum binary64 alignment distance, a 2098-bit value — and drop the 2045 bits again. \
         The shift and the drop are inverse, kernel-executed. Through `ir_nat_mul` and \
         `ir_nat_div` neither half exists. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_min_w",
        "def ir_nat_min_w : Eq Nat (ir_nat_min 53 1022) 53 := Eq.refl Nat 53",
        "min. DerivedProved, zero axiom_deps.",
    ),
    (
        "ir_nat_max_w",
        "def ir_nat_max_w : Eq Nat (ir_nat_max 53 1022) 1022 := Eq.refl Nat 1022",
        "max. DerivedProved, zero axiom_deps.",
    ),
];

#[cfg(test)]
mod tests {
    use super::BITS_WITNESSES;

    /// **Zero accelerated constants.** The whole reason the finite fragment was
    /// refused in the first place is that buying it with the kernel-native
    /// `Nat.div` / `Nat.mod` / `Nat.beq` would add constants whose declared
    /// bodies the kernel never consults — speed bought with trust. This test is
    /// that refusal, mechanised over every source this module registers.
    #[test]
    fn test_no_accelerated_constant_is_added() {
        const BANNED: &[&str] = &[
            "Nat.div",
            "Nat.mod",
            "Nat.mul",
            "Nat.pow",
            "Nat.beq",
            "Nat.ble",
            "Nat.blt",
            "Nat.shiftLeft",
            "Nat.shiftRight",
            "Nat.land",
            "Nat.lor",
            "Nat.xor",
        ];
        for (name, src, _) in BITS_WITNESSES {
            for bad in BANNED {
                assert!(
                    !src.contains(bad),
                    "{name} names the accelerated constant {bad}: the kernel reduces it natively \
                     and never consults its declared body, so relying on it is speed bought with \
                     trust. accelerated_constants_added must stay 0."
                );
            }
        }
    }

    /// The differential ladder must actually compare against the REFERENCE
    /// definitions, not only against literals.
    #[test]
    fn test_the_ladder_compares_against_the_reference_definitions() {
        let joined: String = BITS_WITNESSES.iter().map(|(_, s, _)| *s).collect();
        for reference in ["ir_nat_div ", "ir_nat_rem ", "ir_nat_mul "] {
            assert!(
                joined.contains(reference),
                "the differential ladder must run {reference} on the reference side somewhere, or \
                 it is a ladder of self-consistency and nothing else"
            );
        }
    }

    #[test]
    fn test_sources_balanced_ascii() {
        for (name, src, _) in BITS_WITNESSES {
            let mut d: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => d += 1,
                    ')' => d -= 1,
                    _ => {}
                }
                assert!(d >= 0, "unbalanced parens in {name}");
            }
            assert_eq!(d, 0, "unbalanced parens in {name}");
            assert!(src.is_ascii(), "spec sources must be ASCII: {name}");
        }
    }
}
