// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — **binary64 arithmetic on the FINITE fragment**: correctly-rounded
//! `fadd`, `fsub` and `fmul` at round-to-nearest-even, over the 53-bit
//! significand, with exact subnormals, exact signed zeros and exact overflow to
//! infinity.
//!
//! This is the build item [`super::eval_ir_float`]'s refusal named and
//! `designs/2026-08-16-float-finite-fragment-scope.md` measured as reachable.
//! Read that module's doc first: it states which fragment of IEEE 754 binary64
//! the CLASSIFICATION layer decides, and this module is what fills the
//! `fin_`/`fin_` cell that layer left as a tagged refusal for addition and
//! multiplication.
//!
//! **`fdiv` on the finite fragment is still REFUSED, and §5 below is its
//! measurement.** Three of the four operators, not four.
//!
//! ## The number, and the two shifts
//!
//! A finite binary64 pattern `n` denotes `sig(n) * 2^(sc(n) - 1074)`:
//!
//! ```text
//! ebits = mag(n) / 2^52          frac = mag(n) mod 2^52
//! ebits = 0  ->  sig = frac              sc = 0            (subnormal, and zero)
//! ebits > 0  ->  sig = 2^52 + frac       sc = ebits - 1    (normal)
//! ```
//!
//! Every operation below produces an EXACT integer `m` and an EXACT integer
//! scale `B` with the value `m * 2^(B - 1074)`, and then hands both to ONE
//! shared rounding tail. `B` can be negative — a product of two subnormals is
//! below `2^-1074` before rounding — so it arrives as a pair `(bp, bn)` with
//! `B = bp - bn`, which is how a `Nat`-only substrate carries a signed number
//! without an `Int`.
//!
//! The tail's whole content is **one shift distance**:
//!
//! ```text
//! t = max(bitlen(m) - 53, -B)
//! ```
//!
//! `t > 0` is a right shift of `t` places (round there); `t < 0` is a left
//! shift of `-t` places (renormalise, exact). Split over `Nat`:
//!
//! ```text
//! ir_f64_rsh = max(bitlen m - 53, bn - bp)      ir_f64_lsh = min(53 - bitlen m, bp - bn)
//! ```
//!
//! and **at most one of the two is non-zero**, which is what lets the same
//! three declarations serve normal results, subnormal results, renormalising
//! cancellation and underflow without a case split. `bitlen m` is read ONCE,
//! off the unnormalised `m`: after a renormalising left shift there is nothing
//! left to drop, so a second scan is not merely expensive, it is redundant.
//!
//! ## Rounding, and why the tie test is exact
//!
//! `q0 = m' / 2^t` and `r0 = m' mod 2^t` come out of one `ir_nat_divpow2` pass.
//! Round-to-nearest-even is then three comparisons on integers, with no
//! division and no fraction:
//!
//! ```text
//! 2*r0 > 2^t                     -> up
//! 2*r0 = 2^t  and  q0 is odd     -> up      (the TIE, resolved to even)
//! otherwise                      -> down
//! ```
//!
//! `m` is the exact value for `fadd`/`fsub` (an integer sum or difference of
//! aligned significands) and for `fmul` (an exact 106-bit product), so `r0` is
//! the exact residue and the tie test is exact rather than approximate. That is
//! the property `fdiv` does not have, and §5 is what it costs.
//!
//! A carry out of the rounding — `q0 + 1 = 2^53` — is absorbed by resetting the
//! significand to `2^52` and bumping the scale, which is exactly right because
//! `2^53 * 2^s = 2^52 * 2^(s+1)`.
//!
//! ## What decides the boundaries
//!
//! * **subnormal**: `qf < 2^52` after rounding. It can only happen when the
//!   left shift was clamped by the scale budget, so the scale is already zero,
//!   and the magnitude bits ARE `qf` — the encoding with `ebits = 0`.
//! * **overflow**: the biased exponent reaches 2047, which is the infinity
//!   encoding. The result is `+-inf` at the result's sign, per IEEE 754 §7.4
//!   under roundTiesToEven.
//! * **the sign**: `fmul` is the XOR. `fadd` is the operand sign when the signs
//!   agree, the larger operand's sign when they do not, and `+0` when the sum
//!   is exactly zero (§6.3), which is the one addition rule that is about the
//!   sign of a zero rather than about magnitudes.
//!
//! ## What this does NOT claim
//!
//! **These definitions are not PROVED to be IEEE 754.** They agree with
//! hardware `f64` on every witness `add_eval_ir_float_fin_witnesses` registers
//! — each an `Eq.refl` the kernel had to compute, each expected value taken
//! from `f64` itself in `test_the_answering_witnesses_agree_with_real_f64` —
//! and on 1,001,024 random and hand-picked pairs in an independent
//! transcription of the same formulas (a MODEL result, recorded in the landing
//! design note, not a kernel result). That is the same evidential bar
//! [`super::eval_ir_float`] sets for the classified tables and it is not a
//! proof. It rests in turn on [`super::eval_ir_bits`], whose own agreement
//! theorems are `ir_nat_dbl_eq` plus an executed differential ladder, with the
//! restoring-division and shift-and-add agreement theorems named as unattempted
//! there.
//!
//! ## What it COSTS, measured — and the sign is POSITIVE
//!
//! This is a cost, not a saving, and `test_the_measured_cost_has_a_positive_sign`
//! pins that as data so nobody quotes the wrong direction. The `ir_wrap`
//! literal-folding lemma was **-3.5%** because it removed work from
//! declarations that already existed; the `ltb`/`eqb` folding lemmas were
//! **+2.4%** because they bought declarations that did not. This lane is the
//! second kind: 99 new declarations, of which 51 are kernel-EXECUTED witnesses.
//!
//! **Direct measurement, the exact landed set.** Every one of the 99 sources,
//! elaborated and kernel-checked one at a time against ONE
//! `CoreSpecBundle::EvalIr` build of the tree WITHOUT them — so the number is
//! the added work and nothing else. 99/99, first attempt:
//!
//! ```text
//! the 17 definitions (both modules)                         0.199 s
//! the 22 differential witnesses (super::eval_ir_bits)       3.005 s
//! the 30 finite-fragment witnesses                          4.658 s
//!                                                    total  7.862 s
//! ```
//!
//! Four rows are two thirds of it, and each is an extreme on purpose:
//! `ir_f64_w_fin_max_alignment` (max normal + min subnormal, a 2098-bit exact
//! sum) **1.615 s**, `ir_nat_bitlen_wide_w` **1.328 s**,
//! `ir_nat_shl_divpow2_w` **0.759 s**, `ir_nat_divpow2_ref_w` **0.558 s** —
//! the last being expensive because its REFERENCE side is `ir_nat_div` at a
//! quotient of 2047.
//!
//! **Whole-build measurement**, two paired rounds, both sides launched together
//! so they share one window at matched concurrency (this box was carrying other
//! lanes throughout, at load ~13, which is why the absolute build is ~1775 s
//! rather than the ~215 s the folding lane recorded on a quiet one — the
//! PAIRING is what makes the delta readable, not the absolute):
//!
//! ```text
//!            before (Specification::new() / user CPU)   after
//! round 1     1780.0 s / 1770.45 s                      1790.6 s / 1781.21 s
//! round 2     1769.0 s / 1749.20 s                      1782.0 s / 1773.11 s
//! round 3     1782.2 s / 1768.25 s                      1801.6 s / 1798.39 s
//! ```
//!
//! **+10.6, +13.0 and +19.4 s of `Specification::new()` wall and +10.8, +23.9
//! and +30.1 s of user CPU — all three rounds agreeing in SIGN, mean +14.3 s
//! wall on a ~1777 s build, i.e. +0.8%.** The spread is wide because the box
//! was shared; the sign is not in doubt and the direct measurement above is the
//! tight number. Against the 7.862 s of new declarations, the residual is the
//! two declarations this lane CHANGED rather than added — the `fin`/`fin` cells
//! of `ir_f64_add_at` and `ir_f64_mul_at`, which used to be `IROption.none` and
//! are now applications the kernel carries through every downstream stuck term.
//! That is the same effect the folding lane traced to `add_eval_ir_contains`,
//! at a quarter the size.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// 2^52 — the hidden bit, and the lower bound of a normal significand.
const P52: &str = "4503599627370496";
/// 2^53 — one past the largest representable significand.
const P53: &str = "9007199254740992";

impl Specification {
    /// Register the finite binary64 fragment: field extraction, the shared
    /// rounding tail, addition and multiplication.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_float_fin(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_float_fields()?;
        self.add_eval_ir_float_round()?;
        self.add_eval_ir_float_ops_fin()
    }

    /// Significand and scale, read off a bit pattern.
    fn add_eval_ir_float_fields(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def ir_f64_ebits (n : Nat) : Nat := ir_dm_quot (ir_nat_divpow2 (ir_f64_mag n) 52)",
            "The biased exponent field: the magnitude bits divided by 2^52. Through \
             ir_nat_divpow2 rather than ir_nat_div, and the difference is 0.011 s against \
             0.428 s on the same 9.2e18 dividend — see super::eval_ir_bits. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_frac (n : Nat) : Nat := ir_dm_rem (ir_nat_divpow2 (ir_f64_mag n) 52)",
            "The trailing significand field: the remainder of the same ONE division pass that \
             produced the exponent. That is the reason IRDivMod carries both — computing them \
             from two separate calls would run the restoring loop twice. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def ir_f64_sig (n : Nat) : Nat := Bool.rec (fun (_ : Bool) => Nat) \
                 (Nat.add {P52} (ir_f64_frac n)) (ir_f64_frac n) \
                 (ir_nat_iszero (ir_f64_ebits n))"
            ),
            "THE SIGNIFICAND AS AN INTEGER, with the hidden bit made explicit. Bool.rec's minor \
             order is (false, true), so the FIRST minor is the ebits-non-zero case — a normal \
             number, whose leading 1 is implied by the encoding and has to be restored — and the \
             second is the subnormal case, where there is no hidden bit and the field IS the \
             significand. Getting these two the wrong way round is the classic binary64 bug and \
             it is why the subnormal witnesses below are not optional. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_sc (n : Nat) : Nat := Bool.rec (fun (_ : Bool) => Nat) ",
                "(Nat.pred (ir_f64_ebits n)) Nat.zero (ir_nat_iszero (ir_f64_ebits n))",
            ),
            "The scale: the exponent of the significand's LOW bit, offset so that the value is \
             `sig * 2^(sc - 1074)` uniformly. A normal has `sc = ebits - 1`; a subnormal has \
             `sc = 0`, which is the same scale as `ebits = 1` — that shared scale is exactly why \
             `largest subnormal + smallest subnormal` becomes the smallest NORMAL with no special \
             case anywhere in this module. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }

    /// The shared rounding tail: one shift distance, one division pass,
    /// round-to-nearest-even, then the subnormal and overflow boundaries.
    fn add_eval_ir_float_round(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            concat!(
                "def ir_f64_rsh (m : Nat) (bp : Nat) (bn : Nat) : Nat := ",
                "ir_nat_max (Nat.sub (ir_nat_bitlen m) 53) (Nat.sub bn bp)",
            ),
            "*** THE RIGHT SHIFT — how many bits of m are dropped. *** The larger of two demands: \
             `bitlen m - 53` is what it takes to FIT in 53 bits, and `bn - bp` is what it takes \
             to reach scale zero when the exact value sits below 2^-1074. Taking the max is the \
             whole subnormal story: below the smallest normal the grid stops getting finer, so \
             more bits go. Both subtractions are truncating, so each demand contributes only when \
             it is positive. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_lsh (m : Nat) (bp : Nat) (bn : Nat) : Nat := ",
                "ir_nat_min (Nat.sub 53 (ir_nat_bitlen m)) (Nat.sub bp bn)",
            ),
            "*** THE LEFT SHIFT — renormalisation after cancellation. *** The smaller of what \
             normalising WANTS (`53 - bitlen m` places) and what the scale budget ALLOWS \
             (`bp - bn` places, since the scale may not go below zero). When the budget binds, \
             the result is subnormal; when it does not, the result is normal. \
             \n\nAT MOST ONE OF ir_f64_rsh AND ir_f64_lsh IS NON-ZERO, by construction: if the \
             left shift is positive then `bitlen m < 53` and `bp > bn`, so both of the right \
             shift's demands truncate to zero. That is what lets one tail serve every case. \
             \n\nAnd `ir_nat_bitlen m` is read off the UNNORMALISED m in both, never off the \
             shifted value. A scan inside another scan's argument was measured at over 4 minutes \
             where the single-scan spelling is 0.072 s, and it is not merely expensive — after \
             renormalising there is nothing left to drop, so the second scan would be redundant \
             as well. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_mnorm (m : Nat) (bp : Nat) (bn : Nat) : Nat := ",
                "ir_nat_shl m (ir_f64_lsh m bp bn)",
            ),
            "m renormalised. Exact: a left shift loses nothing. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_dmv (m : Nat) (bp : Nat) (bn : Nat) : IRDivMod := ",
                "ir_nat_divpow2 (ir_f64_mnorm m bp bn) (ir_f64_rsh m bp bn)",
            ),
            "The truncated significand and everything the rounding decision needs, from ONE \
             restoring pass. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_q0 (m : Nat) (bp : Nat) (bn : Nat) : Nat := ir_dm_quot (ir_f64_dmv m bp bn)",
            "The truncated significand, before rounding. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_r0 (m : Nat) (bp : Nat) (bn : Nat) : Nat := ir_dm_rem (ir_f64_dmv m bp bn)",
            "The bits that were dropped, as an integer. EXACT — that is what makes the tie test \
             below a decision and not an estimate. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_odd (q : Nat) : Bool := ",
                "ir_nat_pos (ir_dm_rem (ir_nat_divpow2 q (Nat.succ Nat.zero)))",
            ),
            "Is the truncated significand odd? The `EVEN` in roundTiesToEven, and at a 53-bit \
             significand it is a `q mod 2` the reference `ir_nat_rem` cannot compute — its \
             quotient would be 2^52. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_rup (m : Nat) (bp : Nat) (bn : Nat) : Bool := ",
                "Bool.or ",
                "(ir_nat_ltb (ir_nat_pow2 (ir_f64_rsh m bp bn)) ",
                "(ir_nat_dbl (ir_f64_r0 m bp bn))) ",
                "(Bool.and ",
                "(ir_nat_eqb (ir_nat_dbl (ir_f64_r0 m bp bn)) ",
                "(ir_nat_pow2 (ir_f64_rsh m bp bn))) ",
                "(ir_f64_odd (ir_f64_q0 m bp bn)))",
            ),
            "*** ROUND-TO-NEAREST-EVEN, as three integer comparisons. *** `2*r0 > 2^t` is strictly \
             more than half an ulp, so round up. `2*r0 = 2^t` is EXACTLY half — the tie — and \
             §4.3.1 sends it to the even neighbour, i.e. up exactly when the truncated \
             significand is odd. Everything else rounds down. \n\nNo fraction, no division, no \
             epsilon: r0 is the exact residue, so the middle case is an equality of integers and \
             the tie is DECIDED rather than approached. Doubling through ir_nat_dbl rather than \
             `Nat.add r0 r0` because r0 is a redex here and that spelling is the measured cost \
             bomb. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_q (m : Nat) (bp : Nat) (bn : Nat) : Nat := ",
                "Bool.rec (fun (_ : Bool) => Nat) (ir_f64_q0 m bp bn) ",
                "(Nat.succ (ir_f64_q0 m bp bn)) (ir_f64_rup m bp bn)",
            ),
            "The rounded significand. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def ir_f64_carry (m : Nat) (bp : Nat) (bn : Nat) : Bool := \
                 Bool.not (ir_nat_ltb (ir_f64_q m bp bn) {P53})"
            ),
            "Did rounding UP carry out of the significand? Only one value can: 2^53 - 1 rounding \
             to 2^53. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def ir_f64_qf (m : Nat) (bp : Nat) (bn : Nat) : Nat := \
                 Bool.rec (fun (_ : Bool) => Nat) (ir_f64_q m bp bn) {P52} \
                 (ir_f64_carry m bp bn)"
            ),
            "The final significand: the rounded one, or 2^52 when it carried. Exact rather than \
             an approximation of a shift, because 2^53 * 2^s IS 2^52 * 2^(s+1) — the carry is a \
             change of representation, not a loss. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_sfx (m : Nat) (bp : Nat) (bn : Nat) : Nat := ",
                "Bool.rec (fun (_ : Bool) => Nat) (ir_f64_rsh m bp bn) ",
                "(Nat.succ (ir_f64_rsh m bp bn)) (ir_f64_carry m bp bn)",
            ),
            "The right shift the exponent must account for, bumped by one when the significand \
             carried. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_ex (m : Nat) (bp : Nat) (bn : Nat) : Nat := ",
                "Nat.succ (Nat.sub (Nat.add bp (ir_f64_sfx m bp bn)) ",
                "(Nat.add bn (ir_f64_lsh m bp bn)))",
            ),
            "THE BIASED EXPONENT of a normal result: the scale is `B + t` — the incoming scale \
             plus the net shift — and the encoding adds one, because a normal's scale is \
             `ebits - 1`. The Nat.sub is exact rather than truncating on every input this is \
             read at: the right shift is at least `bn - bp` by construction, so the difference is \
             never negative. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def ir_f64_magn (m : Nat) (bp : Nat) (bn : Nat) : Nat := \
                 Nat.add (ir_nat_shl (ir_f64_ex m bp bn) 52) \
                 (Nat.sub (ir_f64_qf m bp bn) {P52})"
            ),
            "The magnitude bits of a NORMAL result: the biased exponent in the high field and the \
             significand with its hidden bit removed in the low one. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            &format!(
                "def ir_f64_magout (m : Nat) (bp : Nat) (bn : Nat) : Nat := \
                 Bool.rec (fun (_ : Bool) => Nat) \
                 (Bool.rec (fun (_ : Bool) => Nat) (ir_f64_magn m bp bn) ir_f64_inf_mag \
                 (Bool.not (ir_nat_ltb (ir_f64_ex m bp bn) 2047))) \
                 (ir_f64_qf m bp bn) \
                 (ir_nat_ltb (ir_f64_qf m bp bn) {P52})"
            ),
            "*** THE MAGNITUDE, WITH BOTH BOUNDARIES. *** Bool.rec minor order is (false, true). \
             The SECOND minor is the subnormal exit — `qf < 2^52` — where the magnitude bits ARE \
             the significand, because a subnormal encodes `ebits = 0` and no hidden bit; and it \
             is reachable only when the left shift was clamped, which forces the scale to zero, \
             so no exponent has to be written. The FIRST minor is a normal result, and inside it \
             the biased exponent reaching 2047 is OVERFLOW: 2047 is the infinity encoding, so \
             IEEE 754 §7.4 under roundTiesToEven returns the infinity itself. Underflow needs no \
             arm at all — it is `qf = 0` in the subnormal exit, which is the zero encoding. \
             DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }

    /// Kernel-EXECUTED witnesses, every expected value taken from hardware
    /// `f64`.
    ///
    /// Registered from `add_eval_ir_ops` alongside the classified fragment's.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_float_fin_witnesses(&mut self) -> Result<(), SpecError> {
        for (_, src, note) in super::eval_ir_float_fin_witnesses::FIN_WITNESSES {
            self.add_recursive_def(src, note)?;
        }
        Ok(())
    }
}
