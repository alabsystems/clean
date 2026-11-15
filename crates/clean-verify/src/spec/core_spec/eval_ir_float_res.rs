// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — **the float RESIDUE band** (the wave `evalir_w4.PENDING.md`
//! delta 5 named): real semantics for the seven residue operators the plan
//! marked as answerable — `fneg`/`fabs` (sign-bit operations, exact on every
//! genuine bit pattern), `fmin`/`fmax` (the NaN-ignoring minimum/maximum on
//! the classified fragment), `ffloor`/`fceil`/`ftrunc` (exponent-guided
//! integer rounding, exact on every non-NaN pattern) — and the machine-facing
//! unary float dispatcher they ride. The DATED REFUSALS the same plan names
//! (`frem`, `fsqrt`, the eight fp casts, `fdiv`-finite) stay refused, but as
//! kernel-witnessed UNIVERSAL statements
//! ([`super::eval_ir_float_res_witnesses`]), never silence.
//!
//! Plan: `docs/analysis/evalir-completion-plan-2026-08-24.md` §3.3 + §5 W4
//! ("Plus the cheap unops (`fneg`/`fabs` sign-bit ops; `ffloor`/`fceil`/
//! `ftrunc` exponent-guided…), `fmin`/`fmax`. Dated refusals (not silent):
//! `frem`, `fsqrt`, …"). Authored 2026-08-25.
//!
//! ## Ground truth (trust-ir pinned rev `a4e81b6`)
//!
//! `eval_float_unop` (`interpret.rs:5964-6010`, `F64` arm): `FNeg` is `-x`,
//! `FAbs` is `x.abs()`, `FFloor`/`FCeil`/`FTrunc` are `x.floor()`/`.ceil()`/
//! `.trunc()` — "IEEE 754 required/recommended operations with exact or
//! correctly-rounded results". `eval_float_binop` (`interpret.rs:5919-5950`,
//! `F64` arm): `FMin` is `lhs.min(rhs)`, `FMax` is `lhs.max(rhs)` — Rust's
//! IEEE 754-2008 minNum/maxNum discipline: one NaN operand is IGNORED and the
//! other operand returned.
//!
//! ## What answers, and why exactly this much
//!
//! * **`fneg`/`fabs` are TOTAL on genuine 64-bit patterns, NaNs included.**
//!   IEEE 754 §5.5.1 makes negate/abs quiet BIT operations — copy the
//!   pattern, set the sign bit — so unlike arithmetic there is no NaN-payload
//!   freedom: the result pattern is fully determined, payload preserved. The
//!   one refusal is a JUNK carrier (`n >= 2^64`, [`ir_f64_is_pattern`]):
//!   junk has no sign bit to flip, and "clearing" bit 63 of a carrier that
//!   also has bit 64 set would mint a valid-looking pattern out of garbage.
//!   (Contrast the classification's junk posture: comparisons ANSWER on junk
//!   because they return a Bool; these return a PATTERN, so junk must not
//!   escape as one.)
//! * **`fmin`/`fmax` answer wherever minNum/maxNum is DETERMINED.** One NaN
//!   operand → the other operand, exactly (Rust doc: "If one of the
//!   arguments is NaN, then the other argument is returned"). Ordered
//!   operands → the sign-magnitude value order picks one operand's pattern.
//!   Two refusals, both because the standard/implementation does NOT fix the
//!   result: BOTH operands NaN (the result is *a* NaN, payload
//!   implementation-defined — the arithmetic lane's rule), and the
//!   OPPOSITE-SIGNED ZERO pair (LLVM's `llvm.minnum`: "min(+0.0, -0.0) may
//!   return either" — an answer here could be refuted by a conforming host).
//!   Junk classifies `nan_` and is handled by the NaN rows; it is never
//!   returned (the non-NaN operand is).
//! * **`ffloor`/`fceil`/`ftrunc` are exact on every non-NaN pattern.** An
//!   infinity or a zero rounds to itself (sign preserved — `ceil(-0.5)` is
//!   `-0.0`, and the small-magnitude arm keeps the operand's sign). A finite
//!   with biased exponent `e >= 1075` is already an integer. Otherwise the
//!   fractional bits are the low `k = 1075 - e` bits of the magnitude:
//!   clearing them truncates, and adding `2^k` to the cleared pattern is the
//!   next integer — the magnitude increment carries through the significand
//!   into the exponent field exactly because binary64 magnitudes are ordered
//!   bit patterns ([`super::eval_ir_fcmp`]'s order argument, reused as an
//!   INCREMENT argument). A NaN is refused: the rounded result would be *a*
//!   NaN whose payload the host libm chooses (§6.2.3 "should"), the exact
//!   refusal `fadd` already carries. The arithmetic is `ir_nat_divpow2` /
//!   `ir_nat_shl` on the bit-length-linear substrate
//!   ([`super::eval_ir_bits`]) — milliseconds, no new accelerated constant,
//!   no new trust.
//!
//! ## The one duplicated definition, and its pin
//!
//! `fmin`/`fmax` need the non-NaN VALUE ORDER, which is [`ir_f64_ltb_pre`]
//! here — the same sign-magnitude order the comparison band defines as
//! `ir_f64_ltb` ([`super::eval_ir_fcmp`]), spelled IDENTICALLY. It exists
//! twice because registration order forces it: `ir_binop_eval`'s `fmin`/
//! `fmax` arms elaborate in `add_eval_ir_arith`, which runs BEFORE
//! `add_eval_ir_compare` registers the comparison band, and moving
//! `ir_f64_ltb` earlier would change the registration position of a
//! pre-existing def (the inertness discipline every wave's PENDING file
//! states). The duplication is pinned, not trusted: `ir_f64_ltb_pre_agrees`
//! (in the witnesses stage, registered after both) is a kernel-checked
//! `Eq.refl` at UNIVERSALLY QUANTIFIED operands — the two definitions are
//! definitionally equal or every spec build fails — and this file's Rust test
//! cross-checks the order against host `f64` directly.
//!
//! ## Model status — inherited, restated, not strengthened
//!
//! Exactly [`super::eval_ir_fcmp`]'s: agreement with IEEE 754 is by
//! construction and by reading; the executed witnesses are cross-checked
//! against host `f64` in the witnesses file's Rust tests; the gap between
//! these definitions and the hardware is stated and closed nowhere.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// The float residue band: `fneg`/`fabs`, `fmin`/`fmax`,
    /// `ffloor`/`fceil`/`ftrunc`, and the typed unary float dispatcher.
    ///
    /// Registered at the END of `add_eval_ir_float` (after
    /// `add_eval_ir_float_machine`), so every pre-existing float def keeps
    /// its registration position and `add_eval_ir_arith` — which runs next
    /// and whose `ir_unop_eval`/`ir_binop_eval` arms dispatch into these
    /// names — finds them declared. Reuses the classification
    /// (`ir_f64_class`, `ir_f64_mag`, `ir_f64_is_neg`, `ir_f64_pack`,
    /// `ir_f64_negate`, `ir_f64_xsign`), the machine facings
    /// (`ir_as_float`, `ir_ty_float_width`, `ir_float_fault`,
    /// `ir_float_type_fault`, `ir_f64_result`), the finite fragment's
    /// exponent view (`ir_f64_ebits`), and the bits substrate
    /// (`ir_nat_divpow2`, `ir_dm_quot`, `ir_dm_rem`, `ir_nat_shl`,
    /// `ir_nat_pos`, `ir_nat_ltb`, `ir_nat_leb`, `ir_nat_eqb`,
    /// `ir_nat_iszero`).
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_float_res(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_float_res_sign()?;
        self.add_eval_ir_float_res_minmax()?;
        self.add_eval_ir_float_res_round()?;
        self.add_eval_ir_float_res_machine()
    }

    /// The sign-bit operations: `fneg`, `fabs`, and the genuine-pattern gate.
    fn add_eval_ir_float_res_sign(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def ir_f64_junk_bound : Nat := 18446744073709551616",
            "2^64 — the first Nat that is NOT a binary64 bit pattern. Written as the literal \
             (the ir_f64_sign_bit precedent: the kernel folds it natively on BigNat). The \
             boundary of ir_f64_is_pattern, and the exact carrier the junk witnesses probe. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_is_pattern (n : Nat) : Bool := ir_nat_ltb n ir_f64_junk_bound",
            "Is this Nat a genuine 64-bit pattern (n < 2^64)? The sign-bit operations gate on \
             it: fneg/fabs are exact BIT operations on every real pattern including NaNs, but \
             a junk carrier has no bit 63 to speak of — flipping it would mint a valid-looking \
             pattern out of garbage, so junk is the tagged unmodelled outcome instead. One \
             folded ir_nat_ltb, milliseconds. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_fneg (n : Nat) : IROption Nat := ",
                "@Bool.rec (fun (_ : Bool) => IROption Nat) ",
                "(@IROption.none Nat) ",
                "(@IROption.some Nat (ir_f64_negate n)) ",
                "(ir_f64_is_pattern n)",
            ),
            "IEEE 754 negate (5.5.1) on every genuine pattern: flip the sign bit, preserve \
             everything else — NaN payloads included, which is why this is TOTAL where fadd \
             refuses NaNs: negate is a quiet bit operation with no payload freedom. trust-ir \
             a4e81b6 eval_float_unop FNeg is host `-x`, the same bit flip. Junk refuses \
             (ir_f64_is_pattern). Bool.rec minor order is (false, true). DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_fabs (n : Nat) : IROption Nat := ",
                "@Bool.rec (fun (_ : Bool) => IROption Nat) ",
                "(@IROption.none Nat) ",
                "(@IROption.some Nat (ir_f64_mag n)) ",
                "(ir_f64_is_pattern n)",
            ),
            "IEEE 754 abs (5.5.1) on every genuine pattern: clear the sign bit — which is \
             exactly ir_f64_mag, the magnitude view the whole classification is built on. \
             Payload-preserving on NaNs for the same reason fneg is. trust-ir a4e81b6 \
             eval_float_unop FAbs is host `x.abs()`, the same bit clear. DerivedProved, zero \
             axiom_deps.",
        )?;

        Ok(())
    }

    /// The NaN-ignoring minimum/maximum on the classified fragment.
    fn add_eval_ir_float_res_minmax(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            concat!(
                "def ir_f64_ltb_pre (a : Nat) (b : Nat) : Bool := ",
                "@Bool.rec (fun (_ : Bool) => Bool) ",
                "(@Bool.rec (fun (_ : Bool) => Bool) ",
                "(ir_nat_ltb (ir_f64_mag a) (ir_f64_mag b)) ",
                "Bool.false ",
                "(ir_f64_is_neg b)) ",
                "(@Bool.rec (fun (_ : Bool) => Bool) ",
                "(Bool.not (Bool.and (ir_nat_iszero (ir_f64_mag a)) (ir_nat_iszero (ir_f64_mag b)))) ",
                "(ir_nat_ltb (ir_f64_mag b) (ir_f64_mag a)) ",
                "(ir_f64_is_neg b)) ",
                "(ir_f64_is_neg a)",
            ),
            "The binary64 VALUE order on non-NaN patterns — ir_f64_ltb's body, spelled \
             IDENTICALLY (see super::eval_ir_fcmp for the order's design prose). It exists \
             here a second time ONLY because registration order forces it: ir_binop_eval's \
             fmin/fmax arms elaborate before the comparison band registers, and moving \
             ir_f64_ltb would change a pre-existing def's registration position. The \
             duplication is pinned by ir_f64_ltb_pre_agrees — a kernel-checked Eq.refl at \
             universally quantified operands, so the two spellings are definitionally equal \
             or every spec build fails. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_mm_pick_min (a : Nat) (b : Nat) : IROption Nat := ",
                "@IROption.some Nat (@Bool.rec (fun (_ : Bool) => Nat) b a (ir_f64_ltb_pre a b))",
            ),
            "The ordered minimum: a when a < b, else b — always ONE OF THE OPERANDS, exactly \
             as minNum returns an operand. On equal non-NaN values outside the zero pair the \
             two operands are the same pattern, so the else-branch's b is not a choice. \
             Bool.rec minor order is (false, true). DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_mm_pick_max (a : Nat) (b : Nat) : IROption Nat := ",
                "@IROption.some Nat (@Bool.rec (fun (_ : Bool) => Nat) a b (ir_f64_ltb_pre a b))",
            ),
            "The ordered maximum: b when a < b, else a. The mirror of ir_f64_mm_pick_min. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_mm_zero (a : Nat) (b : Nat) : IROption Nat := ",
                "@Bool.rec (fun (_ : Bool) => IROption Nat) ",
                "(@IROption.some Nat a) ",
                "(@IROption.none Nat) ",
                "(ir_f64_xsign a b)",
            ),
            "The zero/zero cell of BOTH min and max tables: two zeros of the SAME sign are the \
             same bit pattern (answer it); the OPPOSITE-signed pair is REFUSED, because \
             llvm.minnum/maxnum may return either zero ('If the operands compare equal, \
             returns either one of the operands') — an answer here could be refuted by a \
             conforming host, and a tagged refusal cannot. This is the one cell where minimum \
             and maximum are indistinguishable to this model, which is why one definition \
             serves both tables. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_fmin_at (a : Nat) (b : Nat) (ca : IRF64Class) (cb : IRF64Class) : IROption Nat := ",
                "@IRF64Class.rec (fun (_ : IRF64Class) => IRF64Class -> IROption Nat) ",
                "(@IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(@IROption.none Nat) ",
                "(@IROption.some Nat b) ",
                "(@IROption.some Nat b) ",
                "(@IROption.some Nat b)) ",
                "(@IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(@IROption.some Nat a) ",
                "(ir_f64_mm_pick_min a b) ",
                "(ir_f64_mm_pick_min a b) ",
                "(ir_f64_mm_pick_min a b)) ",
                "(@IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(@IROption.some Nat a) ",
                "(ir_f64_mm_pick_min a b) ",
                "(ir_f64_mm_zero a b) ",
                "(ir_f64_mm_pick_min a b)) ",
                "(@IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(@IROption.some Nat a) ",
                "(ir_f64_mm_pick_min a b) ",
                "(ir_f64_mm_pick_min a b) ",
                "(ir_f64_mm_pick_min a b)) ",
                "ca cb",
            ),
            "*** IEEE 754-2008 minNum on the classified fragment *** — trust-ir a4e81b6 \
             eval_float_binop FMin, host `lhs.min(rhs)`. Two nested IRF64Class.rec over the \
             4x4 class product in constructor order (nan_, inf_, zero_, fin_), the \
             ir_f64_div_at idiom. NaN/NaN refuses (the result NaN's payload is \
             implementation-defined); NaN/x and x/NaN return THE OTHER OPERAND exactly ('the \
             other argument is returned' — Rust f64::min's documented minNum discipline), \
             which also gives junk carriers (class nan_) the right behavior: the genuine \
             operand is returned and junk never escapes as a value. zero/zero is \
             ir_f64_mm_zero (opposite signs refused); every other ordered cell is the value \
             order's pick. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_fmin (a : Nat) (b : Nat) : IROption Nat := ",
                "ir_f64_fmin_at a b (ir_f64_class a) (ir_f64_class b)",
            ),
            "Minimum, with the classification applied. Table/application split as in \
             ir_f64_div, for the same congruence-rewriting reason. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_fmax_at (a : Nat) (b : Nat) (ca : IRF64Class) (cb : IRF64Class) : IROption Nat := ",
                "@IRF64Class.rec (fun (_ : IRF64Class) => IRF64Class -> IROption Nat) ",
                "(@IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(@IROption.none Nat) ",
                "(@IROption.some Nat b) ",
                "(@IROption.some Nat b) ",
                "(@IROption.some Nat b)) ",
                "(@IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(@IROption.some Nat a) ",
                "(ir_f64_mm_pick_max a b) ",
                "(ir_f64_mm_pick_max a b) ",
                "(ir_f64_mm_pick_max a b)) ",
                "(@IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(@IROption.some Nat a) ",
                "(ir_f64_mm_pick_max a b) ",
                "(ir_f64_mm_zero a b) ",
                "(ir_f64_mm_pick_max a b)) ",
                "(@IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(@IROption.some Nat a) ",
                "(ir_f64_mm_pick_max a b) ",
                "(ir_f64_mm_pick_max a b) ",
                "(ir_f64_mm_pick_max a b)) ",
                "ca cb",
            ),
            "IEEE 754-2008 maxNum on the classified fragment — trust-ir a4e81b6 \
             eval_float_binop FMax, host `lhs.max(rhs)`. The exact mirror of ir_f64_fmin_at: \
             same NaN-ignoring rows, same refused NaN/NaN and opposite-zero cells, the value \
             order's pick flipped. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_fmax (a : Nat) (b : Nat) : IROption Nat := ",
                "ir_f64_fmax_at a b (ir_f64_class a) (ir_f64_class b)",
            ),
            "Maximum, with the classification applied. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }

    /// Exponent-guided integer rounding: `ffloor`, `fceil`, `ftrunc`.
    fn add_eval_ir_float_res_round(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def ir_f64_one_mag : Nat := 4607182418800017408",
            "The magnitude bits of 1.0 (0x3FF0000000000000) — the pattern the small-magnitude \
             rounding arm produces when it rounds away from zero (floor of a negative \
             fraction, ceil of a positive one). A literal for the same folding reason as \
             ir_f64_sign_bit. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_rnd_frac (away : Bool) (s : Bool) (q : Nat) (r : Nat) (k : Nat) : Nat := ",
                "@Bool.rec (fun (_ : Bool) => Nat) ",
                "(ir_f64_pack s (ir_nat_shl q k)) ",
                "(ir_f64_pack s (ir_nat_shl (Nat.succ q) k)) ",
                "(Bool.and away (ir_nat_pos r))",
            ),
            "The mid-range rounding step: q and r are the magnitude's quotient and remainder \
             by 2^k (k = the count of fractional bits), so `shl q k` is the magnitude with \
             its fraction CLEARED — truncation — and `shl (q+1) k` is the NEXT integer's \
             magnitude: the +1 carries from the significand into the exponent field exactly \
             because binary64 magnitudes are ordered bit patterns (ceil of 1.999... reaches \
             2.0 through this carry, and the executed witness pins it). Rounds away from \
             zero only when `away` AND the fraction is nonzero — an exact integer is \
             returned unchanged by BOTH branches' q-side. Bool.rec minor order is \
             (false, true). DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_rnd_small (away : Bool) (s : Bool) : Nat := ",
                "@Bool.rec (fun (_ : Bool) => Nat) ",
                "(ir_f64_pack s Nat.zero) ",
                "(ir_f64_pack s ir_f64_one_mag) ",
                "away",
            ),
            "The |x| < 1 arm (biased exponent <= 1022, subnormals included, x nonzero): \
             toward zero the result is the SIGNED zero — the operand's sign survives, which \
             is how ceil(-0.5) lands on -0.0 (IEEE 754 roundToIntegralTowardPositive keeps \
             the sign of a negative operand on a zero result) — and away from zero it is \
             +/-1.0. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_rnd_fin (away : Bool) (n : Nat) : Nat := ",
                "@Bool.rec (fun (_ : Bool) => Nat) ",
                "(@Bool.rec (fun (_ : Bool) => Nat) ",
                "(ir_f64_rnd_frac away (ir_f64_is_neg n) ",
                "(ir_dm_quot (ir_nat_divpow2 (ir_f64_mag n) (Nat.sub 1075 (ir_f64_ebits n)))) ",
                "(ir_dm_rem (ir_nat_divpow2 (ir_f64_mag n) (Nat.sub 1075 (ir_f64_ebits n)))) ",
                "(Nat.sub 1075 (ir_f64_ebits n))) ",
                "n ",
                "(ir_nat_leb 1075 (ir_f64_ebits n))) ",
                "(ir_f64_rnd_small away (ir_f64_is_neg n)) ",
                "(ir_nat_ltb (ir_f64_ebits n) 1023)",
            ),
            "Round a FINITE NONZERO pattern to an integer, toward zero or away per `away`. \
             Three exponent ranges, decided by folded comparisons on ir_f64_ebits (the \
             biased exponent, mag div 2^52 — the finite fragment's own view): e <= 1022 is \
             |x| < 1 (ir_f64_rnd_small); e >= 1075 means the ulp is at least 1, the value \
             is already an integer, and the pattern is returned UNCHANGED; between them \
             k = 1075 - e in [1, 52] fractional bits ride ir_nat_divpow2 — one restoring \
             bit-at-a-time division by 2^k on the O(bit-length) substrate, milliseconds, no \
             new accelerated constant. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_rnd (awayneg : Bool) (awaypos : Bool) (n : Nat) : IROption Nat := ",
                "@IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(@IROption.none Nat) ",
                "(@IROption.some Nat n) ",
                "(@IROption.some Nat n) ",
                "(@IROption.some Nat (ir_f64_rnd_fin ",
                "(@Bool.rec (fun (_ : Bool) => Bool) awaypos awayneg (ir_f64_is_neg n)) n)) ",
                "(ir_f64_class n)",
            ),
            "The shared roundToIntegral table over the classification, parameterized by which \
             SIGN rounds away from zero — floor rounds negatives away (toward -inf), ceil \
             rounds positives away (toward +inf), trunc neither. nan_ REFUSES: the result \
             would be *a* NaN whose payload the host libm chooses — the same \
             implementation-defined-payload rule every arithmetic arm carries — and junk \
             (class nan_) refuses with it. An infinity or a zero is its own rounding, sign \
             preserved. Minor order is the constructor order (nan_, inf_, zero_, fin_). \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_ffloor (n : Nat) : IROption Nat := ir_f64_rnd Bool.true Bool.false n",
            "IEEE 754 roundToIntegralTowardNegative on the classified fragment: negatives \
             round away from zero, positives toward it. trust-ir a4e81b6 eval_float_unop \
             FFloor, host `x.floor()`. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_fceil (n : Nat) : IROption Nat := ir_f64_rnd Bool.false Bool.true n",
            "IEEE 754 roundToIntegralTowardPositive: positives round away from zero, \
             negatives toward it (which is where ceil(-0.5) = -0.0 comes from). trust-ir \
             a4e81b6 eval_float_unop FCeil, host `x.ceil()`. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_ftrunc (n : Nat) : IROption Nat := ir_f64_rnd Bool.false Bool.false n",
            "IEEE 754 roundToIntegralTowardZero: neither sign rounds away. trust-ir a4e81b6 \
             eval_float_unop FTrunc, host `x.trunc()`. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }

    /// The machine-facing unary float dispatcher.
    fn add_eval_ir_float_res_machine(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            concat!(
                "def ir_float1 (f : Nat -> IRStepResult) (a : IRScalar) : IRStepResult := ",
                "@IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "ir_float_type_fault ",
                "(fun (x : Nat) => f x) (ir_as_float a)",
            ),
            "Apply a unary float operation to a bit pattern, faulting type_error not_float \
             unless the operand is a float. The unary mirror of ir_float2, with the same \
             fail-closed integer posture (ir_as_float's doc). DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_float_unop (f : Nat -> IROption Nat) (t : IRTy) ",
                "(a : IRScalar) : IRStepResult := ",
                "@IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "ir_float_type_fault ",
                "(fun (w : Nat) => @Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "ir_float_fault ",
                "(ir_float1 (fun (x : Nat) => ir_f64_result (f x)) a) ",
                "(ir_nat_eqb w 64)) ",
                "(ir_ty_float_width t)",
            ),
            "*** THE TYPED FLOAT UNARY DISPATCHER *** — ir_float_binop's exact shape with one \
             operand: a non-float type is type_error not_float; a float type at any width \
             but 64 is the tagged unmodelled outcome (the pinned interpreter DOES answer f32 \
             unops — eval_float_unop's F32 arm — so this is a recorded fragment boundary, \
             kernel-witnessed by ir_fneg_f32_unmodelled and its siblings, never a wrong \
             answer); at width 64 the operand is coerced and the classified table decides. \
             The instruction's IRTy is semantic input, exactly as in the binary dispatcher. \
             DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }
}
