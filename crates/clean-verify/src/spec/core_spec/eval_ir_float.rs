// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — **the binary64 float value domain** (the build item the eighth
//! chain needed).
//!
//! Until 2026-08-15 every float-domain operation in this semantics was the
//! single verdict `ir_float_fault` — `IROutcome.unmodelled IRFault.float_domain`
//! — and [`super::eval_ir_state`]'s exclusion table said so in one line:
//! *"`BinOp` fadd/fsub/fmul/fdiv/frem/fmin/fmax | unmodelled | `float_domain`"*.
//! `IRScalar.float_ n` and `IRConst.float_ n` carried a bit pattern that could
//! be BUILT and COMPARED for syntactic identity and never computed with.
//!
//! This module is the smallest honest thing that is not that. It gives
//! `fadd`/`fsub`/`fmul`/`fdiv` a REAL evaluation case on the fragment of
//! IEEE 754-2019 binary64 where the answer is **determined by the operands'
//! CLASSIFICATION alone** — NaN / infinity / signed zero / finite-nonzero — and
//! keeps the tagged `unmodelled` verdict everywhere else. Nothing that used to
//! evaluate changed; strictly more evaluates than before.
//!
//! ## What is modelled, and why exactly this much
//!
//! IEEE 754 §6.1–6.3 fixes these results with no reference to rounding:
//!
//! | case | result | why it is exact |
//! |---|---|---|
//! | `x / 0` (x finite non-zero or ∞) | ±∞, sign = `sign x XOR sign 0` | §7.3 divideByZero; the value is an exact infinity |
//! | `0 / x`, `x / ∞` | ±0, sign = XOR | exact zero |
//! | `∞ / x` (x finite) | ±∞ | exact |
//! | `∞ × x`, `x × ∞` (x ≠ 0) | ±∞ | exact |
//! | `0 × x`, `x × 0` (x ≠ ∞) | ±0 | exact |
//! | `∞ + x`, `x + ∞` (x finite or same-signed ∞) | that ∞ | exact |
//! | `x ± 0`, `0 ± x` (x finite) | `x` / `∓x` | adding a zero is exact |
//! | `(+0) + (+0)`, `(±0) + (∓0)` | `+0` | §6.3: roundTiesToEven gives `+0` |
//! | `(-0) + (-0)` | `-0` | §6.3, the one signed-zero exception |
//! | `x + (-x)`, x finite | `+0` | §6.3: an exact zero sum is `+0` under roundTiesToEven |
//!
//! and since 2026-08-16 the FINITE fragment as well, correctly rounded, for
//! three of the four operators — `fadd`, `fsub` and `fmul` at
//! roundTiesToEven over the 53-bit significand, with exact subnormals, exact
//! signed zeros and exact overflow to infinity. That arithmetic lives in
//! [`super::eval_ir_float_fin`] and this module's tables dispatch into it.
//!
//! It still **refuses** the rest:
//!
//! | case | verdict | why it CANNOT be modelled here |
//! |---|---|---|
//! | either operand NaN | `unmodelled float_domain` | the result is *a* quiet NaN; its PAYLOAD is implementation-defined (§6.2.3 "should"), so no bit pattern is determined |
//! | `∞ - ∞`, `0 × ∞`, `0 / 0`, `∞ / ∞` | `unmodelled float_domain` | invalid operation → a NaN, same payload problem |
//! | **finite ÷ finite** | `unmodelled float_domain` | the ONE arithmetic refusal left, and the only one that is about COST rather than about the standard — see below |
//! | any width but 64 | `unmodelled float_domain` | binary32/binary16 are different formats; `IRTy.float_ w` carries `w` and this module decides only `w = 64` |
//!
//! ## The wall that was a cost law — retired 2026-08-16 for `+`, `-`, `×`
//!
//! Until 2026-08-16 `finite ⊕ finite` was refused for all four operators on a
//! measured cost argument, and **the argument was right about two definitions
//! and wrong about the substrate**. `ir_nat_div` is a fuel loop linear in the
//! QUOTIENT, so rounding a 53-bit significand was `2^52` iterations — measured
//! at 3,600 steps/s, about **39,700 years**. `ir_nat_mul` is linear in its
//! second operand, so a 2045-place alignment was `2^2045` additions.
//!
//! Neither is the only way to write those operations out of `Nat.add` and
//! `Nat.sub`, which is all the substrate is allowed. A restoring bit-at-a-time
//! division and a doubling ladder are linear in the BIT LENGTH:
//! [`super::eval_ir_bits`] is that rewrite and [`super::eval_ir_float_fin`] is
//! the correctly-rounded arithmetic built on it. The same quotient the fuel
//! loop could not reach costs **0.040 s**, and `1.0 + 1.0` — registered here
//! for a year as the embarrassing refusal — is **0.089 s**.
//!
//! **`fdiv` on the finite fragment is STILL refused**, and now for a reason
//! specific to it rather than a blanket one: a quotient is not an exact
//! integer, so its significand has to be produced by a second division at
//! guard precision, and the shared rounding tail names its significand
//! argument enough times that an input costing 0.13 s does not terminate in
//! 250 s where a literal of the same value costs 0.101 s. Addition's exact
//! sum (0.001 s) and multiplication's exact product (0.042 s) do not have that
//! problem. [`super::eval_ir_float_fin`] carries the measurement and names the
//! build item.
//!
//! **The trust rule is unchanged and was re-checked, not assumed.** Nothing in
//! this lane uses `Nat.div`, `Nat.mod`, `Nat.mul`, `Nat.pow`, `Nat.beq`,
//! `Nat.ble`, `Nat.shiftLeft` or `Nat.shiftRight` — every one of which the
//! kernel reduces natively without consulting its declared body, i.e. would buy
//! speed with trust. Everything is `Nat.add` / `Nat.sub` / `Nat.succ` /
//! `Nat.rec` / `Bool.rec`, exactly as before, so the substrate gains **no new
//! accelerated constant and no new trust**; `eval_ir_bits`'s
//! `test_no_accelerated_constant_is_added` is that refusal mechanised.
//!
//! So the classification layer is decided with `ir_nat_ltb` and `ir_nat_eqb` — since
//! 2026-08-16 both are native `BigNat` subtractions plus one iota step rather than
//! paired unary walks, and `ir_nat_ltb_walk_eq` / `ir_nat_eqb_walk_eq` prove each
//! is the same predicate as the walk it replaced. That is what makes a witness at
//! `0x7FF0000000000000` — a dividend of 9.2e18 — cost milliseconds instead of
//! being unreachable by a factor of a billion.
//!
//! ## What this does NOT claim
//!
//! `ir_f64_div` is **not** proved to be `f64::div`. It is a definition that
//! agrees with IEEE 754 on the classified fragment BY CONSTRUCTION AND BY
//! READING, and returns `IROption.none` — which the machine turns into a tagged
//! `unmodelled` outcome, never a value — everywhere else. The eighth chain's
//! refinement theorem says the emitted body computes THIS function; the gap
//! between this function and the hardware's `fdiv` is stated here and closed
//! nowhere. That gap is exactly the same shape as the one
//! [`super::eval_ir_valid_char`] states for `env_is_valid_char` (a `u64`-level
//! specification, not the Unicode predicate) — it is not new debt, but it is
//! larger, because a float format has more structure than an interval test.
//!
//! Junk bit patterns are fail-closed rather than special-cased: any `n` at or
//! above `2^64` has magnitude at or above `2^63`, which is greater than
//! `0x7FF0000000000000`, so it classifies `nan_` and every operation on it is
//! `unmodelled`.
//!
//! ## What guards the tables
//!
//! **Completeness of each 4x4 table is enforced by ELABORATION**: every table is
//! two nested `IRF64Class.rec` applications, and a recursor application needs
//! exactly four minors of exactly the right type, so a missing arm does not
//! type-check. What elaboration cannot catch is arms in the WRONG ORDER — that
//! computes a different function and checks fine — so every rule below has a
//! kernel-EXECUTED witness (`add_eval_ir_float_witnesses`), and
//! `test_the_answering_witnesses_agree_with_real_f64` checks each answering
//! witness against `f64` itself rather than against a second reading of the
//! standard.
//!
//! `DerivedProved`, empty axiom closures.

use crate::spec::error::SpecError;
use crate::spec::Specification;

impl Specification {
    /// Register the binary64 value domain: the classification and the four
    /// classified operation tables, then the machine-facing combinators from
    /// [`super::eval_ir_float_ops`].
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check.
    pub(super) fn add_eval_ir_float(&mut self) -> Result<(), SpecError> {
        self.add_eval_ir_float_classify()?;
        // The FINITE fragment, before the tables that dispatch into it.
        self.add_eval_ir_float_fin()?;
        self.add_eval_ir_float_fin_witnesses()?;
        self.add_eval_ir_float_tables()?;
        self.add_eval_ir_float_machine()
    }

    /// Bit-pattern classification: sign, magnitude, and the four-way class.
    fn add_eval_ir_float_classify(&mut self) -> Result<(), SpecError> {
        self.add_inductive(
            r"inductive IRF64Class : Type
| nan_ : IRF64Class
| inf_ : IRF64Class
| zero_ : IRF64Class
| fin_ : IRF64Class",
            "The four IEEE 754 binary64 classes this semantics distinguishes, in the order every \
             dispatch below uses them. Subnormals are NOT a fifth class: they are `fin_`, because \
             every rule stated in this module treats a subnormal exactly as it treats a normal \
             number (a zero added to a subnormal is exact; a subnormal divided by an infinity is \
             an exact zero). Splitting them out would add a case that no rule reads. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_sign_bit : Nat := 9223372036854775808",
            "2^63 — the binary64 sign bit, and therefore also the bit pattern of `-0.0`. Written \
             as the literal rather than as `ir_nat_pow2 ir_d64`'s neighbour so the kernel folds \
             it natively on BigNat; a unary numeral of this magnitude does not exist. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_inf_mag : Nat := 9218868437227405312",
            "0x7FF0000000000000 — the magnitude bits of an infinity: exponent all ones, \
             significand zero. It is the exact boundary of the class table: a magnitude BELOW it \
             is finite, EQUAL to it is an infinity, ABOVE it is a NaN. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_is_neg (n : Nat) : Bool := Bool.not (ir_nat_ltb n ir_f64_sign_bit)",
            "The sign bit, decided as `NOT (n < 2^63)`. Through ir_nat_ltb rather than \
             ir_nat_ltb, and that is the whole reason this module is affordable: the paired unary \
             walk would peel 9.2e18 Nat.rec layers to decide the sign of an infinity, while the \
             subtraction test is one native BigNat subtract and one iota step. \
             ir_nat_ltb_walk_eq proves the two are the same predicate. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_mag (n : Nat) : Nat := ",
                "Bool.rec (fun (_ : Bool) => Nat) n (Nat.sub n ir_f64_sign_bit) ",
                "(ir_f64_is_neg n)",
            ),
            "The magnitude bits: n with the sign bit cleared. Bool.rec's minor order is \
             (false, true), so the FIRST minor is the non-negative case. `Nat.sub` is exact here \
             rather than truncating, because the true branch is reached only when n >= 2^63. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_class (n : Nat) : IRF64Class := ",
                "Bool.rec (fun (_ : Bool) => IRF64Class) ",
                "(Bool.rec (fun (_ : Bool) => IRF64Class) ",
                "(Bool.rec (fun (_ : Bool) => IRF64Class) ",
                "IRF64Class.fin_ IRF64Class.zero_ ",
                "(Bool.not (ir_nat_pos (ir_f64_mag n)))) ",
                "IRF64Class.inf_ ",
                "(Bool.not (ir_nat_ltb (ir_f64_mag n) ir_f64_inf_mag))) ",
                "IRF64Class.nan_ ",
                "(ir_nat_ltb ir_f64_inf_mag (ir_f64_mag n))",
            ),
            "Classify a bit pattern. Three nested Bool.rec, tested in the order that makes each \
             test correct given the ones outside it: NaN first (magnitude ABOVE the infinity \
             boundary), then infinity (NOT below the boundary — which is equality only because \
             the NaN test already failed), then zero (magnitude has no successor), else finite. \
             \n\nJunk is fail-closed by construction: any n at or above 2^64 has magnitude at or \
             above 2^63 > 0x7FF0000000000000, so it classifies nan_ and every operation on it is \
             the tagged unmodelled outcome. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_pack (s : Bool) (m : Nat) : Nat := ",
                "Bool.rec (fun (_ : Bool) => Nat) m (Nat.add ir_f64_sign_bit m) s",
            ),
            "Rebuild a bit pattern from a sign and a magnitude. The sign bit is the FIRST operand \
             of Nat.add deliberately: Nat.add recurses on its second argument, so `pack true 0` \
             settles in one iota step instead of walking 2^63 of them, and on two closed literals \
             the kernel folds it natively anyway. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_negate (n : Nat) : Nat := ir_f64_pack (Bool.not (ir_f64_is_neg n)) (ir_f64_mag n)",
            "Flip the sign bit. This is IEEE 754 negate (§5.5.1), a bit operation that is exact \
             on every input including zeros, infinities and NaNs — which is what licenses \
             ir_f64_sub being ir_f64_add of the negation. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_xsign (a : Nat) (b : Nat) : Bool := ir_bool_xor (ir_f64_is_neg a) (ir_f64_is_neg b)",
            "The sign of a product or quotient: the XOR of the operand signs (IEEE 754 §6.3). \
             Exact for EVERY pair of operands, including the ones whose magnitude this module \
             refuses to compute — which is why multiplication and division can decide their \
             result sign in every arm they answer at all. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_ssign (a : Nat) (b : Nat) : Bool := Bool.not (ir_f64_xsign a b)",
            "Do the two operands have the SAME sign? Used by addition's infinity arm, where \
             `(+inf) + (+inf)` is `+inf` and `(+inf) + (-inf)` is an invalid operation. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_mag_eqb (a : Nat) (b : Nat) : Bool := ir_nat_eqb (ir_f64_mag a) (ir_f64_mag b)",
            "Equal magnitudes. Straight through `ir_nat_eqb`, which since 2026-08-16 is itself \
             `a - b = 0 AND b - a = 0` on two native BigNat subtractions rather than a paired \
             unary walk (`ir_nat_eqb_walk_eq` proves the two are the same predicate). The first \
             draft of this module hand-rolled the subtraction test here, because at the time \
             `ir_nat_eqb` still walked; the folding lane landed underneath it and the hand-rolled \
             version became a worse spelling of the same thing. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_opposite (a : Nat) (b : Nat) : Bool := Bool.and (ir_f64_xsign a b) (ir_f64_mag_eqb a b)",
            "Is b exactly -a? Opposite signs and equal magnitudes. This is the ONLY finite+finite \
             addition whose result IEEE 754 fixes without rounding: the sum is exactly zero, and \
             §6.3 says an exact zero sum is +0 under roundTiesToEven. Everything else in that arm \
             is refused. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }

    /// The four classified operation tables.
    fn add_eval_ir_float_tables(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            "def ir_f64_qinf (a : Nat) (b : Nat) : Nat := ir_f64_pack (ir_f64_xsign a b) ir_f64_inf_mag",
            "The infinity a multiplicative operation on a and b produces, at the XOR sign. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_qzero (a : Nat) (b : Nat) : Nat := ir_f64_pack (ir_f64_xsign a b) Nat.zero",
            "The zero a multiplicative operation on a and b produces, at the XOR sign. It is a \
             SIGNED zero and the sign is observable: -0.0 and +0.0 are different bit patterns, \
             different values of Eq Float (Clean's own Float.decEq is structural on the bit \
             pattern for exactly this reason), and 1.0/(+0.0) and 1.0/(-0.0) are different \
             infinities. DerivedProved, zero axiom_deps.",
        )?;

        // ── division ───────────────────────────────────────────────────
        // The table is complete over the 4x4 class product. Only the
        // finite/finite cell needs rounding; two more are invalid operations
        // whose NaN payload is not determined.
        self.add_recursive_def(
            concat!(
                "def ir_f64_div_at (a : Nat) (b : Nat) (ca : IRF64Class) (cb : IRF64Class) : IROption Nat := ",
                "IRF64Class.rec (fun (_ : IRF64Class) => IRF64Class -> IROption Nat) ",
                "(fun (_ : IRF64Class) => IROption.none Nat) ",
                "(IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(IROption.none Nat) (IROption.none Nat) ",
                "(IROption.some Nat (ir_f64_qinf a b)) ",
                "(IROption.some Nat (ir_f64_qinf a b))) ",
                "(IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(IROption.none Nat) ",
                "(IROption.some Nat (ir_f64_qzero a b)) ",
                "(IROption.none Nat) ",
                "(IROption.some Nat (ir_f64_qzero a b))) ",
                "(IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(IROption.none Nat) ",
                "(IROption.some Nat (ir_f64_qzero a b)) ",
                "(IROption.some Nat (ir_f64_qinf a b)) ",
                "(IROption.none Nat)) ",
                "ca cb",
            ),
            "*** IEEE 754 binary64 DIVISION on the classified fragment. *** Two nested \
             IRF64Class.rec — the multi-scrutinee dispatch idiom, since this surface syntax has \
             single-scrutinee match only — over the full 4x4 class product, in constructor order \
             (nan_, inf_, zero_, fin_). \n\nAnswered: inf/0 and inf/fin and fin/0 are an infinity \
             at the XOR sign; 0/inf and 0/fin and fin/inf are a zero at the XOR sign. Refused: \
             anything with a NaN operand, 0/0 and inf/inf (invalid operations whose NaN payload \
             is implementation-defined), and fin/fin (rounding). \n\nDIVISION BY ZERO IS THE ROW \
             THAT MAKES THIS NOT A RENAME OF THE INTEGER LANE: ir_div_checked answers \
             `IROutcome.ub IRFault.div_zero` on a zero divisor, and this answers a signed \
             infinity. Same shape, different semantics, and the difference is the point of \
             modelling floats at all. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_div (a : Nat) (b : Nat) : IROption Nat := ir_f64_div_at a b (ir_f64_class a) (ir_f64_class b)",
            "Division, with the classification applied. The TABLE and its APPLICATION are separate \
             declarations on purpose, and it is not cosmetic: a theorem that knows the class of an \
             operand — `ir_fd_machine_sound_divzero`, which is the eighth chain's A5 reaching past \
             the machine's answer onto its ARGUMENTS — rewrites `ir_f64_class b` to \
             `IRF64Class.zero_` with Eq.cong and then the table COMPUTES. With the two fused into \
             one definition there is no subterm to rewrite, and the only way to reach the same \
             conclusion is a four-by-four case analysis on classes that are already known. \
             DerivedProved, zero axiom_deps.",
        )?;

        // ── multiplication ─────────────────────────────────────────────
        self.add_recursive_def(
            concat!(
                "def ir_f64_mul_at (a : Nat) (b : Nat) (ca : IRF64Class) (cb : IRF64Class) : IROption Nat := ",
                "IRF64Class.rec (fun (_ : IRF64Class) => IRF64Class -> IROption Nat) ",
                "(fun (_ : IRF64Class) => IROption.none Nat) ",
                "(IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(IROption.none Nat) ",
                "(IROption.some Nat (ir_f64_qinf a b)) ",
                "(IROption.none Nat) ",
                "(IROption.some Nat (ir_f64_qinf a b))) ",
                "(IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(IROption.none Nat) (IROption.none Nat) ",
                "(IROption.some Nat (ir_f64_qzero a b)) ",
                "(IROption.some Nat (ir_f64_qzero a b))) ",
                "(IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(IROption.none Nat) ",
                "(IROption.some Nat (ir_f64_qinf a b)) ",
                "(IROption.some Nat (ir_f64_qzero a b)) ",
                "(IROption.some Nat (ir_f64_mul_fin a b))) ",
                "ca cb",
            ),
            "IEEE 754 binary64 MULTIPLICATION on the classified fragment. inf*inf and inf*fin are \
             an infinity at the XOR sign; 0*0 and 0*fin are a zero at the XOR sign. Refused: any \
             NaN operand and 0*inf in either order (invalid operation, so a NaN with an \
             implementation-defined payload). \n\nfin*fin ANSWERS as of 2026-08-16: \
             ir_f64_mul_fin computes the exact 106-bit product of the two significands and rounds \
             it to nearest-even, with gradual underflow and overflow to an infinity, through the \
             same tail addition uses (super::eval_ir_float_fin). It was refused until then \
             because the product needed `ir_nat_mul`, which is linear in its second operand. \
             DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_mul (a : Nat) (b : Nat) : IROption Nat := ir_f64_mul_at a b (ir_f64_class a) (ir_f64_class b)",
            "Multiplication, with the classification applied. Same table/application split as \
             division, for the same reason. DerivedProved, zero axiom_deps.",
        )?;

        // ── addition ───────────────────────────────────────────────────
        self.add_recursive_def(
            concat!(
                "def ir_f64_add_at (a : Nat) (b : Nat) (ca : IRF64Class) (cb : IRF64Class) : IROption Nat := ",
                "IRF64Class.rec (fun (_ : IRF64Class) => IRF64Class -> IROption Nat) ",
                "(fun (_ : IRF64Class) => IROption.none Nat) ",
                "(IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(IROption.none Nat) ",
                "(Bool.rec (fun (_ : Bool) => IROption Nat) (IROption.none Nat) ",
                "(IROption.some Nat a) (ir_f64_ssign a b)) ",
                "(IROption.some Nat a) (IROption.some Nat a)) ",
                "(IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(IROption.none Nat) (IROption.some Nat b) ",
                "(IROption.some Nat (ir_f64_pack ",
                "(Bool.and (ir_f64_is_neg a) (ir_f64_is_neg b)) Nat.zero)) ",
                "(IROption.some Nat b)) ",
                "(IRF64Class.rec (fun (_ : IRF64Class) => IROption Nat) ",
                "(IROption.none Nat) (IROption.some Nat b) (IROption.some Nat a) ",
                "(Bool.rec (fun (_ : Bool) => IROption Nat) ",
                "(IROption.some Nat (ir_f64_add_fin a b)) ",
                "(IROption.some Nat Nat.zero) (ir_f64_opposite a b))) ",
                "ca cb",
            ),
            "IEEE 754 binary64 ADDITION on the classified fragment, and the arm that carries the \
             signed-zero rule everyone gets wrong. \n\ninf+inf is that infinity when the signs \
             AGREE and refused when they do not (`inf - inf` is an invalid operation). inf+fin \
             and inf+0 are the infinity; 0+inf and fin+inf are the infinity too. 0+fin is the \
             finite operand and fin+0 is the finite operand — adding a zero is exact, including \
             to a subnormal. \n\n0+0 IS NOT ALWAYS +0: §6.3 makes the sum of two zeros of the \
             SAME sign that sign, and of opposite signs +0 under roundTiesToEven. That is exactly \
             `Bool.and (is_neg a) (is_neg b)`, and it is the reason the zero arm is not the \
             constant Nat.zero. \n\nfin+fin ANSWERS as of 2026-08-16, and the arm still tests \
             ir_f64_opposite FIRST. That is deliberate rather than vestigial: `b = -a` is the one \
             finite sum §6.3 fixes with NO rounding, so keeping it as an exact classified rule \
             keeps an exact rule exact — and it is two comparisons where the pipeline is a \
             2098-bit alignment. ir_f64_add_fin agrees with it on that input, and \
             ir_f64_w_fin_exact_zero_sum is the executed proof that the redundant path does not \
             disagree. Everything else in the arm is ir_f64_add_fin: the exact aligned sum, \
             rounded to nearest-even (super::eval_ir_float_fin). DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_add (a : Nat) (b : Nat) : IROption Nat := ir_f64_add_at a b (ir_f64_class a) (ir_f64_class b)",
            "Addition, with the classification applied. Same table/application split as division \
             and multiplication. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            "def ir_f64_sub (a : Nat) (b : Nat) : IROption Nat := ir_f64_add a (ir_f64_negate b)",
            "IEEE 754 binary64 SUBTRACTION: `a - b` is `a + (-b)`, exactly, in every case \
             including the zeros and the NaNs (§5.4.1 defines subtraction that way, and negation \
             is an exact bit operation). Stated as the composition rather than as a fourth copied \
             table, so the two cannot drift: writing it out would put the signed-zero rule in two \
             places, and `(-0) - (+0) = -0` while `(-0) + (+0) = +0` is precisely where a copied \
             table goes wrong. DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }
}
