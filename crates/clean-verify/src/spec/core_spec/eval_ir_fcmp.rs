// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — **the binary64 float COMPARISON semantics** (plan W4): the 12
//! `IRFCmpOp` arms, real, on the classified fragment.
//!
//! Until 2026-08-25 every arm of `ir_fcmp_eval` was the single verdict
//! `ir_float_fault`, and the refusal rationale — *"an FCmp semantics would be
//! modelling with no artifact to be about"* (`eval_ir_syntax.rs`, the
//! `IRFCmpOp` doc) — predates B3-SELECT. Under the ratified mandate EvalIR is
//! THE definitional semantics of the trust-ir waist
//! (`designs/2026-08-23-b3-select-semantics-decision.md`), so its subject is
//! every constructed-`Inst` module, not only the bodies clean-kernel emits;
//! the plan states this retirement explicitly
//! (`docs/analysis/evalir-completion-plan-2026-08-24.md` §0). This module is
//! the last tagged constructor-level arm becoming real semantics: after it,
//! ZERO `ir_exec` arms are the unmodelled outcome (the residue is
//! operator/fragment-level and stays listed in `eval_ir_state.rs`).
//!
//! ## Ground truth (trust-ir pinned rev `a4e81b6`)
//!
//! `Inst::FCmp { op, ty, lhs, rhs }` executes as `eval_fcmp`
//! (`interpret.rs:651-657`, `:3925-3931` scalar path): both operands must BE
//! the instruction type, their float bits are extracted, and `eval_float_fcmp`
//! (`:6013-6035`) dispatches on the TYPE — `F32`/`F64` compute, `F16` is
//! unsupported, a non-float type is a type error. The comparison itself is
//! `eval_fcmp_f64` (`:6056-6072`):
//!
//! ```text
//! let unordered = lhs.is_nan() || rhs.is_nan();
//! OEq => !unordered && lhs == rhs,   UEq => unordered || lhs == rhs,
//! OLt => !unordered && lhs <  rhs,   ULt => unordered || lhs <  rhs,   ...
//! ```
//!
//! [`ir_fcmp_bool`] is that function arm for arm: the ordered predicates
//! conjoin `NOT unordered`, the unordered ones disjoin `unordered`, `gt`/`ge`
//! are `lt`/`le` with the operands exchanged (exact on non-NaN reals), and
//! `ne` is the negation of `eq` (exact on non-NaN reals; on a NaN both halves
//! are decided by the unordered term alone, matching `!=`'s IEEE behavior).
//!
//! ## Why comparison is TOTAL where arithmetic is not
//!
//! Arithmetic on a NaN operand is refused in this value domain because the
//! result is *a* NaN whose PAYLOAD is implementation-defined
//! (`eval_ir_float.rs`). A comparison returns a Bool — there is no payload to
//! invent — and IEEE 754 §5.11 fixes every predicate on every pair of
//! operands, NaNs included. So on `binary64` this fragment answers on ANY
//! classified operands, which is exactly the plan's W4 observation ("this
//! fragment is total for fcmp, unlike arithmetic").
//!
//! The finite/ordering substrate is the sign-magnitude order the format was
//! designed to have: for non-NaN patterns, `a < b` is decided by the sign
//! bits and the MAGNITUDE order of the remaining 63 bits (`ir_f64_mag`),
//! because binary64 magnitudes are lexicographic in (exponent, significand)
//! and the infinity pattern sits above every finite one. The two zeros are the
//! single exception (`+0 = -0` across different bit patterns) and get their
//! own conjunct. All of it folds: the deciders are `ir_nat_ltb` /
//! `ir_nat_eqb` (native `BigNat` subtractions + one iota step,
//! `ir_nat_ltb_walk_eq` / `ir_nat_eqb_walk_eq` pin them to the paired unary
//! walks) over `ir_f64_mag`'s single exact `Nat.sub` — the measured
//! folded-path cost class (`docs/CRYSTAL_STATUS.md` §"the folding lane":
//! 0.003 s per classification where the walk was 9.2e18 layers). No new
//! accelerated constant and no new trust enters the substrate.
//!
//! ## What is refused, exactly, and why
//!
//! | case | verdict | why |
//! |---|---|---|
//! | non-float `t` | `type_error not_float` | ill-formed IR; the interpreter's `expect_ty`/type-error class |
//! | non-float operand under `float_ 64` | `type_error not_float` | same class (`ir_float2`'s coercion, the `ir_float_binop` discipline) |
//! | `float_ w`, `w ≠ 64` | `unmodelled float_domain` | binary32/binary16 are different formats with different NaN boundaries; this module decides only binary64. NOTE the pinned interpreter DOES execute `f32` compares (`eval_fcmp_f32`, `interpret.rs:6038-6054`) — a fragment boundary of this model, tagged fail-closed, never a wrong answer; recorded in `data/evalir_w4.PENDING.md` |
//!
//! Junk bit patterns (any `n ≥ 2^64`) classify `nan_` by construction
//! (`ir_f64_class`'s doc), so under a comparison they ANSWER as a NaN would —
//! ordered predicates false, unordered true — rather than faulting. That is
//! the classification's junk posture carried through unchanged, and it is
//! pinned by executed witnesses below rather than argued.
//!
//! ## Model status — inherited, restated, not strengthened
//!
//! The `ir_f64_*` lanes are checked by kernel-EXECUTED witnesses (38 across
//! the arithmetic chains, 0 discrepancies) and are explicitly **not proved to
//! be hardware arithmetic** (`eval_ir_float.rs` "What this does NOT claim").
//! These comparisons inherit exactly that status: [`ir_fcmp_bool`] agrees
//! with IEEE 754 §5.11 by construction and by reading, its witnesses are
//! executed by the kernel and cross-checked against host `f64` in this file's
//! Rust tests, and the gap between this definition and the hardware's `fcmp`
//! is stated here and closed nowhere.
//!
//! One adequacy-grid consequence, recorded for W5: the §4(c) sketch listed
//! `fcmp.t` among the retained-INERT operands. As of this wave `t` is
//! DISPATCHED (the width gate above consults it, exactly like `binop.t`'s
//! float arms), so that grid row is dead — the type operand is semantic
//! input, not inert cargo, and its coverage is the battery's, not an
//! irrelevance theorem's.
//!
//! `DerivedProved`, empty axiom closures — every witness is an `Eq.refl` the
//! kernel discharges by computing.

use crate::spec::error::SpecError;
use crate::spec::Specification;

// ── kernel-EXECUTED witnesses, per rule the arms encode ────────────────────
//
// The bit patterns, once (the same table as eval_ir_float_ops.rs):
//   1.0   = 0x3FF0000000000000 = 4607182418800017408
//   2.0   = 0x4000000000000000 = 4611686018427387904
//   -1.0  = 0xBFF0000000000000 = 13830554455654793216
//   -2.0  = 0xC000000000000000 = 13835058055282163712
//   +0.0  = 0
//   -0.0  = 0x8000000000000000 = 9223372036854775808
//   +inf  = 0x7FF0000000000000 = 9218868437227405312
//   -inf  = 0xFFF0000000000000 = 18442240474082181120
//   qNaN  = 0x7FF8000000000000 = 9221120237041090560
//   junk  = 2^64               = 18446744073709551616
const SRC_WC_OEQ_EQUAL: &str = "def ir_exact_fcmp_oeq_equal : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.oeq (IRTy.float_ 64) (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 4607182418800017408)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))";
const SRC_WC_OEQ_NAN: &str = "def ir_exact_fcmp_oeq_nan : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.oeq (IRTy.float_ 64) (IRScalar.float_ 9221120237041090560) (IRScalar.float_ 9221120237041090560)) (IRStepResult.value (IRScalar.bool_ Bool.false)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.false))";
const SRC_WC_UEQ_NAN: &str = "def ir_exact_fcmp_ueq_nan : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.ueq (IRTy.float_ 64) (IRScalar.float_ 9221120237041090560) (IRScalar.float_ 4607182418800017408)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))";
const SRC_WC_UNE_NAN: &str = "def ir_exact_fcmp_une_nan : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.une (IRTy.float_ 64) (IRScalar.float_ 9221120237041090560) (IRScalar.float_ 9221120237041090560)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))";
const SRC_WC_OLT_NAN: &str = "def ir_exact_fcmp_olt_nan : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.olt (IRTy.float_ 64) (IRScalar.float_ 9221120237041090560) (IRScalar.float_ 4607182418800017408)) (IRStepResult.value (IRScalar.bool_ Bool.false)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.false))";
const SRC_WC_ULT_NAN: &str = "def ir_exact_fcmp_ult_nan : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.ult (IRTy.float_ 64) (IRScalar.float_ 4607182418800017408) (IRScalar.float_ 9221120237041090560)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))";
const SRC_WC_OEQ_ZEROS: &str = "def ir_exact_fcmp_oeq_zeros : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.oeq (IRTy.float_ 64) (IRScalar.float_ 0) (IRScalar.float_ 9223372036854775808)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))";
const SRC_WC_OLT_ZEROS: &str = "def ir_exact_fcmp_olt_zeros : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.olt (IRTy.float_ 64) (IRScalar.float_ 9223372036854775808) (IRScalar.float_ 0)) (IRStepResult.value (IRScalar.bool_ Bool.false)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.false))";
const SRC_WC_OLT_NEG: &str = "def ir_exact_fcmp_olt_neg : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.olt (IRTy.float_ 64) (IRScalar.float_ 13835058055282163712) (IRScalar.float_ 13830554455654793216)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))";
const SRC_WC_OGT_SWAP: &str = "def ir_exact_fcmp_ogt_swap : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.ogt (IRTy.float_ 64) (IRScalar.float_ 4611686018427387904) (IRScalar.float_ 4607182418800017408)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))";
const SRC_WC_OGE_INF: &str = "def ir_exact_fcmp_oge_inf : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.oge (IRTy.float_ 64) (IRScalar.float_ 9218868437227405312) (IRScalar.float_ 9218868437227405312)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))";
const SRC_WC_OLT_NINF: &str = "def ir_exact_fcmp_olt_ninf : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.olt (IRTy.float_ 64) (IRScalar.float_ 18442240474082181120) (IRScalar.float_ 4607182418800017408)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))";
const SRC_WC_OLE_ASYM: &str = "def ir_exact_fcmp_ole_asym : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.ole (IRTy.float_ 64) (IRScalar.float_ 4611686018427387904) (IRScalar.float_ 4607182418800017408)) (IRStepResult.value (IRScalar.bool_ Bool.false)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.false))";
const SRC_WC_UGE_NAN: &str = "def ir_exact_fcmp_uge_nan : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.uge (IRTy.float_ 64) (IRScalar.float_ 9221120237041090560) (IRScalar.float_ 9221120237041090560)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))";
const SRC_WC_JUNK_OEQ: &str = "def ir_exact_fcmp_junk_oeq : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.oeq (IRTy.float_ 64) (IRScalar.float_ 18446744073709551616) (IRScalar.float_ 18446744073709551616)) (IRStepResult.value (IRScalar.bool_ Bool.false)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.false))";
const SRC_WC_JUNK_UEQ: &str = "def ir_exact_fcmp_junk_ueq : Eq IRStepResult (ir_fcmp_eval IRFCmpOp.ueq (IRTy.float_ 64) (IRScalar.float_ 18446744073709551616) (IRScalar.float_ 0)) (IRStepResult.value (IRScalar.bool_ Bool.true)) := Eq.refl IRStepResult (IRStepResult.value (IRScalar.bool_ Bool.true))";

impl Specification {
    /// The float-comparison band: the non-NaN bit-order deciders, the
    /// unordered split, the 12-arm operator table, the typed dispatcher, and
    /// the kernel-executed witnesses.
    ///
    /// Registered from `add_eval_ir_compare` (in [`super::eval_ir_ops`]),
    /// which runs AFTER `add_eval_ir_float` — everything here reuses that
    /// module's classification (`ir_f64_class`, `ir_f64_mag`,
    /// `ir_f64_is_neg`), its machine facings (`ir_float2`,
    /// `ir_ty_float_width`, `ir_float_fault`, `ir_float_type_fault`), and the
    /// folded deciders (`ir_nat_ltb`, `ir_nat_eqb`, `ir_nat_iszero`).
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check — for the witnesses, that means the kernel RAN the
    /// comparison and got a different Bool, which is a red to report, never
    /// to tune.
    pub(super) fn add_eval_ir_fcmp(&mut self) -> Result<(), SpecError> {
        self.add_recursive_def(
            concat!(
                "def ir_f64_is_nan (n : Nat) : Bool := ",
                "IRF64Class.rec (fun (_ : IRF64Class) => Bool) ",
                "Bool.true Bool.false Bool.false Bool.false ",
                "(ir_f64_class n)",
            ),
            "Is this bit pattern a NaN? Decided by THE classification (ir_f64_class) rather \
             than by a re-derived boundary test, so the comparison lane and the arithmetic \
             lane cannot disagree about what a NaN is — junk patterns at or above 2^64 \
             classify nan_ there and are therefore NaN here too, by the same construction. \
             Minor order is the constructor order (nan_, inf_, zero_, fin_). DerivedProved, \
             zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_unordered (a : Nat) (b : Nat) : Bool := ",
                "Bool.or (ir_f64_is_nan a) (ir_f64_is_nan b)",
            ),
            "IEEE 754's UNORDERED relation: either operand is a NaN. This is the term every \
             one of the 12 predicates consults first — trust-ir a4e81b6 interpret.rs:6057 \
             (`let unordered = lhs.is_nan() || rhs.is_nan()`), arm for arm. DerivedProved, \
             zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_eqb (a : Nat) (b : Nat) : Bool := ",
                "Bool.or (ir_nat_eqb a b) ",
                "(Bool.and (ir_nat_iszero (ir_f64_mag a)) (ir_nat_iszero (ir_f64_mag b)))",
            ),
            "Binary64 VALUE equality on non-NaN patterns: identical bits, OR both magnitudes \
             zero (+0 = -0 across two different bit patterns, the format's one many-to-one \
             value). Exact because every other non-NaN value has exactly one pattern. Only \
             consulted under the unordered guard, so its answer on NaN patterns is never the \
             predicate's answer. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_ltb (a : Nat) (b : Nat) : Bool := ",
                "Bool.rec (fun (_ : Bool) => Bool) ",
                "(Bool.rec (fun (_ : Bool) => Bool) ",
                "(ir_nat_ltb (ir_f64_mag a) (ir_f64_mag b)) ",
                "Bool.false ",
                "(ir_f64_is_neg b)) ",
                "(Bool.rec (fun (_ : Bool) => Bool) ",
                "(Bool.not (Bool.and (ir_nat_iszero (ir_f64_mag a)) (ir_nat_iszero (ir_f64_mag b)))) ",
                "(ir_nat_ltb (ir_f64_mag b) (ir_f64_mag a)) ",
                "(ir_f64_is_neg b)) ",
                "(ir_f64_is_neg a)",
            ),
            "Binary64 VALUE order on non-NaN patterns — the sign-magnitude order the format \
             was designed to sort by. Outer Bool.rec on a's sign, inner on b's; minor order \
             is (false, true) so each FIRST minor is the non-negative case. Both \
             non-negative: magnitude order (finite < infinity falls out because the infinity \
             magnitude bounds every finite one). Both negative: magnitude order REVERSED. \
             a negative, b non-negative: true UNLESS both are zeros (-0 < +0 is false, the \
             signed-zero exception). a non-negative, b negative: false. Deciders are one \
             ir_nat_ltb (native BigNat subtraction) over ir_f64_mag's single exact Nat.sub \
             — the folded path, nothing walks. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_f64_leb (a : Nat) (b : Nat) : Bool := ",
                "Bool.or (ir_f64_ltb a b) (ir_f64_eqb a b)",
            ),
            "Binary64 less-or-equal on non-NaN patterns: the disjunction, exactly as <= is < \
             or = on the reals the non-NaN patterns denote. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            r"def ir_fcmp_bool (op : IRFCmpOp) (x : Nat) (y : Nat) : Bool := match op with
| IRFCmpOp.oeq => Bool.and (Bool.not (ir_f64_unordered x y)) (ir_f64_eqb x y)
| IRFCmpOp.one_ => Bool.and (Bool.not (ir_f64_unordered x y)) (Bool.not (ir_f64_eqb x y))
| IRFCmpOp.olt => Bool.and (Bool.not (ir_f64_unordered x y)) (ir_f64_ltb x y)
| IRFCmpOp.ole => Bool.and (Bool.not (ir_f64_unordered x y)) (ir_f64_leb x y)
| IRFCmpOp.ogt => Bool.and (Bool.not (ir_f64_unordered x y)) (ir_f64_ltb y x)
| IRFCmpOp.oge => Bool.and (Bool.not (ir_f64_unordered x y)) (ir_f64_leb y x)
| IRFCmpOp.ueq => Bool.or (ir_f64_unordered x y) (ir_f64_eqb x y)
| IRFCmpOp.une => Bool.or (ir_f64_unordered x y) (Bool.not (ir_f64_eqb x y))
| IRFCmpOp.ult => Bool.or (ir_f64_unordered x y) (ir_f64_ltb x y)
| IRFCmpOp.ule => Bool.or (ir_f64_unordered x y) (ir_f64_leb x y)
| IRFCmpOp.ugt => Bool.or (ir_f64_unordered x y) (ir_f64_ltb y x)
| IRFCmpOp.uge => Bool.or (ir_f64_unordered x y) (ir_f64_leb y x)",
            "*** THE 12 FCMP PREDICATES ON binary64 BIT PATTERNS. *** Arm for arm trust-ir \
             a4e81b6's eval_fcmp_f64 (interpret.rs:6056-6072): ordered predicates are `NOT \
             unordered AND cmp`, unordered predicates `unordered OR cmp`; gt/ge exchange the \
             operands of lt/le (exact on the non-NaN reals), ne negates eq (exact there too, \
             and on a NaN pair both sides are decided by the unordered term alone — which is \
             precisely IEEE 754 making != true on NaNs). The 12 arms are enumerated rather \
             than collapsed so the per-operator claim stays checkable — these are the '12 \
             named places' the old refusal reserved, now landed. DerivedProved, zero \
             axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_float_cmp (f : Nat -> Nat -> Bool) (t : IRTy) ",
                "(a : IRScalar) (b : IRScalar) : IRStepResult := ",
                "IROption.rec Nat (fun (_ : IROption Nat) => IRStepResult) ",
                "ir_float_type_fault ",
                "(fun (w : Nat) => Bool.rec (fun (_ : Bool) => IRStepResult) ",
                "ir_float_fault ",
                "(ir_float2 (fun (x : Nat) (y : Nat) => ",
                "IRStepResult.value (IRScalar.bool_ (f x y))) a b) ",
                "(ir_nat_eqb w 64)) ",
                "(ir_ty_float_width t)",
            ),
            "The typed float COMPARISON dispatcher — ir_float_binop's exact shape with a Bool \
             result: a non-float type is type_error not_float; a float type at any width but \
             64 is the tagged unmodelled outcome (binary32/binary16 are different formats \
             with different NaN boundaries, and this module decides only binary64 — the \
             pinned interpreter DOES answer f32 compares, so this is a recorded fragment \
             boundary, not parity); at width 64 the operands are coerced through ir_float2 \
             and the predicate decides. The instruction's IRTy is semantic input here, \
             exactly as in the arithmetic dispatcher. DerivedProved, zero axiom_deps.",
        )?;

        self.add_recursive_def(
            concat!(
                "def ir_fcmp_eval (op : IRFCmpOp) (t : IRTy) ",
                "(a : IRScalar) (b : IRScalar) : IRStepResult := ",
                "ir_float_cmp (ir_fcmp_bool op) t a b",
            ),
            "FCmp semantics, 12/12 arms REAL on the classified binary64 fragment (plan W4, \
             2026-08-25). Until this wave every arm was the tagged `unmodelled float_domain` \
             outcome and the doc here promised 'a future float domain has 12 named places to \
             land' — this is that landing: the operator table is ir_fcmp_bool, the type/width \
             gate and operand coercion are ir_float_cmp, and the signature GAINED the \
             instruction type `t` (the dispatch previously dropped it), because the width \
             gate is semantic exactly as it is for ir_binop_eval's float arms. Comparison is \
             TOTAL on classified operands — a NaN produces an ANSWER (ordered false / \
             unordered true), never a refusal, because a Bool has no payload for the \
             implementation to define. DerivedProved, zero axiom_deps.",
        )?;

        // ── the executed witnesses ─────────────────────────────────────
        self.add_recursive_def(SRC_WC_OEQ_EQUAL, "fcmp oeq 1.0 1.0 = true: the ordered equality answers on equal finite patterns. Run by the kernel through the full typed dispatcher. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_OEQ_NAN, "fcmp oeq NaN NaN = FALSE — the sentence every fcmp semantics is judged by: a NaN is not equal to itself under the ordered predicate, even at IDENTICAL bit patterns (ir_f64_eqb alone would say true; the unordered guard is what makes the arm right). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_UEQ_NAN, "fcmp ueq NaN 1.0 = true: the unordered predicates answer TRUE on any NaN operand — the other half of the ordered/unordered split, at a mixed operand pair. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_UNE_NAN, "fcmp une NaN NaN = true: != is TRUE on a NaN pair (unordered short-circuits before the negated equality is consulted) — IEEE 754's most-quoted comparison fact, executed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_OLT_NAN, "fcmp olt NaN 1.0 = false: ordered less-than declines on a NaN, whatever the magnitudes would have said. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_ULT_NAN, "fcmp ult 1.0 NaN = true: unordered less-than accepts on a RIGHT NaN — the operand side the left-NaN witnesses do not pin. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_OEQ_ZEROS, "fcmp oeq +0.0 -0.0 = TRUE: the two zeros are DIFFERENT bit patterns and the SAME value — the one many-to-one point of the format, and the reason ir_f64_eqb is not bare bit equality. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_OLT_ZEROS, "fcmp olt -0.0 +0.0 = FALSE: equal values are not less, though the naive sign-split (negative < non-negative) would say true — the signed-zero conjunct in ir_f64_ltb's mixed-sign arm is what this executes. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_OLT_NEG, "fcmp olt -2.0 -1.0 = true: on the negative side the MAGNITUDE order reverses — the arm a bare bit-pattern comparison would get exactly backwards. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_OGT_SWAP, "fcmp ogt 2.0 1.0 = true: gt is lt with the operands exchanged, and the exchange is executed rather than assumed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_OGE_INF, "fcmp oge +inf +inf = true: infinities are ORDERED values (equal to themselves, greater than every finite), unlike NaNs — the class split the comparison lane must not blur. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_OLT_NINF, "fcmp olt -inf 1.0 = true: the negative infinity sits below every finite value through the reversed-magnitude arm (its magnitude is the LARGEST). DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_OLE_ASYM, "fcmp ole 2.0 1.0 = false: le is a real order test, not a reflexivity artifact — the asymmetric pair pins the direction. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_UGE_NAN, "fcmp uge NaN NaN = true: the unordered family answers true on the all-NaN quadrant for the swapped-operand predicates too. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_JUNK_OEQ, "fcmp oeq (2^64) (2^64) = FALSE: a Nat that is not a 64-bit pattern at all classifies nan_ (ir_f64_class's junk posture), so under a comparison it answers exactly as a NaN — ordered predicates false even at identical carriers. The junk rule carried through from the arithmetic lane unchanged, executed. DerivedProved, zero axiom_deps.")?;
        self.add_recursive_def(SRC_WC_JUNK_UEQ, "fcmp ueq (2^64) +0.0 = true: the unordered half of the junk-classifies-NaN posture. DerivedProved, zero axiom_deps.")?;

        // ── the fragment/fault boundary, universally quantified ────────
        self.add_recursive_def(
            concat!(
                "def ir_fcmp_int_ty_faults (op : IRFCmpOp) (w : Nat) ",
                "(a : IRScalar) (b : IRScalar) : Eq IRStepResult ",
                "(ir_fcmp_eval op (IRTy.int_ w) a b) ir_float_type_fault := ",
                "Eq.refl IRStepResult ir_float_type_fault",
            ),
            "An fcmp at an INTEGER type is `type_error not_float` at EVERY operator, width \
             and operand pair: the kernel iota-reduces ir_ty_float_width on the int_ \
             constructor, so nothing else is consulted — ill-formed IR, the interpreter's \
             type-error class, not an unmodelled fragment. DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_fcmp_f32_unmodelled (op : IRFCmpOp) ",
                "(a : IRScalar) (b : IRScalar) : Eq IRStepResult ",
                "(ir_fcmp_eval op (IRTy.float_ 32) a b) ir_float_fault := ",
                "Eq.refl IRStepResult ir_float_fault",
            ),
            "An fcmp at binary32 is the TAGGED `unmodelled float_domain` outcome at every \
             operator and operand pair — the dated fragment refusal (2026-08-25): the pinned \
             interpreter executes f32 compares (eval_fcmp_f32), but binary32 has a different \
             NaN boundary and this value domain decides only binary64; a tagged refusal can \
             never become a wrong answer. Recorded in data/evalir_w4.PENDING.md. \
             DerivedProved, zero axiom_deps.",
        )?;
        self.add_recursive_def(
            concat!(
                "def ir_fcmp_not_float_operand (op : IRFCmpOp) (n : Nat) ",
                "(b : IRScalar) : Eq IRStepResult ",
                "(ir_fcmp_eval op (IRTy.float_ 64) (IRScalar.int_ n) b) ",
                "ir_float_type_fault := ",
                "Eq.refl IRStepResult ir_float_type_fault",
            ),
            "A non-float OPERAND under a well-formed f64 fcmp fails closed with type_error \
             not_float at every operator, payload and second operand: ir_float2's first \
             coercion rejects int_ before the predicate or the other operand is consulted — \
             an integer is deliberately not a bit pattern here (ir_as_float's doc). \
             DerivedProved, zero axiom_deps.",
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The witness bit patterns are the binary64s the comments claim.
    #[test]
    fn test_the_fcmp_witness_patterns_are_binary64s() {
        assert_eq!(4_607_182_418_800_017_408u64, 1.0f64.to_bits());
        assert_eq!(4_611_686_018_427_387_904u64, 2.0f64.to_bits());
        assert_eq!(13_830_554_455_654_793_216u64, (-1.0f64).to_bits());
        assert_eq!(13_835_058_055_282_163_712u64, (-2.0f64).to_bits());
        assert_eq!(9_223_372_036_854_775_808u64, (-0.0f64).to_bits());
        assert_eq!(9_218_868_437_227_405_312u64, f64::INFINITY.to_bits());
        assert_eq!(18_442_240_474_082_181_120u64, f64::NEG_INFINITY.to_bits());
        assert!(f64::from_bits(9_221_120_237_041_090_560u64).is_nan());
        assert_eq!(18_446_744_073_709_551_616u128, 1u128 << 64);
    }

    /// The pinned interpreter's fcmp formula (`eval_fcmp_f64`, a4e81b6
    /// `interpret.rs:6056-6072`), restated over host `f64` for the
    /// cross-check below. Distinct parameters on purpose: the NaN rows
    /// compare a value with itself and must exercise the operator, not a
    /// syntactic self-comparison.
    fn host_fcmp(op: &str, l: f64, r: f64) -> bool {
        let u = l.is_nan() || r.is_nan();
        match op {
            "oeq" => !u && l == r,
            "one" => !u && l != r,
            "olt" => !u && l < r,
            "ole" => !u && l <= r,
            "ogt" => !u && l > r,
            "oge" => !u && l >= r,
            "ueq" => u || l == r,
            "une" => u || l != r,
            "ult" => u || l < r,
            "ule" => u || l <= r,
            "ugt" => u || l > r,
            "uge" => u || l >= r,
            other => panic!("unknown fcmp op {other}"),
        }
    }

    /// **Every answering witness agrees with the HARDWARE** — the comparison
    /// lane's copy of the arithmetic lane's cross-check: each witness's
    /// operator/operands/expected-Bool triple is recomputed on host `f64`
    /// with the pinned interpreter's own formula ([`host_fcmp`]) and must
    /// match the Bool the spec string pins. The junk rows are excluded: 2^64
    /// is not a representable `f64` bit pattern, which is exactly why they
    /// exist.
    #[test]
    fn test_the_fcmp_witnesses_agree_with_real_f64() {
        let b = f64::from_bits;
        let one = b(4_607_182_418_800_017_408);
        let two = b(4_611_686_018_427_387_904);
        let mone = b(13_830_554_455_654_793_216);
        let mtwo = b(13_835_058_055_282_163_712);
        let pz = b(0);
        let mz = b(9_223_372_036_854_775_808);
        let pinf = b(9_218_868_437_227_405_312);
        let minf = b(18_442_240_474_082_181_120);
        let nan = b(9_221_120_237_041_090_560);

        // (source, operator, lhs, rhs)
        let rows: &[(&str, &str, f64, f64)] = &[
            (SRC_WC_OEQ_EQUAL, "oeq", one, one),
            (SRC_WC_OEQ_NAN, "oeq", nan, nan),
            (SRC_WC_UEQ_NAN, "ueq", nan, one),
            (SRC_WC_UNE_NAN, "une", nan, nan),
            (SRC_WC_OLT_NAN, "olt", nan, one),
            (SRC_WC_ULT_NAN, "ult", one, nan),
            (SRC_WC_OEQ_ZEROS, "oeq", pz, mz),
            (SRC_WC_OLT_ZEROS, "olt", mz, pz),
            (SRC_WC_OLT_NEG, "olt", mtwo, mone),
            (SRC_WC_OGT_SWAP, "ogt", two, one),
            (SRC_WC_OGE_INF, "oge", pinf, pinf),
            (SRC_WC_OLT_NINF, "olt", minf, one),
            (SRC_WC_OLE_ASYM, "ole", two, one),
            (SRC_WC_UGE_NAN, "uge", nan, nan),
        ];
        for (src, op, lhs, rhs) in rows {
            let want = host_fcmp(op, *lhs, *rhs);
            let pinned = format!("(IRScalar.bool_ Bool.{want})");
            assert!(
                src.contains(&pinned),
                "the witness must pin what the hardware computes for {lhs} vs {rhs}: \
                 expected {want} in {src}"
            );
            // …and each witness carries BOTH operands' bit patterns.
            for v in [lhs, rhs] {
                assert!(
                    src.contains(&v.to_bits().to_string()),
                    "operand {v} ({}) missing from {src}",
                    v.to_bits()
                );
            }
        }
    }

    /// The junk witnesses answer as NaN answers — false ordered, true
    /// unordered — and carry the out-of-format pattern.
    #[test]
    fn test_junk_answers_as_nan() {
        assert!(SRC_WC_JUNK_OEQ.contains("18446744073709551616"));
        assert!(SRC_WC_JUNK_OEQ.contains("(IRScalar.bool_ Bool.false)"));
        assert!(SRC_WC_JUNK_UEQ.contains("18446744073709551616"));
        assert!(SRC_WC_JUNK_UEQ.contains("(IRScalar.bool_ Bool.true)"));
    }

    #[test]
    fn test_sources_balanced_ascii() {
        for src in [
            SRC_WC_OEQ_EQUAL,
            SRC_WC_OEQ_NAN,
            SRC_WC_UEQ_NAN,
            SRC_WC_UNE_NAN,
            SRC_WC_OLT_NAN,
            SRC_WC_ULT_NAN,
            SRC_WC_OEQ_ZEROS,
            SRC_WC_OLT_ZEROS,
            SRC_WC_OLT_NEG,
            SRC_WC_OGT_SWAP,
            SRC_WC_OGE_INF,
            SRC_WC_OLT_NINF,
            SRC_WC_OLE_ASYM,
            SRC_WC_UGE_NAN,
            SRC_WC_JUNK_OEQ,
            SRC_WC_JUNK_UEQ,
        ] {
            let mut d: i64 = 0;
            for ch in src.chars() {
                match ch {
                    '(' => d += 1,
                    ')' => d -= 1,
                    _ => {}
                }
                assert!(d >= 0, "unbalanced parens in {src}");
            }
            assert_eq!(d, 0, "unbalanced parens in {src}");
            assert!(src.is_ascii(), "spec sources must be ASCII");
        }
    }
}
