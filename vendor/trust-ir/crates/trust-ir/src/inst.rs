// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::constant::{Constant, ConstantG};
use crate::ty::{Ty, TyG};
use crate::value::{BindingFrameId, BlockId, FuncId, GlobalId, ValueId};
use core::ops::ControlFlow;

mod observed_edges;
mod observed_operands;
mod observed_types;

// Named so `CmpXchg.weak`'s serde attribute fits on ONE line: rustfmt wraps a longer one
// across lines, which `tests/lean_schema_parity.rs`'s field-level `Inst` axis cannot read.
#[cfg(feature = "serde")]
use crate::is_false;

// Named for the same reason: `Assert.site`'s serde attribute stays on ONE line.
// `site` is `Assert`'s sole trailing skipped field (positional MessagePack
// tolerates exactly one); `kind` before it is always emitted.
#[cfg(feature = "serde")]
fn no_site(site: &Option<PanicSite>) -> bool {
    site.is_none()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    URem,
    SRem,
    FAdd,
    FSub,
    FMul,
    FDiv,
    FRem,
    /// Floating-point minimum, NaN-propagating-away (the IEEE-754-2019
    /// `minimumNumber` / Rust `f{32,64}::min` semantics): if exactly one
    /// operand is NaN the result is the OTHER (non-NaN) operand; if both are
    /// NaN the result is NaN; otherwise the numerically lesser operand. This is
    /// NOT IEEE `fp.min` for signed zeros (it follows the hardware
    /// MINSD/MINSS ±0 behavior, which Rust's `nsz` lowering admits).
    FMin,
    /// Floating-point maximum, NaN-propagating-away (the IEEE-754-2019
    /// `maximumNumber` / Rust `f{32,64}::max` semantics). The mirror of `FMin`.
    FMax,
    /// Bitwise conjunction for integer scalars/vectors; logical conjunction for
    /// boolean scalars/vectors.
    And,
    /// Bitwise disjunction for integer scalars/vectors; logical disjunction for
    /// boolean scalars/vectors.
    Or,
    /// Bitwise exclusive-or for integer scalars/vectors; logical exclusive-or
    /// for boolean scalars/vectors.
    Xor,
    Shl,
    LShr,
    AShr,
    /// Logical conjunction on the boolean 0/1 carrier. DISTINCT from [`BinOp::And`]
    /// above, whose doc admits both readings ("bitwise for integer …; logical for
    /// boolean") — an overloading the LEAN semantics does not share, where
    /// `semIntBinOp .And` is `Int.land` unconditionally. That gap is not academic:
    /// a Bool connective lowered onto `And` denotes through an OPAQUE integer
    /// carrier, so its refinement closes by `rfl` while asserting nothing a
    /// consumer contract (`ensures r == (a && b)`) can discharge against. These
    /// three are the unambiguous target — total, computable, decidable — and a
    /// frontend that means the connective must say so.
    BAnd,
    /// Logical disjunction on the boolean 0/1 carrier. See [`BinOp::BAnd`].
    BOr,
    /// Logical exclusive-or on the boolean 0/1 carrier. See [`BinOp::BAnd`].
    /// `bxor %b, true` is the ONE spelling of scalar boolean negation
    /// (SPEC_RATIFICATIONS §3.2, WS2.21); [`UnOp::Not`] is bitwise and is
    /// refused at scalar `Bool`.
    BXor,
    /// Rotate left (WS3.20, F-057): the bits of `lhs` rotated toward the most
    /// significant end by `rhs` positions. TOTAL — the amount is reduced
    /// MODULO the bit width (Rust `uN::rotate_left`, LLVM `fshl(x, x, n)`),
    /// so there is no out-of-range poison and no `ShiftInRange` obligation,
    /// unlike `Shl`/`LShr`/`AShr`. Integer scalars and vectors only, like
    /// `CtPop`. Text `rotl`; Lean `semIntBinOp .RotL`; wire BinOp tag 23
    /// (v51, the INST wire batch; `RotR` 24, `FCopySign` 25).
    RotL,
    /// Rotate right (WS3.20, F-057): the mirror of [`BinOp::RotL`] (Rust
    /// `uN::rotate_right`, LLVM `fshr(x, x, n)`). Text `rotr`.
    RotR,
    /// IEEE 754 `copySign` (WS3.20, F-057): the magnitude of `lhs` with the
    /// sign bit of `rhs` — exact, quiet, never rounds, never signals; a NaN
    /// magnitude stays a NaN with its payload. Float scalars and vectors only,
    /// like `FMin`. The reference interpreter executes it at `F32`/`F64`
    /// exactly as it executes `FNeg`, and refuses `F16` by name. Text
    /// `fcopysign`; Lean `semFloatBinOp .FCopySign`.
    FCopySign,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UnOp {
    Neg,
    FNeg,
    /// Floating-point absolute value (clears the IEEE sign bit). The mirror of
    /// `FNeg`: `FNeg` flips the sign bit, `FAbs` clears it.
    FAbs,
    /// Floating-point square root (IEEE `fp.sqrt`, round-to-nearest-even).
    FSqrt,
    /// Floating-point round toward negative infinity (IEEE
    /// `fp.roundToIntegral(RTN, x)`). The integral-valued floor of `x`.
    FFloor,
    /// Floating-point round toward positive infinity (IEEE
    /// `fp.roundToIntegral(RTP, x)`). The integral-valued ceiling of `x`.
    FCeil,
    /// Floating-point round toward zero (IEEE `fp.roundToIntegral(RTZ, x)`).
    /// Truncates the fractional part of `x`.
    FTrunc,
    /// Bitwise complement. Defined on integers, integer vectors and bool
    /// vectors (a bool vector's lanes are its bit mask). NOT on a scalar
    /// `Bool`: boolean negation has one spelling, [`BinOp::BXor`] with `true`
    /// (`bxor %b, true`, SPEC_RATIFICATIONS §3.2), and the validator refuses
    /// `not bool` as `UnOpNotOnScalarBool` (WS2.21, F-033).
    Not,
    CtPop,
    /// Count leading zero bits (WS3.20, F-057). TOTAL: `ctlz 0 = width` — the
    /// ONE spelling (no LLVM-style `is_zero_poison` operand, no poison), so
    /// Rust `uN::leading_zeros` lowers to it directly. Integer scalars and
    /// vectors only, like `CtPop`. Text `ctlz`; Lean `semIntUnOp .CtLz`;
    /// wire UnOp tag 9 (v51, the INST wire batch; `CtTz` 10, `BSwap` 11,
    /// `BitReverse` 12).
    CtLz,
    /// Count trailing zero bits (WS3.20, F-057). TOTAL: `cttz 0 = width`
    /// (Rust `uN::trailing_zeros`). Text `cttz`; Lean `semIntUnOp .CtTz`.
    CtTz,
    /// Byte swap (WS3.20, F-057): reverse the order of the `width / 8` bytes
    /// (Rust `uN::swap_bytes`, LLVM `bswap`). Every TrustIr integer width is a
    /// whole number of bytes, so it is total; on an 8-bit operand it is the
    /// identity. Text `bswap`; Lean `semIntUnOp .BSwap`.
    BSwap,
    /// Bit reverse (WS3.20, F-057): reverse the order of all `width` bits
    /// (Rust `uN::reverse_bits`, LLVM `bitreverse`). Text `bitreverse`; Lean
    /// `semIntUnOp .BitReverse`.
    BitReverse,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum OverflowOp {
    AddOverflow,
    SubOverflow,
    MulOverflow,
}

/// The operation whose overflow an [`AssertKind::Overflow`] check guards
/// (plan item P, wire v52). One variant per Rust overflow panic: the seven
/// arithmetic operators rustc checks (`Add`/`Sub`/`Mul`/`Div`/`Rem`/`Shl`/
/// `Shr`, MIR `AssertKind::Overflow(op, ..)`) and negation (MIR
/// `AssertKind::OverflowNeg`). Division and remainder overflow only at
/// `MIN / -1` / `MIN % -1`; shift "overflow" is a shift amount `>= width`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum AssertOverflowOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
    Neg,
}

impl AssertOverflowOp {
    /// Every operation, in wire-tag order.
    pub const ALL: [AssertOverflowOp; 8] = [
        AssertOverflowOp::Add,
        AssertOverflowOp::Sub,
        AssertOverflowOp::Mul,
        AssertOverflowOp::Div,
        AssertOverflowOp::Rem,
        AssertOverflowOp::Shl,
        AssertOverflowOp::Shr,
        AssertOverflowOp::Neg,
    ];

    /// The text-format spelling (`assert %c overflow <name>`).
    pub const fn name(self) -> &'static str {
        match self {
            AssertOverflowOp::Add => "add",
            AssertOverflowOp::Sub => "sub",
            AssertOverflowOp::Mul => "mul",
            AssertOverflowOp::Div => "div",
            AssertOverflowOp::Rem => "rem",
            AssertOverflowOp::Shl => "shl",
            AssertOverflowOp::Shr => "shr",
            AssertOverflowOp::Neg => "neg",
        }
    }

    /// Inverse of [`Self::name`].
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|op| op.name() == name)
    }
}

/// Why an [`Inst::Assert`] fails: the Rust panic its failure IS (plan item P,
/// "Panics, faithfully"; wire v52, `docs/SPEC_RATIFICATIONS.md` §19).
///
/// A producer lowering a MIR/THIR runtime check states which check it is, so
/// a consumer can lower a failed check to the Rust panic entry point that
/// prints Rust's message ([`Self::rust_panic_lang_item`]) instead of a bare
/// trap, and key check elision on the check's identity. The kind is an
/// attribute of the FAILURE only: whether the assert fails is still exactly
/// `!cond`, so no kind changes which executions panic.
///
/// [`AssertKind::Unspecified`] is what every assert decoded from an older
/// blob (any wire version, Inst tag 29), from serde without a `kind`, or
/// from text without a kind clause carries: a check of UNKNOWN identity. It
/// is the default and stays legal, but a consumer must not lower it
/// faithfully — it has no Rust message to print — and refuses it where
/// faithful panics are required
/// (`CodegenAdmission::with_require_assert_panic_kinds` in `trust-ir-build`).
///
/// The operand-carrying kinds name SSA values the panic message prints; they
/// are ordinary operands (visited by [`Inst::visit_value_operands`]), read
/// only when the assert fails, and must be `usize` (the validator checks).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum AssertKind {
    /// Unknown check identity: older blobs and producers that do not record
    /// it. Never lowered faithfully.
    #[default]
    Unspecified,
    /// Arithmetic overflow of `op` (`panic_const_<op>_overflow`).
    Overflow(AssertOverflowOp),
    /// Division by zero (`panic_const_div_by_zero`).
    DivByZero,
    /// Remainder by zero (`panic_const_rem_by_zero`).
    RemByZero,
    /// An index out of bounds (`panic_bounds_check(index, len)`).
    BoundsCheck { index: ValueId, len: ValueId },
    /// A misaligned pointer dereference
    /// (`panic_misaligned_pointer_dereference(required, found)`): `required`
    /// is the alignment, `found` the address.
    MisalignedPtr { required: ValueId, found: ValueId },
    /// A null pointer dereference (`panic_null_pointer_dereference`).
    NullPtr,
}

impl AssertKind {
    /// `true` for [`AssertKind::Unspecified`].
    pub const fn is_unspecified(&self) -> bool {
        matches!(self, AssertKind::Unspecified)
    }

    /// The `core` lang item a faithful lowering calls when the check fails,
    /// or `None` for [`AssertKind::Unspecified`], which has none: a consumer
    /// that needs a faithful panic refuses that assert rather than inventing
    /// one. Names are rustc's (`compiler/rustc_hir/src/lang_items.rs`).
    pub const fn rust_panic_lang_item(&self) -> Option<&'static str> {
        Some(match self {
            AssertKind::Unspecified => return None,
            AssertKind::Overflow(op) => match op {
                AssertOverflowOp::Add => "panic_const_add_overflow",
                AssertOverflowOp::Sub => "panic_const_sub_overflow",
                AssertOverflowOp::Mul => "panic_const_mul_overflow",
                AssertOverflowOp::Div => "panic_const_div_overflow",
                AssertOverflowOp::Rem => "panic_const_rem_overflow",
                AssertOverflowOp::Shl => "panic_const_shl_overflow",
                AssertOverflowOp::Shr => "panic_const_shr_overflow",
                AssertOverflowOp::Neg => "panic_const_neg_overflow",
            },
            AssertKind::DivByZero => "panic_const_div_by_zero",
            AssertKind::RemByZero => "panic_const_rem_by_zero",
            AssertKind::BoundsCheck { .. } => "panic_bounds_check",
            AssertKind::MisalignedPtr { .. } => "panic_misaligned_pointer_dereference",
            AssertKind::NullPtr => "panic_null_pointer_dereference",
        })
    }

    /// The panic message of an operand-free kind, byte-identical to the one
    /// `core` prints (`library/core/src/panicking.rs`), or `None` for the
    /// operand-carrying kinds (see [`Self::panic_message`]).
    /// `Unspecified` is `"assertion failed"`, the reference engines' message
    /// for a check of unknown identity — NOT a Rust message.
    pub const fn constant_panic_message(&self) -> Option<&'static str> {
        Some(match self {
            AssertKind::Unspecified => "assertion failed",
            AssertKind::Overflow(op) => match op {
                AssertOverflowOp::Add => "attempt to add with overflow",
                AssertOverflowOp::Sub => "attempt to subtract with overflow",
                AssertOverflowOp::Mul => "attempt to multiply with overflow",
                AssertOverflowOp::Div => "attempt to divide with overflow",
                AssertOverflowOp::Rem => "attempt to calculate the remainder with overflow",
                AssertOverflowOp::Shl => "attempt to shift left with overflow",
                AssertOverflowOp::Shr => "attempt to shift right with overflow",
                AssertOverflowOp::Neg => "attempt to negate with overflow",
            },
            AssertKind::DivByZero => "attempt to divide by zero",
            AssertKind::RemByZero => "attempt to calculate the remainder with a divisor of zero",
            AssertKind::NullPtr => "null pointer dereference occurred",
            AssertKind::BoundsCheck { .. } | AssertKind::MisalignedPtr { .. } => return None,
        })
    }

    /// The panic message `core` prints for this kind, given the operand
    /// VALUES (`[index, len]` for `BoundsCheck`, `[required, found]` for
    /// `MisalignedPtr`, as unsigned integers; ignored otherwise).
    pub fn panic_message(&self, operands: [u128; 2]) -> String {
        match self {
            AssertKind::BoundsCheck { .. } => format!(
                "index out of bounds: the len is {} but the index is {}",
                operands[1], operands[0]
            ),
            AssertKind::MisalignedPtr { .. } => format!(
                "misaligned pointer dereference: address must be a multiple of {:#x} but is {:#x}",
                operands[0], operands[1]
            ),
            other => other
                .constant_panic_message()
                .expect("every operand-free kind has a constant message")
                .to_owned(),
        }
    }

    /// The SSA operands this kind carries, in field order.
    pub fn operands(&self) -> Option<[ValueId; 2]> {
        match *self {
            AssertKind::BoundsCheck { index, len } => Some([index, len]),
            AssertKind::MisalignedPtr { required, found } => Some([required, found]),
            _ => None,
        }
    }

    /// Mutable access to the SSA operands, in field order.
    pub fn operands_mut(&mut self) -> Option<[&mut ValueId; 2]> {
        match self {
            AssertKind::BoundsCheck { index, len } => Some([index, len]),
            AssertKind::MisalignedPtr { required, found } => Some([required, found]),
            _ => None,
        }
    }

    /// The operand role names, in field order (diagnostics, text format).
    pub const fn operand_roles(&self) -> Option<[&'static str; 2]> {
        match self {
            AssertKind::BoundsCheck { .. } => Some(["index", "len"]),
            AssertKind::MisalignedPtr { .. } => Some(["required", "found"]),
            _ => None,
        }
    }

    /// The kind's own name, without operands (`overflow`, `div_by_zero`,
    /// `bounds_check`, ...): the text-format keyword after the condition.
    pub const fn keyword(&self) -> &'static str {
        match self {
            AssertKind::Unspecified => "unspecified",
            AssertKind::Overflow(_) => "overflow",
            AssertKind::DivByZero => "div_by_zero",
            AssertKind::RemByZero => "rem_by_zero",
            AssertKind::BoundsCheck { .. } => "bounds_check",
            AssertKind::MisalignedPtr { .. } => "misaligned_ptr",
            AssertKind::NullPtr => "null_ptr",
        }
    }

    /// How many SSA operands this kind carries: 2 for `BoundsCheck` and
    /// `MisalignedPtr`, 0 otherwise. A panic site's entry takes exactly this
    /// many `usize` parameters before the location (amendment P,
    /// `docs/SPEC_RATIFICATIONS.md` §19.1 rule 1).
    pub const fn operand_count(&self) -> usize {
        match self {
            AssertKind::BoundsCheck { .. } | AssertKind::MisalignedPtr { .. } => 2,
            _ => 0,
        }
    }
}

/// Where a failed check's panic is reported: the LAST argument of its panic
/// site's entry (amendment P, wire v54, `docs/SPEC_RATIFICATIONS.md` §19.1).
/// trust-ir treats the record as opaque: no IR semantics reads its bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PanicLocation {
    /// The address of an immutable, non-thread-local module global holding
    /// the record (Rust: a `core::panic::Location` constant). The ONE
    /// spelling of every location known at compile time (§19.1 rule 2).
    Global(GlobalId),
    /// A location computed at run time (a `#[track_caller]` function
    /// forwarding its caller-location parameter). Never defined directly by
    /// `GlobalAddr`, or by a `SymbolAddr` constant naming a module global:
    /// that location is a `Global` (`NonCanonicalPanicLocation`).
    Value(ValueId),
}

/// How a failed assert is realized (amendment P, wire v54): call
/// `entry(kind operands.., location)`; `entry` never returns normally.
///
/// The site changes WHICH panic a failed check is and where it is reported,
/// never whether the check fails. trust-ir checks the entry's SIGNATURE
/// (`usize` per kind operand, then a pointer, not variadic, returning
/// nothing); that the entry IS the frontend's panic entry for the kind is a
/// producer claim (`docs/SPEC_RATIFICATIONS.md` §19.1, prose-only).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct PanicSite {
    /// The module function a failed check calls.
    pub entry: FuncId,
    /// The location record the failed check passes as `entry`'s last argument.
    pub location: PanicLocation,
}

impl PanicSite {
    /// The run-time location operand, if the location is a `Value`.
    pub const fn location_value(&self) -> Option<ValueId> {
        match self.location {
            PanicLocation::Value(value) => Some(value),
            PanicLocation::Global(_) => None,
        }
    }

    /// Mutable access to the run-time location operand (operand rewriting).
    pub fn location_value_mut(&mut self) -> Option<&mut ValueId> {
        match &mut self.location {
            PanicLocation::Value(value) => Some(value),
            PanicLocation::Global(_) => None,
        }
    }

    /// The location global, if the location is a `Global`.
    pub const fn location_global(&self) -> Option<GlobalId> {
        match self.location {
            PanicLocation::Global(global) => Some(global),
            PanicLocation::Value(_) => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ICmpOp {
    Eq,
    Ne,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum FCmpOp {
    OEq,
    ONe,
    OLt,
    OLe,
    OGt,
    OGe,
    UEq,
    UNe,
    ULt,
    ULe,
    UGt,
    UGe,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CastOp {
    /// Drop high bits. `Bool` participates as the canonical one-bit scalar, so
    /// truncating a wider integer to `Bool` keeps its low bit.
    Trunc,
    /// Zero-extend a narrower integer scalar. `Bool` is a one-bit source and
    /// therefore extends as `false -> 0`, `true -> 1`.
    ZExt,
    /// Sign-extend a narrower integer scalar. Extending a one-bit `Bool` maps
    /// `false -> 0` and `true -> -1` (all destination bits set).
    SExt,
    FPTrunc,
    FPExt,
    FPToUI,
    FPToSI,
    UIToFP,
    SIToFP,
    PtrToInt,
    IntToPtr,
    PtrToPtr,
    Bitcast,
    Transmute,
    ReifyFnPointer,
    /// Saturating float→signed-int cast — Rust's `f as iN` (stabilized 1.45).
    /// Unlike [`CastOp::FPToSI`] (raw, LLVM `fptosi`, out-of-range/NaN is UB),
    /// this maps NaN→0 and clamps out-of-range magnitudes to `iN::MIN`/`iN::MAX`
    /// (LLVM `fptosi.sat`). See `docs/ub-numerics-policy.md` §2.
    FPToSISat,
    /// Saturating float→unsigned-int cast — Rust's `f as uN` (LLVM `fptoui.sat`):
    /// NaN→0, negative→0, above-range→`uN::MAX`. The unsigned twin of
    /// [`CastOp::FPToSISat`]; contrast the raw [`CastOp::FPToUI`].
    FPToUISat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Ordering {
    Relaxed,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
}

impl Ordering {
    /// Whether an atomic LOAD may carry this ordering: `Relaxed`, `Acquire`
    /// or `SeqCst` (the C11 / LLVM rule).
    ///
    /// `Release` and `AcqRel` are excluded: a release constrains a WRITE, and
    /// a load performs none, so the ordering would name a fence half the
    /// instruction does not have. Lean states the same rule as
    /// `isValidLoadOrdering` (`TrustIr/Semantics/Atomic.lean`); the validator
    /// refuses a violation as `IllegalAtomicOrdering` by calling this table.
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::atomic_load_*` (gate 13).
    #[inline]
    #[must_use]
    pub const fn is_legal_for_load(self) -> bool {
        matches!(
            self,
            Ordering::Relaxed | Ordering::Acquire | Ordering::SeqCst
        )
    }

    /// Whether an atomic STORE may carry this ordering: `Relaxed`, `Release`
    /// or `SeqCst`. The mirror of [`Ordering::is_legal_for_load`]: `Acquire`
    /// and `AcqRel` are excluded because an acquire constrains a READ and a
    /// store performs none. Lean: `isValidStoreOrdering`.
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::atomic_store_*` (gate 13).
    #[inline]
    #[must_use]
    pub const fn is_legal_for_store(self) -> bool {
        matches!(
            self,
            Ordering::Relaxed | Ordering::Release | Ordering::SeqCst
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum AtomicRMWOp {
    Xchg,
    Add,
    Sub,
    And,
    Or,
    Xor,
    Max,
    Min,
    UMax,
    UMin,
}

impl core::fmt::Display for BinOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            BinOp::Add => "add",
            BinOp::Sub => "sub",
            BinOp::Mul => "mul",
            BinOp::UDiv => "udiv",
            BinOp::SDiv => "sdiv",
            BinOp::URem => "urem",
            BinOp::SRem => "srem",
            BinOp::FAdd => "fadd",
            BinOp::FSub => "fsub",
            BinOp::FMul => "fmul",
            BinOp::FDiv => "fdiv",
            BinOp::FRem => "frem",
            BinOp::FMin => "fmin",
            BinOp::FMax => "fmax",
            BinOp::And => "and",
            BinOp::Or => "or",
            BinOp::Xor => "xor",
            BinOp::Shl => "shl",
            BinOp::LShr => "lshr",
            BinOp::AShr => "ashr",
            BinOp::BAnd => "band",
            BinOp::BOr => "bor",
            BinOp::BXor => "bxor",
            BinOp::RotL => "rotl",
            BinOp::RotR => "rotr",
            BinOp::FCopySign => "fcopysign",
        })
    }
}

impl core::fmt::Display for UnOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            UnOp::Neg => "neg",
            UnOp::FNeg => "fneg",
            UnOp::FAbs => "fabs",
            UnOp::FSqrt => "fsqrt",
            UnOp::FFloor => "ffloor",
            UnOp::FCeil => "fceil",
            UnOp::FTrunc => "ftrunc",
            UnOp::Not => "not",
            UnOp::CtPop => "ctpop",
            UnOp::CtLz => "ctlz",
            UnOp::CtTz => "cttz",
            UnOp::BSwap => "bswap",
            UnOp::BitReverse => "bitreverse",
        })
    }
}

impl core::fmt::Display for OverflowOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            OverflowOp::AddOverflow => "add.overflow",
            OverflowOp::SubOverflow => "sub.overflow",
            OverflowOp::MulOverflow => "mul.overflow",
        })
    }
}

impl core::fmt::Display for ICmpOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            ICmpOp::Eq => "eq",
            ICmpOp::Ne => "ne",
            ICmpOp::Ult => "ult",
            ICmpOp::Ule => "ule",
            ICmpOp::Ugt => "ugt",
            ICmpOp::Uge => "uge",
            ICmpOp::Slt => "slt",
            ICmpOp::Sle => "sle",
            ICmpOp::Sgt => "sgt",
            ICmpOp::Sge => "sge",
        })
    }
}

impl core::fmt::Display for FCmpOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            FCmpOp::OEq => "oeq",
            FCmpOp::ONe => "one",
            FCmpOp::OLt => "olt",
            FCmpOp::OLe => "ole",
            FCmpOp::OGt => "ogt",
            FCmpOp::OGe => "oge",
            FCmpOp::UEq => "ueq",
            FCmpOp::UNe => "une",
            FCmpOp::ULt => "ult",
            FCmpOp::ULe => "ule",
            FCmpOp::UGt => "ugt",
            FCmpOp::UGe => "uge",
        })
    }
}

impl core::fmt::Display for CastOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            CastOp::Trunc => "trunc",
            CastOp::ZExt => "zext",
            CastOp::SExt => "sext",
            CastOp::FPTrunc => "fptrunc",
            CastOp::FPExt => "fpext",
            CastOp::FPToUI => "fptoui",
            CastOp::FPToSI => "fptosi",
            CastOp::UIToFP => "uitofp",
            CastOp::SIToFP => "sitofp",
            CastOp::PtrToInt => "ptrtoint",
            CastOp::IntToPtr => "inttoptr",
            CastOp::PtrToPtr => "ptrtoptr",
            CastOp::Bitcast => "bitcast",
            CastOp::Transmute => "transmute",
            CastOp::ReifyFnPointer => "reify_fn_pointer",
            CastOp::FPToSISat => "fptosi.sat",
            CastOp::FPToUISat => "fptoui.sat",
        })
    }
}

impl core::fmt::Display for Ordering {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Ordering::Relaxed => "relaxed",
            Ordering::Acquire => "acquire",
            Ordering::Release => "release",
            Ordering::AcqRel => "acq_rel",
            Ordering::SeqCst => "seq_cst",
        })
    }
}

impl core::fmt::Display for AtomicRMWOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            AtomicRMWOp::Xchg => "xchg",
            AtomicRMWOp::Add => "add",
            AtomicRMWOp::Sub => "sub",
            AtomicRMWOp::And => "and",
            AtomicRMWOp::Or => "or",
            AtomicRMWOp::Xor => "xor",
            AtomicRMWOp::Max => "max",
            AtomicRMWOp::Min => "min",
            AtomicRMWOp::UMax => "umax",
            AtomicRMWOp::UMin => "umin",
        })
    }
}

/// A single typed slot in a binding frame.
///
/// Slots are named (for diagnostics / debug) and typed. The slot's ordinal
/// in `BindingFrameDef.slots` is the `slot` index used by `Inst::BindSlot`
/// and `Inst::LoadSlot`.
///
/// Slot names have no semantic effect on execution — they exist for text
/// format readability and pretty-printing of quantifier lowerings
/// (e.g., `%1 = bind_slot %0, 0 /*i*/, %7`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BindingSlot {
    pub name: String,
    pub ty: Ty,
}

impl BindingSlot {
    pub fn new(name: impl Into<String>, ty: Ty) -> Self {
        Self {
            name: name.into(),
            ty,
        }
    }
}

/// Declaration of a binding frame's slot layout.
///
/// A binding frame is the SSA representation of a quantifier's binding
/// environment: for `\E i \in S : P(i)`, the frame has one slot `i: I64`
/// (or whatever the element type of `S` is). Frames are opened, bound,
/// loaded from, and closed as SSA values — never as memory — so backends
/// can lower them to stack slots (CPU) or per-lane registers (GPU).
///
/// Each `Inst::OpenFrame` carries its own `BindingFrameDef` inline; frames
/// are not interned at the module level. This keeps binding frames local
/// to the function that uses them and avoids a cross-cutting registry.
/// The `id` is unique *within the enclosing function* and disambiguates
/// frames in text/debug output; it is not a global identifier.
///
/// See `designs/2026-04-18-ty-supremacy-trust-ir-scope.md` §R4 for the
/// design rationale.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BindingFrameDef {
    pub id: BindingFrameId,
    pub name: String,
    pub slots: Vec<BindingSlot>,
}

impl BindingFrameDef {
    pub fn new(id: BindingFrameId, name: impl Into<String>, slots: Vec<BindingSlot>) -> Self {
        Self {
            id,
            name: name.into(),
            slots,
        }
    }

    /// Look up a slot's declared type by its ordinal index.
    pub fn slot_ty(&self, slot: u32) -> Option<&Ty> {
        self.slots.get(slot as usize).map(|s| &s.ty)
    }

    /// Return the number of slots in this frame.
    pub fn arity(&self) -> usize {
        self.slots.len()
    }
}

/// Reason a typed `select` condition does not satisfy the TrustIr contract.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SelectConditionTypeError {
    /// The condition type is not the required scalar `bool` or `<N x bool>`.
    TypeMismatch {
        select_ty: Ty,
        expected_cond_ty: Ty,
        actual_cond_ty: Ty,
    },
    /// The condition is a same-lane integer vector mask. Backends must compare
    /// it to zero first, producing the logical `<N x bool>` mask used by
    /// `select`.
    PhysicalIntegerMaskRequiresCompareToZero {
        select_ty: Ty,
        mask_ty: Ty,
        expected_cond_ty: Ty,
    },
}

impl core::fmt::Display for SelectConditionTypeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SelectConditionTypeError::TypeMismatch {
                select_ty,
                expected_cond_ty,
                actual_cond_ty,
            } => write!(
                f,
                "select over {select_ty} requires condition {expected_cond_ty}, got {actual_cond_ty}"
            ),
            SelectConditionTypeError::PhysicalIntegerMaskRequiresCompareToZero {
                select_ty,
                mask_ty,
                expected_cond_ty,
            } => write!(
                f,
                "select over {select_ty} requires logical condition {expected_cond_ty}; \
                 physical integer mask {mask_ty} must be compared to zero before select"
            ),
        }
    }
}

/// Origin of a heap allocation produced by [`Inst::HeapAlloc`].
///
/// Mirrors the `AllocationOrigin` axis in the Lean state model
/// (`State/Memory.lean`): it records which runtime owns the allocation so a
/// backend can route the ALLOCATION to its runtime, and an RC op (`Retain` /
/// `Release` / `IsUnique`) on the cell to the runtime that counts it. It does
/// NOT license lowering an `Inst::Dealloc` by recovering the origin from
/// dataflow: every `Dealloc` is refused for codegen (G18-1, re-decided
/// 2026-09-27, `lowering-target-subset.md` "Deallocation"). The stack origin
/// is `Alloca` and needs no marker.
///
/// `CleanHeap` and `SwiftHeap` share the same refcount discipline (no
/// origin-sensitive semantic rule distinguishes them — see the Lean
/// `alloc_isInBounds_ignores_origin` / executable parity fixtures); the two
/// variants exist because origin is *provenance*: a Clean-produced module
/// must not claim Swift origins, and the backend frees each through its own
/// runtime.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum AllocOrigin {
    /// Rust global allocator (`__rust_alloc`) — `Box`/`Vec`/`String` backing.
    /// Not reference-counted: it carries no count, `Retain` / `Release` /
    /// `IsUnique` on it are undefined behaviour (SPEC "An ARC operation counts
    /// only a reference-counted cell"), and it is freed by the call its
    /// producer pairs with the allocation (`Dealloc` stays executable in both
    /// engines but is refused for codegen).
    RustHeap,
    /// Swift heap allocation (ARC-managed object storage). A reference-counted
    /// cell: it starts at count 1 and is freed by the `Release` that takes its
    /// count to zero; `Dealloc` of it is undefined behaviour (Lean decides it
    /// for a scalar-typed cell only — see `CleanHeap`).
    SwiftHeap,
    /// C `malloc`. Not reference-counted, exactly like `RustHeap`: the ARC
    /// instructions on it are undefined behaviour, and it is freed by the
    /// producer's `free` call.
    CMalloc,
    /// Clean Perceus reference-counted heap cell (`clean_alloc_ctor` /
    /// `clean_inc` / `clean_dec` runtime). Freed by `Release` reaching
    /// refcount zero, exactly like `SwiftHeap`; `Dealloc` of it is undefined
    /// behaviour — the interpreter's `MemoryState::dealloc` for every such
    /// cell, Lean's `semDealloc` for a scalar-typed one (Lean has no byte
    /// size for an aggregate `HeapAlloc` and refuses it as
    /// `unsupported.layout`; SPEC "A reference-counted cell is released by
    /// `Release`, never by `Dealloc`").
    ///
    /// The RC runtime that counts these cells is PINNED, not inferred from
    /// symbol names: `trust_ir_build::TRUSTED_RC_RUNTIMES` (WS3.21) fixes
    /// `clean_inc` / `clean_dec` / `clean_is_exclusive` to exact signatures,
    /// and the validator refuses any other declaration, definition, global or
    /// symbol address of them. A `CleanHeap` cell never changes owner: passed
    /// into Rust it stays `CleanHeap`, released only through `clean_dec`.
    CleanHeap,
}

impl AllocOrigin {
    /// Whether a heap cell of this origin is REFERENCE-COUNTED: `SwiftHeap`
    /// and `CleanHeap`, never `RustHeap` or `CMalloc`.
    ///
    /// The one statement of the set two SPEC rules read: `Retain` / `Release`
    /// / `IsUnique` are defined only on such a cell ("An ARC operation counts
    /// only a reference-counted cell"), and `Dealloc` of one is undefined
    /// behaviour ("A reference-counted cell is released by `Release`, never
    /// by `Dealloc`"). The reference interpreter decides all four through
    /// this table; Lean's `requireArcRef` / `semDealloc` state it for the
    /// cells `semHeapAlloc` grants `arcRef`.
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::rc_*` (gate 13).
    #[inline]
    #[must_use]
    pub const fn is_reference_counted(self) -> bool {
        matches!(self, AllocOrigin::SwiftHeap | AllocOrigin::CleanHeap)
    }
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum InstG<X> {
    BinOp {
        op: BinOp,
        ty: TyG<X>,
        lhs: ValueId,
        rhs: ValueId,
    },
    UnOp {
        op: UnOp,
        ty: TyG<X>,
        operand: ValueId,
    },
    Overflow {
        op: OverflowOp,
        ty: TyG<X>,
        lhs: ValueId,
        rhs: ValueId,
    },
    ICmp {
        op: ICmpOp,
        ty: TyG<X>,
        lhs: ValueId,
        rhs: ValueId,
    },
    FCmp {
        op: FCmpOp,
        ty: TyG<X>,
        lhs: ValueId,
        rhs: ValueId,
    },
    Cast {
        op: CastOp,
        src_ty: TyG<X>,
        dst_ty: TyG<X>,
        operand: ValueId,
    },

    // Memory
    Load {
        ty: TyG<X>,
        ptr: ValueId,
        volatile: bool,
        align: Option<u64>,
    },
    Store {
        ty: TyG<X>,
        ptr: ValueId,
        value: ValueId,
        volatile: bool,
        align: Option<u64>,
    },
    Alloca {
        ty: TyG<X>,
        count: Option<ValueId>,
        align: Option<u64>,
    },
    /// Run `ty`'s drop glue on the object at `ptr` (Trust wave-DS; given a
    /// meaning by amendment D, `docs/SPEC_RATIFICATIONS.md` §20).
    ///
    /// A PLACE is named the way this IR already names places -- by a pointer, exactly as
    /// [`Inst::Store`] does, typed exactly `Ptr`. No new notion of "where a value lives" is
    /// introduced: a droppable temporary is materialised with [`Inst::Alloca`] and dropped
    /// through the pointer that yields, which is also what rustc's MIR does (its `Drop` names
    /// a local, and the shim maps an alloca to one).
    ///
    /// SEMANTICS (normative, §20 rule 3): a drop RESOLVES through the module drop-glue table
    /// ([`crate::Module::drop_glue`]) to the glue of the one row whose `ty` equals its own,
    /// and a resolved `drop T, %p` IS `call glue(%p)` under the ordinary call rules (call
    /// depth, argument typing, poison at the boundary is UB, a bodyless glue is a host call
    /// or `UnsupportedCall`), yielding no value. It has no effect of its own: it frees
    /// nothing, de-initializes nothing and ends no borrow -- that is MIR's own meaning after
    /// drop elaboration; deadness belongs to `StorageDead` and the producer.
    ///
    /// A drop at a type with NO row is UNRESOLVED (§20 rule 4): it states no destructor, so
    /// it must be refused, never ignored -- dropping is observable (it frees, it runs user
    /// code), and treating it as a no-op would silently model a different program. Both
    /// executable models refuse it (`UnsupportedInstruction`; `unsupported.destructor`), the
    /// default codegen gate refuses it (`UnlowerableForCodegen`), and a consumer that
    /// verifies or lowers a module MUST refuse it (`refuse/drop_unresolved`).
    /// `validate_module` accepts it: a blob older than wire v55 decodes with an empty table,
    /// so its drops keep their v47 standing.
    ///
    /// ONE SPELLING (§20 rule 5, VALIDATED): a drop of a trivially droppable type
    /// ([`Ty::is_trivially_droppable`]) or of a refined type is refused (`NonCanonicalDrop`:
    /// the no-op drop is spelled by absence, a refinement's drop at its base); and a
    /// registered glue is reached ONLY by drop resolution or through its address -- a direct
    /// `Call` / `CallCannotUnwind` / `Invoke`, a `SeqMap` or a panic-site entry naming it is
    /// refused, so every destructor run is a drop site a verifier can find
    /// (`refuse/drop_glue_called_directly`).
    ///
    /// A PLAIN INSTRUCTION, not a terminator, though MIR's `Drop` is one. The shim splits the
    /// block when it lowers this, which is mechanical; making the producer structure its blocks
    /// around every drop would push MIR's terminator convention into a lowering that does not
    /// otherwise have it. A plain drop is a plain call: an unwinding out of its glue continues
    /// to the caller. The drop whose unwinding must enter an in-frame cleanup pad is
    /// [`Inst::DropInvoke`].
    ///
    /// Both spellings of the lowering-target subset exclude it by name until a backend lowers
    /// it (the v5 expansion).
    ///
    /// Binary: instruction tag 57, read-gated on `DROP_INST_FORMAT_VERSION` (v47 on main),
    /// unchanged by §20.
    Drop {
        ty: TyG<X>,
        ptr: ValueId,
    },
    /// Heap allocation: a fresh region of `count` (default 1) elements of `ty`,
    /// owned by `origin`'s runtime, returned as an opaque `Ty::Ptr`. The heap
    /// counterpart to the stack-only `Alloca`. `align` defaults to the natural
    /// alignment of `ty`.
    ///
    /// Who emits it (measured 2026-09-27): not `~/trust`'s producers or Clean,
    /// which spell allocation as a call; but this repo's own `frontend/` MIR
    /// driver does, as `RustHeap` (inline `Box::new_uninit` / `Arc::new`
    /// blocks, immortal literal byte images, enum construction), and Rust drop
    /// glue later releases its `Box`/`Arc` buffers through a CALL to
    /// `__rust_dealloc`. The
    /// format states no layout a lowered `HeapAlloc` passes its allocator, so
    /// that pairing is correct only under the backend's own allocation
    /// convention (trust-cg: `__rust_alloc(size, align)` with its natural-C
    /// element size times `count`). That size matches the `Layout` the drop
    /// glue passes only where the frontend itself sized an `I8`-element block
    /// from rustc's layout; for any other element type (the enum
    /// construction's `Struct`) nothing states that they agree. It is an open
    /// format gap, not a guarantee. `Dealloc` is not a codegen release of a
    /// `HeapAlloc` result (G18-1).
    HeapAlloc {
        ty: TyG<X>,
        count: Option<ValueId>,
        align: Option<u64>,
        origin: AllocOrigin,
    },
    /// Pointer arithmetic. **TrustIr GEP is single-scale array indexing**, not
    /// the multi-scale type-walking GEP of LLVM: every index in `indices` is
    /// scaled by `size_of(pointee_ty)` and indices are summed, so it computes
    /// `base + (Σ indices) * size_of(pointee_ty)`. It does NOT walk struct/array
    /// nesting with per-level scales, and a negative index is UB. Frontends must
    /// therefore lower **struct field access via `ExtractField`/`InsertField`**
    /// (or an explicit byte-offset GEP over an `I8` pointee), not via a nested
    /// GEP index. The Lean model agrees with this flat semantics. See
    /// `docs/binary-format.md` / `interpret.rs` for the operational rule.
    GEP {
        pointee_ty: TyG<X>,
        base: ValueId,
        indices: Vec<ValueId>,
        /// LLVM `inbounds`: the computed address is asserted to stay within the
        /// same allocation as `base` (poison/UB otherwise). A claim-style backend
        /// hint enabling no-wrap GEP folding (fast-3). Defaults to `false`
        /// (conservative) for legacy modules and the bare constructor.
        #[cfg_attr(feature = "serde", serde(default))]
        inbounds: bool,
    },
    /// Extract the data-address lane from a pointer-like value.
    ///
    /// For thin pointers this is the provenance-preserving identity of the
    /// pointer address. For fat pointers this extracts only the data pointer,
    /// leaving metadata available through `PtrMetadata`.
    PtrData {
        ptr_ty: TyG<X>,
        ptr: ValueId,
    },
    /// Extract the metadata lane from a pointer-like value.
    ///
    /// Fat slice/str metadata is the target pointer-sized unsigned integer;
    /// trait-object metadata is a thin vtable pointer. Thin pointer-like
    /// values carry unit metadata.
    PtrMetadata {
        ptr_ty: TyG<X>,
        metadata_ty: TyG<X>,
        ptr: ValueId,
    },
    /// Rebuild a pointer-like value from a data pointer and metadata.
    ///
    /// This is the structured target for Rust MIR wide-pointer coercions and
    /// `ptr::from_raw_parts`-style normalization.
    PtrFromParts {
        ptr_ty: TyG<X>,
        metadata_ty: TyG<X>,
        data: ValueId,
        metadata: ValueId,
    },

    // Atomics
    AtomicLoad {
        ty: TyG<X>,
        ptr: ValueId,
        ordering: Ordering,
    },
    AtomicStore {
        ty: TyG<X>,
        ptr: ValueId,
        value: ValueId,
        ordering: Ordering,
    },
    AtomicRMW {
        op: AtomicRMWOp,
        ty: TyG<X>,
        ptr: ValueId,
        value: ValueId,
        ordering: Ordering,
    },
    CmpXchg {
        ty: TyG<X>,
        ptr: ValueId,
        expected: ValueId,
        desired: ValueId,
        success: Ordering,
        failure: Ordering,
        /// Trust (crystal D3): a WEAK compare-and-exchange (LLVM `cmpxchg weak`, rustc's
        /// `atomic_cxchgweak`). It may FAIL SPURIOUSLY: even when the loaded value equals
        /// `expected` it may leave memory unchanged and report `false`. A strong one never
        /// does, so a strong CAS is a valid IMPLEMENTATION of a weak one (codegen may emit
        /// either), but modelling a weak one as strong DELETES executions -- the unsound
        /// direction for a proof. Every executable model that cannot represent that
        /// nondeterminism must therefore REFUSE a weak CAS rather than step it as strong:
        /// the reference interpreter and the Lean executable model both do. `false` (the
        /// default for legacy modules and serde) is the historical strong instruction, whose
        /// text, binary, serde encoding and semantics are unchanged byte for byte: the field is
        /// the variant's TRAILING one and is skipped when `false` (the `ParamAttrs::sret`
        /// precedent -- a trailing field is the only one positional MessagePack lets skip).
        #[cfg_attr(feature = "serde", serde(default, skip_serializing_if = "is_false"))]
        weak: bool,
    },
    Fence {
        ordering: Ordering,
    },

    // Control flow
    Br {
        target: BlockId,
        args: Vec<ValueId>,
    },
    CondBr {
        cond: ValueId,
        then_target: BlockId,
        then_args: Vec<ValueId>,
        else_target: BlockId,
        else_args: Vec<ValueId>,
    },
    Switch {
        value: ValueId,
        default: BlockId,
        default_args: Vec<ValueId>,
        cases: Vec<SwitchCase>,
        /// A PRODUCER-ASSERTED, ZERO-AUTHORITY hint that the `default` arm is
        /// dead because the cases cover every value the selector can take.
        ///
        /// The validator (`trust-ir-build`, `validate::exhaustive_switch`,
        /// roadmap WS2.6) checks ONLY this, and nothing more:
        /// 1. `default_args` is empty, the `default` block has no parameters
        ///    and its body is exactly `[Unreachable]`, and the case values are
        ///    distinct as selector values (`ExhaustiveSwitchDefaultReachable`);
        /// 2. when the selector's definition (through `Copy` and `zext` /
        ///    `sext` / equal-width `bitcast` widenings) is the tag lane
        ///    (`ExtractField` field 0) of a `Ty::Enum` value in the same
        ///    function, every case value is one of that enum's discriminants
        ///    (carried through the same casts) and every omitted discriminant
        ///    belongs to a variant `Module::variant_is_uninhabited` proves
        ///    uninhabited (`ExhaustiveSwitchCasesIncomplete`).
        ///
        /// When the selector's provenance does not resolve (a block parameter,
        /// a call result, a plain integer, a narrowing cast), only (1) is
        /// checked, so the flag on a validated module does NOT establish that
        /// the case set is exhaustive. A verifier MUST NOT use it as a fact
        /// without re-deriving the case set. (The Trust producer sets it from a
        /// TyCtxt-vetted check; that is the producer's claim, not the
        /// format's.) Text carries it as the trailing ` exhaustive` keyword
        /// of the `switch` line (WS4.5); its absence reads `false`.
        #[cfg_attr(feature = "serde", serde(default))]
        exhaustive_enum_unreachable: bool,
    },
    Call {
        callee: FuncId,
        args: Vec<ValueId>,
    },
    /// Indirect call through a first-class callee value.
    ///
    /// # Two callee shapes, one instruction (G18-2)
    ///
    /// * **`Ty::Func(s)`** — a bare function pointer. `s` must equal `sig`, and
    ///   `args` must match `func_types[sig]` exactly. Unchanged.
    /// * **`Ty::Closure(c)`** — a first-class closure. `sig` must equal
    ///   `closure_types[c].func`, the closure's APPARENT signature (what a
    ///   caller sees), and `args` is checked against it by that same rule. The
    ///   captured environment is NOT in `args`: it is supplied by the ABI as
    ///   LEADING arguments, spread in capture order, so the target function's
    ///   physical signature must be `captures ++ apparent params -> apparent
    ///   returns`.
    ///
    /// The closure mode exists because `Ty::Closure` was otherwise
    /// INTRODUCTION-ONLY — constructible via `Const` + `InsertField`,
    /// projectable via `ExtractField` (which reads a CAPTURE, never the `func`
    /// lane), and applicable by nothing. Spreading the captures rather than
    /// passing one env pointer follows the format's own model: `ClosureTy`
    /// states captures as N explicit typed values, and there is no env object
    /// in the value model to point at. A producer that wants the pointer-env
    /// ABI keeps spelling it as an explicit env struct plus a `Ty::Func`
    /// pointer.
    ///
    /// Semantics: `crate::interpret::Interpreter::execute_closure_call`.
    /// Validation: `CallIndirectClosureSigMismatch` /
    /// `CallIndirectClosureTargetMismatch` in `trust-ir-build`. The closure
    /// callee mode is deliberately OUTSIDE the lowering-target conformance
    /// subset until the Lean model grows a closure-application case — see
    /// `lowering-target-subset.md`, structural condition 4.
    CallIndirect {
        callee: ValueId,
        sig: crate::value::FuncTyId,
        args: Vec<ValueId>,
        /// Calling convention of the (dynamically-resolved) callee. A direct
        /// `Call`'s convention is the callee `Function`'s `calling_conv`; an
        /// indirect call has no statically-known callee, so it declares the
        /// expected ABI here for the backend to lower the call edge correctly.
        ///
        /// RATIFIED (abi-pinning enforcement layer): direct `Call` carries no
        /// per-call conv override — its edge convention IS the callee
        /// declaration, so a redundant field could only ever agree or lie.
        /// For `CallIndirect`, `validate_module` cross-checks this declared
        /// conv (and the declared `sig`) against the callee-side declaration
        /// wherever the pointer's provenance is statically visible.
        ///
        /// Defaults to `CallingConv::C` for legacy modules: the binary codec
        /// version-gates this field (absent before v12) and the text parser
        /// omits `cc=` for the default, so serde deserialization of pre-v12
        /// JSON/MessagePack (which lacks the key/element) must default it too —
        /// otherwise an old blob fails with "missing field `calling_conv`".
        #[cfg_attr(feature = "serde", serde(default))]
        calling_conv: crate::CallingConv,
    },
    Return {
        values: Vec<ValueId>,
    },

    // Aggregates
    ExtractField {
        ty: TyG<X>,
        aggregate: ValueId,
        field: u32,
    },
    InsertField {
        ty: TyG<X>,
        aggregate: ValueId,
        field: u32,
        value: ValueId,
    },
    ExtractElement {
        ty: TyG<X>,
        array: ValueId,
        index: ValueId,
    },
    InsertElement {
        ty: TyG<X>,
        array: ValueId,
        index: ValueId,
        value: ValueId,
    },

    // Constants
    Const {
        ty: TyG<X>,
        value: ConstantG<X>,
    },
    NullPtr,
    /// Address of a module-level [`Global`](crate::Global) as an SSA pointer.
    ///
    /// Produces an opaque `Ty::Ptr` to the global's storage — static data, a
    /// `&str` literal's backing bytes, or a trait-object vtable. `global`
    /// indexes into [`Module::globals`](crate::Module). This is the in-body
    /// counterpart to the top-level `global @Name` declaration: a frontend
    /// lowers `&STATIC`, string-literal data, and vtable references to it, and
    /// `trust-cg` emits a relocation to the corresponding data/rodata symbol.
    ///
    /// Taking the address is always pure; mutability of the pointee is governed
    /// by the referenced global's `mutable` flag (enforced where the resulting
    /// pointer is stored through, not here).
    GlobalAddr {
        global: GlobalId,
    },
    /// A POISON value of type `ty` (docs/ub-numerics-policy.md §4). Executing
    /// it is not undefined behaviour; INSPECTING the value is — arithmetic, a
    /// comparison or cast, a branch/switch/select condition, a field
    /// projection, a call argument or return, a strict (volatile/atomic)
    /// store. It may be transported (`Copy`, a `Select` arm, a plain `Store`,
    /// a block argument). It is not an input source or a nondeterministic
    /// choice: no value is ever observed through it. The reference interpreter
    /// models scalar poison only and fails closed on a non-scalar `ty`.
    Undef {
        ty: TyG<X>,
    },

    // Proof
    Assume {
        cond: ValueId,
    },
    /// A runtime check: execution continues iff `cond` is `true`; `false`
    /// is a panic. `kind` names WHICH Rust panic (plan item P, wire v52;
    /// [`AssertKind`]); [`AssertKind::Unspecified`] — every pre-v52 assert —
    /// is a check of unknown identity. `site` (amendment P, wire v54;
    /// [`PanicSite`]) names the entry a failed check calls and the location
    /// it reports; a faithful lowering refuses an assert without one
    /// (`docs/SPEC_RATIFICATIONS.md` §19.1). A failed assert is a TERMINAL
    /// panic outcome: the reference engines never execute the entry.
    ///
    /// Serde always emits `kind` and skips an absent `site` (its sole
    /// trailing skipped field); documents written without either still
    /// decode. Binary: tag 29 is the kindless, siteless assert at every
    /// version, tag 63 a kinded siteless one (v52), tag 66 a sited one of any
    /// kind (v54).
    Assert {
        cond: ValueId,
        #[cfg_attr(feature = "serde", serde(default))]
        kind: AssertKind,
        #[cfg_attr(feature = "serde", serde(default, skip_serializing_if = "no_site"))]
        site: Option<PanicSite>,
    },
    Unreachable,

    // Pseudo
    Copy {
        ty: TyG<X>,
        operand: ValueId,
    },
    Select {
        ty: TyG<X>,
        cond: ValueId,
        then_val: ValueId,
        else_val: ValueId,
    },
    /// Structural element-wise constant increment of a sequence: `SeqMapAddK { seq, k }`
    /// produces a new sequence with every element incremented by the constant `k`
    /// (Aeneas's `loopFwd` for `for x in &mut l { *x += k }`). A CORE instruction with
    /// FIXED canonical semantics (like `BinOp(Add)`), so the give-back elaborator can
    /// OBSERVE it (not name-trust a dialect op) and synthesize the loop backward function
    /// (map `λx. x - k`), certified by the kernel `listMap_roundTrip` induction law for
    /// any reversible element operation (`k = 1` is the canonical `*x += 1` case).
    SeqMapAddK {
        /// The sequence type (`Ty::Sequence(_)`).
        ty: TyG<X>,
        /// The sequence value whose elements are incremented.
        seq: ValueId,
        /// The constant added to every element (`1` for `*x += 1`).
        k: u64,
    },
    /// Structural element-wise boolean flip of a sequence: `SeqMapNot { seq }` produces a
    /// new sequence with every element negated (`Bool.not`), i.e. Aeneas's `loopFwd` for
    /// `for b in &mut l { *b = !*b }`. A SECOND element-op alongside [`Inst::SeqMapAddK`]
    /// proving the loop instruction is not `+k`-locked: `Bool.not` is self-inverse, so the
    /// backward function is `map not`, certified by the kernel `boolNotLoop_roundTrip`
    /// theorem (an instance of the type-polymorphic `listMapT_roundTrip`).
    SeqMapNot {
        /// The sequence type (`Ty::Sequence(_)` over `Bool`).
        ty: TyG<X>,
        /// The sequence value whose elements are negated.
        seq: ValueId,
    },
    /// Structural element-wise map of a sequence by a REVERSIBLE element function:
    /// `SeqMap { ty, seq, fwd }` produces a new sequence with `fwd`'s forward semantics
    /// applied to every element (Aeneas's `loopFwd` for `for x in &mut l { *x = fwd(x) }`).
    /// The GENERAL element-op loop instruction — `fwd` is a first-class [`FuncId`]
    /// referencing the single-`&mut` element function `fn(&mut elem)` (its Aeneas forward
    /// view is `elem -> elem`), where `elem` is the pointee of `ty = Ty::Sequence(elem)`.
    ///
    /// Give-back: `fwd`'s own give-back is separately synthesized + certified by the
    /// scalar tier; the loop backward function is `map (giveback fwd)`, certified by ONE
    /// application of the kernel `listMapT_roundTrip` law to `fwd`'s round-trip — no new
    /// metatheory (see `designs/2026-06-30-general-seqmap-instruction.md`). The fixed
    /// specializations [`Inst::SeqMapAddK`] (`fwd = (+k)`) and [`Inst::SeqMapNot`]
    /// (`fwd = not`) remain as the smallest wire forms for the ubiquitous cases.
    SeqMap {
        /// The sequence type (`Ty::Sequence(elem)`).
        ty: TyG<X>,
        /// The sequence value whose elements are mapped.
        seq: ValueId,
        /// The element operation: a single-`&mut` function `fn(&mut elem)` whose
        /// give-back must be independently certifiable for the loop to certify.
        fwd: FuncId,
    },

    // Borrow instructions: an allocation-keyed PERMISSION machine (Lean
    // `Semantics/Borrow.lean`; the interpreter's live-borrow count, read only
    // by `Dealloc`). Not Rust's reference semantics: a Rust producer spells a
    // reference as the place's address (or a `Copy` of it) and emits none of
    // the three (`docs/SPEC_RATIFICATIONS.md`, "A Rust reference carries no
    // permission instruction"; `InstShape::uses_borrow_permissions`).
    Borrow {
        ptr: ValueId,
    },
    BorrowMut {
        ptr: ValueId,
    },
    EndBorrow {
        borrow_ptr: ValueId,
    },

    // ARC instructions (Swift / Clean reference counting model). Defined only
    // on a reference-counted cell: a live `HeapAlloc { origin: SwiftHeap |
    // CleanHeap }` result. On any other live allocation (a stack `Alloca`, a
    // `RustHeap` or `CMalloc` cell, a global's reservation) each of the three
    // is undefined behaviour in the interpreter and in Lean (`requireArcRef`);
    // the engines agree while the pointer's address lies inside the allocation
    // it was derived from (SPEC "An ARC operation counts only a
    // reference-counted cell"). Wire-legal and well-formed either way: the
    // rule is dynamic.
    Retain {
        ptr: ValueId,
    },
    Release {
        ptr: ValueId,
    },
    IsUnique {
        ptr: ValueId,
    },

    // Release of a region: executable in the interpreter and Lean on a stack
    // `Alloca`, a global's reservation, or a `RustHeap` / `CMalloc` cell;
    // UNDEFINED BEHAVIOUR on a `SwiftHeap` / `CleanHeap` cell (the interpreter
    // for every such cell, Lean for a scalar-typed one — an aggregate
    // `HeapAlloc` is `unsupported.layout` there; a reference-counted cell is
    // released by the `Release` that takes its count to zero, never by this
    // instruction); refused for codegen in every body (G18-1). A Rust `Box` drop is a `__rust_dealloc` CALL.
    Dealloc {
        ptr: ValueId,
    },

    /// Bulk byte copy with a DYNAMIC count (WS3.20, F-057): `memcpy` /
    /// `memmove`. Copies `bytes` bytes from `src` to `dst`, carrying for every
    /// byte its VALUE, its INIT STATE (an uninitialized source byte stays
    /// uninitialized at the destination — copy-propagates-poison, exactly as a
    /// non-strict `Load`+`Store` of a scalar image does) and the POINTER
    /// PROVENANCE of any pointer stored in the range (a pointer copied through
    /// it still dereferences). It is the format's replacement for the
    /// `RegionHavocStore` marker a producer had to emit for
    /// `ptr::copy_nonoverlapping` / `copy_from_slice` with a runtime length —
    /// a real operation with semantics, never a havoc.
    ///
    /// Operand typing (`trust-ir-build`): `dst` and `src` are pointer-like
    /// (`OperandNotPointer`); `bytes` is exactly `Usize` when the module
    /// pins a target and exactly `U64` when it does not
    /// (`OperandTypeMismatch`); a handle- or dialect-typed operand is refused
    /// by the nominal transport rule (`InvalidHandleUse`), so a sealed handle
    /// slot can never be copied through it.
    ///
    /// Undefined behaviour (the reference interpreter FAULTS, the Lean model
    /// answers `ub`): either range out of the bounds of a live allocation, and
    /// — when `overlap` is `false` (`memcpy`) — source and destination ranges
    /// that overlap. With `overlap: true` (`memmove`) an overlapping copy is
    /// defined and behaves as if through a temporary. `bytes == 0` is a no-op
    /// even with a dangling or null pointer. Alignment is not asserted: the
    /// copy is byte-granular. The obligation a producer attaches is an
    /// `InBounds`-class `MemorySafety` obligation per site, never a havoc.
    /// Text: `memcopy ptr %dst, ptr %src, %bytes` / `memcopy overlap …`.
    /// Wire: Inst tag 61, read-gated on v51 (the INST wire batch): the three
    /// operands, then `overlap` as a 0/1 byte.
    MemCopy {
        dst: ValueId,
        src: ValueId,
        /// The byte count: `Usize` (or `U64` with no target info).
        bytes: ValueId,
        /// `true` = `memmove` semantics (overlapping ranges are defined);
        /// `false` = `memcpy` (overlap is UB).
        overlap: bool,
    },
    /// Bulk byte fill with a DYNAMIC count (WS3.20, F-057): `memset` /
    /// `ptr::write_bytes`. Writes `byte` (exactly `U8`) to each of `bytes`
    /// bytes starting at `dst`; every written byte is INITIALIZED and carries
    /// no provenance (a pointer whose bytes are overwritten is destroyed, as
    /// under a byte store). Out-of-bounds is UB (the interpreter faults);
    /// `bytes == 0` is a no-op. Same operand typing as [`Inst::MemCopy`]
    /// (`dst` pointer-like, `byte` exactly `U8`, `bytes` exactly `Usize` /
    /// `U64`). Text: `memset ptr %dst, %byte, %bytes`. Wire: Inst tag 62,
    /// read-gated on v51 (the INST wire batch): the three operands.
    MemSet {
        dst: ValueId,
        /// The fill value: exactly `U8`.
        byte: ValueId,
        /// The byte count: `Usize` (or `U64` with no target info).
        bytes: ValueId,
    },

    // Binding frames (typed SSA frames for quantifier lowering).
    //
    // Fixes the Cranelift JIT `\E` / `\A` ceiling: bindings get lowered in
    // TrustIr via four instructions, not as an implicit backend construct. See
    // `designs/2026-04-18-ty-supremacy-trust-ir-scope.md` §R4.
    //
    // Ownership discipline:
    //   - `OpenFrame` declares a fresh `BindingFrameDef` (inline) and
    //     produces a frame-handle SSA value of type `Ptr`.
    //   - `BindSlot { frame, slot, value }` writes `value` into slot `slot`
    //     of `frame` and produces a *new* frame handle (SSA: frames are
    //     immutable; each bind yields a new value).
    //   - `LoadSlot { frame, slot, ty }` reads slot `slot` of `frame`; the
    //     declared `ty` must match the slot's type.
    //   - `CloseFrame { frame }` marks the end of a frame's live scope. It
    //     produces no value and has no runtime effect; it is purely a
    //     validation discipline marker (dominator-LIFO nesting).
    //
    // A full quantifier lowering `\E i \in S : P(i)` emits:
    //   %f0  = open_frame #0 {i: I64}
    //   ... loop header branches with %f0 as a block arg ...
    //   %f1  = bind_slot %f0, 0, %i_current
    //   %b   = ... compute P(i) using load_slot %f1, 0 (I64) ...
    //   ... cond_br ...
    //          close_frame %fK  (on each exit path)
    /// Open a new binding frame with the given inline definition.
    ///
    /// Produces a frame-handle value (treated as `Ty::Ptr` for type
    /// propagation; the underlying representation is backend-chosen).
    OpenFrame {
        /// Inline frame layout — slot names and types.
        def: BindingFrameDef,
    },
    /// Bind a slot in a frame; returns a new frame-handle.
    ///
    /// `BindSlot` is functional: the result is a new frame handle whose
    /// slot `slot` has been set to `value`. Previous frame handles remain
    /// valid; loading from them returns their prior slot values. Backends
    /// lower this to an in-place write when the previous handle is not
    /// otherwise used (standard SSA destination-passing).
    BindSlot {
        frame: ValueId,
        slot: u32,
        value: ValueId,
    },
    /// Load the current value of a slot in a frame.
    ///
    /// `ty` is the declared slot type; validation checks it matches the
    /// frame's `BindingFrameDef.slots[slot].ty`.
    LoadSlot {
        frame: ValueId,
        slot: u32,
        ty: TyG<X>,
    },
    /// Close a binding frame.
    ///
    /// Produces no value. Its sole role is to mark the end of a frame's
    /// live scope for dominator-LIFO nesting validation. A frame handle
    /// passed to `CloseFrame` must not be used by any subsequent
    /// `BindSlot` / `LoadSlot` on the same control-flow path.
    CloseFrame {
        frame: ValueId,
    },

    // Coroutine suspend point (state-machine lowering; trust-ir#coroutines §1).
    //
    // `CoroSuspend` is the single coroutine-specific primitive. It is a
    // TERMINATOR that models one `yield`: it saves the resume STATE INDEX into
    // the coroutine FRAME, then returns the yielded value to the resumer.
    //
    // Operationally it is exactly:
    //     store i64 `next_state` into `frame[state_slot]`   (the frame's state index)
    //     return `value`
    // where `frame` is a pointer to the caller-owned coroutine frame (an
    // explicit on-stack aggregate of `{ state_index, live-across-suspend locals }`)
    // and `state_slot` is the I64-element index of the state field in that frame.
    //
    // The matched `resume` entry dispatches on `frame[state_slot]` with a
    // `Switch` to the continuation block, so a 2-state generator is
    //     resume:  state = load frame[state_slot]; switch state { 0 => k0, .. }
    //     k0:      coro_suspend frame, state_slot, next=1, value=%y
    //
    // Backends lower `CoroSuspend` by macro-expanding it into the already-verified
    // `GEP(frame, state_slot)` + `Store(next_state)` + `Return(value)` sequence,
    // so its correctness reduces to those per-instruction lowering proofs. This
    // keeps coroutines free of any new machine-level codegen.
    //
    // Because it IS a return, it is typed like one: `value` must have the
    // function's single return type (a suspend in a function that does not
    // return exactly one value is `ReturnArityMismatch`, a yield of another
    // type `ReturnTypeMismatch` — the `Return` rule, shared), and `frame` must
    // be pointer-like (`OperandNotPointer`, the GEP-base rule).
    CoroSuspend {
        /// Pointer to the coroutine frame (caller-owned on-stack aggregate).
        /// Must be pointer-like.
        frame: ValueId,
        /// I64-element index of the resume state field within the frame.
        state_slot: u32,
        /// Resume state index to record before returning (which continuation the
        /// next `resume` dispatches to).
        next_state: i64,
        /// The yielded value handed back to the resumer. Must have the
        /// function's single return type.
        value: ValueId,
    },

    // Exception-handling instructions (zero-cost table-driven unwinding;
    // trust-ir#exceptions §1). These are the trust-ir front of the EXISTING,
    // verified trust-cg MachIR EH backend (LSDA + compact-unwind): the backend
    // already lowers a throwing call to a `Bl` whose PC range is recorded in the
    // function's call-site table, and a landing pad to a block the unwinder
    // diverts to with the exception object in the platform ABI register. These
    // three opcodes carry exactly the structural intent that backend needs.
    //
    // `Invoke` is a CALL with two control-flow successors — the Itanium / LLVM
    // `invoke` instruction. It calls `callee(args)`:
    //   * on a NORMAL return, the callee's return values bind this instruction's
    //     own results (the same value-producing shape as `Inst::Call`), and
    //     control transfers to `normal_dest` passing `normal_args`. Because the
    //     result is only defined on the normal edge, it may be consumed in
    //     `normal_args` or where that exact normal edge dominates the use.
    //     Domination by the invoking block alone is insufficient (a backend
    //     splitting the normal edge keeps the result copy on that edge);
    //   * if the callee THROWS (unwinds), the host unwinder diverts control to
    //     `unwind_dest` — a block that BEGINS with an `Inst::LandingPad`.
    //
    // It is a TERMINATOR with successors {normal_dest, unwind_dest}. The backend
    // lowers it to the same `Bl` a `Call` lowers to, plus a branch to
    // `normal_dest`, and records an EH call-site entry pointing at `unwind_dest`.
    Invoke {
        /// The function being invoked.
        callee: FuncId,
        /// Call arguments.
        args: Vec<ValueId>,
        /// Continuation on a normal (non-throwing) return.
        normal_dest: BlockId,
        /// Block arguments passed to `normal_dest` on the normal edge.
        normal_args: Vec<ValueId>,
        /// Landing-pad block entered if the callee unwinds.
        unwind_dest: BlockId,
    },

    // `LandingPad` is the entry of an exception handler / cleanup block. It is
    // NOT a terminator — it is the first instruction of a block that an
    // `Invoke`'s `unwind_dest` names. The unwinder transfers control here with
    // the exception object pointer and a type selector already in the platform
    // ABI registers (AArch64: X0 / X1); the backend lowers `LandingPad` to reads
    // of those registers into its two results:
    //   results[0] : Ptr — the exception object pointer
    //   results[1] : I32 — the type selector (which catch clause matched)
    //
    // `catch_type_indices` (0 == catch-all, i.e. `catch(...)` / a Rust
    // `catch_unwind` cleanup landing pad) and `is_cleanup` drive the LSDA action
    // table the backend already emits. Both engines execute a pad under
    // `PanicStrategy::Unwind` (amendment D Part 2, `docs/SPEC_RATIFICATIONS.md`
    // §21 rule 5): entered by a taken unwind edge it binds the exception and
    // selector 1 (a clause 0) or 0 (a cleanup pad); a typed clause (any index
    // but 0) is refused; a pad with neither re-propagates. Reached any other
    // way, or under the `Abort` default, it is refused.
    LandingPad {
        /// True if this pad runs cleanup (Drop glue) without catching.
        is_cleanup: bool,
        /// Type indices this pad catches; 0 == catch-all. Empty + `is_cleanup`
        /// is a pure cleanup pad.
        catch_type_indices: Vec<u32>,
    },

    // `Resume` continues unwinding (re-raises the in-flight exception) after a
    // cleanup landing pad has run. It is a TERMINATOR with no successors in this
    // function — the backend lowers it to a call to the unwinder's resume entry
    // (`_Unwind_Resume(exn)`), which transfers control to the next frame's pad.
    // Under `PanicStrategy::Unwind` both engines re-raise the exception whose
    // object is at `exn`'s ADDRESS (any other value is UB; §21 rule 6); under
    // the `Abort` default it is refused.
    Resume {
        /// The exception object pointer obtained from the `LandingPad`.
        exn: ValueId,
    },

    /// A sited [`Inst::Assert`] whose failure must enter an in-frame landing
    /// pad (MIR `UnwindAction::Cleanup` / `Terminate`; amendment P, wire v54,
    /// `docs/SPEC_RATIFICATIONS.md` §19.1 rule 5). A TERMINATOR with
    /// `Invoke`'s successor discipline, successors {`normal_dest`,
    /// `unwind_dest`}: a passing check jumps to `normal_dest(normal_args)`; a
    /// failing one is the sited panic. Under the ratified panic=abort
    /// projection (`PanicStrategy::Abort`, the default;
    /// `docs/ub-numerics-policy.md` §4) the unwind edge is never taken,
    /// exactly as for `Invoke`; under `PanicStrategy::Unwind` a failing check
    /// raises into its own `unwind_dest` (`docs/SPEC_RATIFICATIONS.md` §21).
    /// `unwind_dest` begins with a `LandingPad`. Its site is required. A plain
    /// sited `Assert` is the spelling for `UnwindAction::Continue` /
    /// `Unreachable`.
    AssertInvoke {
        /// The checked condition: the check passes iff it is `true`.
        cond: ValueId,
        /// WHICH panic a failure is (operands read only on failure).
        kind: AssertKind,
        /// The entry a failure calls and the location it reports.
        site: PanicSite,
        /// Continuation when the check passes.
        normal_dest: BlockId,
        /// Block arguments passed to `normal_dest`.
        normal_args: Vec<ValueId>,
        /// Landing-pad block entered if the failure unwinds (only under
        /// `PanicStrategy::Unwind`).
        unwind_dest: BlockId,
    },

    // Dialect op — a namespaced operation belonging to a TrustIr dialect
    // registered in a `DialectRegistry`. Core TrustIr tools round-trip these
    // without knowing their semantics; dialect-aware passes lower them into
    // core instructions (or into another dialect). See `crate::dialect`.
    DialectOp(Box<crate::dialect::DialectInst>),

    /// Build a fully-initialised aggregate VALUE from typed register lanes.
    ///
    /// This is the register-level origination form for struct / tuple /
    /// record / array / enum values. Before it, `Inst::Const` was the only
    /// aggregate originator, and no `Constant` inhabits `Rc<T>` / `&T` /
    /// `&mut T` / `*const T` / `*mut T` (a constant reference has no
    /// provenance, `shape::shape_matches_ty`), so an aggregate with a typed
    /// reference lane had **no register seed at all** — only the memory lane
    /// (`Alloca` + field `Store`s + `Load`) could originate one (F-049,
    /// proof-program row `b6.enum.typed_ref_payload_has_no_register_seed`).
    /// The `Undef` + `InsertField`-chain spelling is not a substitute: it
    /// starts from an uninitialised value, so every intermediate step is a
    /// partially-initialised aggregate.
    ///
    /// Shape, exactly (enforced by `validate_module`, never by this type):
    ///
    /// * `ty` is `Struct` / `Tuple` / `Record` / `Array(_, n)` ⇒ `variant`
    ///   is `None` and `fields` is the declaration-ordered lane list, whose
    ///   length is the lane count and whose operands have **exactly** the
    ///   declared lane types.
    /// * `ty` is `Enum(e)` ⇒ `variant` is `Some(v)` with `v` in range,
    ///   `fields` is variant `v`'s payload in declaration order, and the
    ///   result's discriminant is `discriminants[v]` under the existing
    ///   `[tag, fields..]` value model. Constructing an uninhabited variant
    ///   is refused (`UninhabitedVariantConstructed`).
    /// * Every other `ty` — including `Closure`, `Sequence`, `Set`,
    ///   `FatPtr`, `Vector`, `Dialect`, `Handle` and every scalar — is
    ///   refused with `InvalidMakeAggregate`. Vectors keep `InsertElement`
    ///   and fat pointers keep `PtrFromParts`; a dialect or handle lane rule
    ///   is not designed yet, so it fails closed.
    /// * `ty` is `Array(_, n)` with `n >= 1` lanes that are ALL THE SAME
    ///   register (one lane included) ⇒ refused with
    ///   `NonCanonicalUniformArray`: that is the uniform array `[v; n]`,
    ///   whose one register spelling is [`Inst::ArraySplat`]
    ///   (`docs/SPEC_RATIFICATIONS.md` §3.1, VALIDATED).
    ///
    /// A refined lane (`Ty::Refine`) is consumed under the SAME rule
    /// `InsertField` uses, never a looser one: an unrefined operand for a
    /// refined lane is refused exactly as it is there.
    ///
    /// Total and statically typed: there is no run-time obligation, the
    /// validator rule above IS the side condition. Pure — a fresh value out
    /// of its operands, with no aliasing and no memory effect.
    ///
    /// **One spelling** (`docs/SPEC_RATIFICATIONS.md` §3): `MakeAggregate`
    /// is the canonical spelling for an aggregate with a non-constant lane,
    /// and `Const` stays canonical for an all-constant one. `Undef` +
    /// `InsertField` / `InsertElement` chains remain legal for existing
    /// producers but must not be emitted for new code. This is a PRODUCER
    /// rule (prose-only): the validator does not refuse an all-constant
    /// `MakeAggregate`. The uniform-array case above (§3.1) IS validated.
    ///
    /// WIRE: Inst tag 60, read-gated on wire v51 (the INST wire batch,
    /// `docs/wire-allocation.md`): the type, the variant as a presence byte
    /// plus a v32, then the lane list. Before v51 the binary writer panicked
    /// on it, so a module carrying one had no `stable_digest` and every
    /// digest-keyed check refused it as `ModuleHasNoWireIdentity`; since v51
    /// it is encoded like any other instruction and a module carrying one
    /// has a wire identity. It stays outside the lowering-target subset v3
    /// (`bridge.rs`, `lowering-target-subset.md` addendum 2026-09-19) until a
    /// backend lowering and the enum / record Lean depth land.
    MakeAggregate {
        /// The aggregate type being built. Restricted as above.
        ty: TyG<X>,
        /// The enum variant index, iff `ty` is `Ty::Enum`; `None` otherwise.
        variant: Option<u32>,
        /// One operand per declared lane, in declaration order.
        fields: Vec<ValueId>,
    },
    /// `n` copies of one register value: the array `[value; n]` of type
    /// `ty = Array(e, n)` (text `%r = array_splat [e x n] %v`; wire v50, Inst
    /// tag 59). The register-level twin of [`Constant::Splat`], as
    /// `MakeAggregate` is `Const`'s.
    ///
    /// CONSTANT SIZE in `n`, everywhere: one type and one operand in every
    /// codec; the validator checks the operand's type against `e` once and
    /// never walks `n`; the reference interpreter binds a lazy
    /// `ArrayValue::splat` (O(1)), on which `ExtractElement` /
    /// `InsertElement` cost O(log n) in the persistent rope's height, never
    /// a copy of the array; the Lean model denotes it as
    /// `.aggregate (List.replicate n v)` with the proved law
    /// `ExtractElement i ∘ ArraySplat = v` for `i < n`.
    ///
    /// Shape (enforced by `validate_module`, `InvalidArraySplat`): `ty`
    /// resolves to `Ty::Array(e, n)` (a `Refine` of an array is refused, as
    /// `MakeAggregate` refuses it); `value` has EXACTLY type `e`, consumed
    /// under the rule `InsertElement` applies to its value (a refined element
    /// type is decided by the refinement consumption rule). Total and pure: no
    /// run-time obligation, no memory effect.
    ///
    /// **One spelling** (`docs/SPEC_RATIFICATIONS.md` §3.1, the third instance,
    /// VALIDATED): an `ArraySplat` is canonical iff `n >= 1` — the empty
    /// array has no element to repeat and is the constant `const [e x 0]
    /// array[ ]`. Conversely a `MakeAggregate` over `Array(e, n)` whose `n >=
    /// 1` lane operands are all the SAME value (one lane included) is
    /// non-canonical and must be an `ArraySplat`. Both directions are
    /// `NonCanonicalUniformArray`. (Unlike `Constant::Splat`, whose list
    /// twin `array[ c ]` is canonical for one element, a register array of one
    /// element is an `ArraySplat`: the rule was ratified while its list twin,
    /// `MakeAggregate`, had no wire encoding, precisely so that the INST wire
    /// batch (v51) would change no canonical spelling — and it did not.)
    ArraySplat {
        /// `Ty::Array(e, n)`: the array type built.
        ty: TyG<X>,
        /// The element value every one of the `n` lanes holds.
        value: ValueId,
    },
    /// A direct call with a normative no-crossing unwind boundary. Normal
    /// return has exactly [`Inst::Call`]'s meaning. If the callee starts an
    /// unwind, it MUST NOT propagate through this site: the target must enforce
    /// its non-propagating boundary behavior, or refuse the instruction.
    ///
    /// This is NOT a proof that the callee cannot panic/throw, is pure, or has
    /// no observable effects. A frontend must separately establish fidelity to
    /// its source ABI. The reference and proof-subset interpreters currently
    /// refuse this boundary because they do not model host unwinding.
    /// Appended (rather than inserted beside Call) to preserve serde indices.
    CallCannotUnwind {
        callee: FuncId,
        args: Vec<ValueId>,
    },
    /// The indirect twin of [`Inst::CallCannotUnwind`]. Callee typing, closure
    /// captures, arguments, returns and calling convention follow
    /// [`Inst::CallIndirect`]; only the unwind boundary differs.
    CallIndirectCannotUnwind {
        callee: ValueId,
        sig: crate::value::FuncTyId,
        args: Vec<ValueId>,
        #[cfg_attr(feature = "serde", serde(default))]
        calling_conv: crate::CallingConv,
    },
    /// Run `ty`'s drop glue on the object at `ptr`, with an unwind edge
    /// (amendment D, `docs/SPEC_RATIFICATIONS.md` §20 rule 6; wire v55, Inst
    /// tag 68). The unwinding twin of [`Inst::Drop`], exactly as
    /// [`Inst::Invoke`] is [`Inst::Call`]'s.
    ///
    /// A TERMINATOR with no results and successors {`normal_dest`,
    /// `unwind_dest`}. Resolved through [`crate::Module::drop_glue`] it IS
    /// `Invoke { callee: glue(ty), args: [ptr], normal_dest, normal_args,
    /// unwind_dest }`: the glue runs, then control continues on the normal
    /// edge. An UNRESOLVED one (no row for `ty`) is refused exactly as an
    /// unresolved `Drop` is, never run as a no-op. It takes `Invoke`'s
    /// successor discipline verbatim: `unwind_dest` begins with a
    /// `LandingPad` and differs from `normal_dest`, the unwind edge carries
    /// no arguments, and the function joins
    /// `ModuleValidationReport::unwind_surface`. A consumer must refuse one
    /// whose `unwind_dest` does not begin with a `LandingPad`
    /// (`refuse/drop_invoke_unwind_dest_without_landing_pad`). Under
    /// `PanicStrategy::Abort` (the default; `docs/ub-numerics-policy.md` §4)
    /// the unwind edge is never taken; under `PanicStrategy::Unwind` an
    /// unwinding out of the glue enters `unwind_dest`
    /// (`docs/SPEC_RATIFICATIONS.md` §21).
    ///
    /// Appended (rather than inserted beside `Drop`) to preserve serde
    /// variant indices.
    DropInvoke {
        /// The dropped type; resolves through the module drop-glue table.
        ty: TyG<X>,
        /// The place: a pointer to the object, typed exactly `Ptr`.
        ptr: ValueId,
        /// Continuation after the glue returns normally.
        normal_dest: BlockId,
        /// Block arguments passed to `normal_dest`.
        normal_args: Vec<ValueId>,
        /// Landing-pad block entered if the glue unwinds (only under
        /// `PanicStrategy::Unwind`).
        unwind_dest: BlockId,
    },
    /// [`Inst::CallIndirect`] with an unwind edge (amendment D, Part 2,
    /// `docs/SPEC_RATIFICATIONS.md` §21; wire v56, Inst tag 69): the
    /// unwinding twin of `CallIndirect`, exactly as [`Inst::Invoke`] is
    /// [`Inst::Call`]'s.
    ///
    /// A TERMINATOR with successors {`normal_dest`, `unwind_dest`}. The
    /// callee, `sig`, the arguments, the closure application and the calling
    /// convention follow `CallIndirect` verbatim; the call's results are this
    /// node's results and are defined ON THE NORMAL EDGE ONLY, as `Invoke`'s
    /// are. It takes `Invoke`'s successor discipline verbatim: `unwind_dest`
    /// begins with a `LandingPad` and differs from `normal_dest`, the unwind
    /// edge carries no arguments, and the function joins
    /// `ModuleValidationReport::unwind_surface`. A consumer must refuse one
    /// whose `unwind_dest` does not begin with a `LandingPad`
    /// (`refuse/invoke_indirect_unwind_dest_without_landing_pad`). Under
    /// `PanicStrategy::Abort` (the default) the unwind edge is never taken;
    /// under `PanicStrategy::Unwind` an unwinding out of the callee transfers
    /// to `unwind_dest` (§21).
    ///
    /// Appended (rather than inserted beside `CallIndirect`) to preserve serde
    /// variant indices.
    InvokeIndirect {
        /// The function pointer (or closure) called, as `CallIndirect`'s.
        callee: ValueId,
        /// The apparent signature, as `CallIndirect`'s.
        sig: crate::value::FuncTyId,
        /// Call arguments.
        args: Vec<ValueId>,
        /// The calling convention, as `CallIndirect`'s.
        #[cfg_attr(feature = "serde", serde(default))]
        calling_conv: crate::CallingConv,
        /// Continuation on a normal return.
        normal_dest: BlockId,
        /// Block arguments passed to `normal_dest` (they may use this node's
        /// results).
        normal_args: Vec<ValueId>,
        /// Landing-pad block entered if the callee unwinds.
        unwind_dest: BlockId,
    },
    /// Construct a closure from runtime SSA capture values in declaration order.
    /// The target's physical signature is the declared captures followed by
    /// the apparent parameters, with the apparent return types. No call,
    /// allocation or synthetic reference value is introduced by construction.
    /// Wire v63, Inst tag 70. Existing Constant::Closure remains the constant form.
    MakeClosure {
        ty: crate::value::ClosureTyId,
        func: FuncId,
        captures: Vec<ValueId>,
    },
    /// A general tensor contraction (the tensor region, PKG-U13a; Trust
    /// `docs/design/2026-11-12-one-software.md` §6), in XLA `DotGeneral`'s
    /// shape: matrix multiply is the instance `batch: []`,
    /// `contract: [(1, 0)]`.
    ///
    /// `lhs: tensor<E, p>` and `rhs: tensor<E, q>` share one INTEGER element
    /// type `E`; `ty` is the result `tensor<E, r>`. Each `(a, b)` pair names a
    /// left axis `a < p` and a right axis `b < q`; no axis is named twice on
    /// one side, and `r = |batch| + (p - |batch| - |contract|) + (q - |batch| -
    /// |contract|)`. The result's axes are the batch axes (in pair order),
    /// then the left free axes, then the right free axes (each ascending), and
    /// each result element is the wrapping (`BinOp::Add`/`BinOp::Mul`) sum,
    /// over the contracted multi-index in row-major order starting from 0, of
    /// the products of the paired elements. Paired axes of different extents,
    /// and a result with more elements than `usize` holds, are undefined
    /// behaviour: shape agreement is a precondition of the operation, never a
    /// type. One fuel unit, as every node.
    ///
    /// Text: `tensor_contract tensor<i32, 2> %a, %b batch [] contract [1:0]`.
    /// Wire: Inst tag 71, read-gated on v67 (`TENSOR_FORMAT_VERSION`).
    TensorContract {
        /// The result tensor type.
        ty: TyG<X>,
        lhs: ValueId,
        rhs: ValueId,
        /// Batch axis pairs `(lhs axis, rhs axis)`, in result order.
        batch: Vec<(u32, u32)>,
        /// Contracted axis pairs `(lhs axis, rhs axis)`.
        contract: Vec<(u32, u32)>,
    },
    /// An elementwise tensor map with a scalar body (PKG-U13c; Trust
    /// `docs/design/2026-11-12-one-software.md` §6).
    ///
    /// `ty` is the result `tensor<E, r>`. Each operand is either a tensor
    /// `tensor<E_i, r>` of the result's rank (at least one is) or an integer
    /// or `Bool` scalar, which every coordinate reads. The body is a non-empty
    /// list of [`TensorMapNode`]s over LANES: with `n = args.len()`, lane
    /// `i < n` is operand `i` at the coordinate (a tensor's element there, a
    /// scalar itself), and lane `n + j` is node `j`'s value; node `j` reads
    /// only lanes below `n + j`. Each node is a scalar instruction (`BinOp`,
    /// `UnOp`, `ICmp`, `Select`, `Cast`) with that instruction's typing and
    /// semantics, its verdicts included (a division by zero in a node is that
    /// undefined behaviour). The result element is the LAST node's value, of
    /// type `E`. Tensor operands whose extents differ are undefined
    /// behaviour: shape agreement is a precondition, never a type. The
    /// coordinates run in row-major order. One fuel unit.
    ///
    /// Text: `tensor_map tensor<i32, 1> (%a, %b) { add i32 $0, $1 }`.
    /// Wire: Inst tag 72, read-gated on v68
    /// (`TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION`).
    TensorMap {
        /// The result tensor type.
        ty: TyG<X>,
        /// The operands: tensors of the result's rank, or scalars.
        args: Vec<ValueId>,
        /// The scalar body; the last node is the result element.
        body: Vec<TensorMapNode<X>>,
    },
    /// A tensor reduction (PKG-U13c): `src: tensor<E, s>` reduced over
    /// `axes` (strictly ascending, each below `s`) by `op`, into `ty =
    /// tensor<E, s - |axes|>` whose extents are the source's at the kept
    /// axes, in order. Each result element is a left fold from `op`'s
    /// identity over the reduced multi-index in the order `order` names
    /// ([`TensorReduceOrder::RowMajor`]: row-major, the first reduced axis
    /// outermost), so an empty reduced extent gives the identity. Integer
    /// elements only; no undefined behaviour beyond a poison operand. One
    /// fuel unit.
    ///
    /// Text: `tensor_reduce add tensor<i32, 1> %x axes [1] order row_major`.
    /// Wire: Inst tag 73, read-gated on v68.
    TensorReduce {
        /// The result tensor type.
        ty: TyG<X>,
        /// The reduced tensor.
        src: ValueId,
        /// The combining operator.
        op: TensorReduceOp,
        /// The reduced axes, strictly ascending.
        axes: Vec<u32>,
        /// The fold order.
        order: TensorReduceOrder,
    },
    /// A tensor view given as a coordinate function (PKG-U13c), so reshape,
    /// slice, pad, transpose and broadcast are one instruction.
    ///
    /// `ty` is `tensor<E, r>` and `src` a `tensor<E, s>`. `exprs` is a node
    /// list of [`TensorIndexExpr`]s over the integers, each arithmetic node
    /// reading only nodes before it; `params` are `usize` operands the nodes
    /// read. The result's extents are the values of the `shape` nodes (`r` of
    /// them, none depending on a coordinate); at each result coordinate (row
    /// major), the source coordinate along source axis `j` is the value of
    /// node `index[j]`. Where some source coordinate is outside its axis the
    /// element is `fill` (a scalar `E`), or, with no fill, undefined
    /// behaviour. A node value outside `[-2^127, 2^127)`, a division by zero,
    /// a result extent that is negative or does not fit `usize`, and a result
    /// count at or past `2^pointer_bits` are undefined behaviour. One fuel
    /// unit.
    ///
    /// Text: `tensor_view tensor<i32, 2> %x params [] exprs [src_extent(1),
    /// src_extent(0), coord(1), coord(0)] shape [$0, $1] index [$2, $3]`
    /// (a transpose). Wire: Inst tag 74, read-gated on v68.
    TensorView {
        /// The result tensor type.
        ty: TyG<X>,
        /// The viewed tensor.
        src: ValueId,
        /// The `usize` operands `TensorIndexExpr::Param` reads.
        params: Vec<ValueId>,
        /// The coordinate function's nodes.
        exprs: Vec<TensorIndexExpr>,
        /// The node of each result extent.
        shape: Vec<u32>,
        /// The node of each source coordinate.
        index: Vec<u32>,
        /// The element read where a source coordinate is out of range.
        fill: Option<ValueId>,
    },
    /// A tensor gather in coordinate form (PKG-U13d; Trust
    /// `docs/design/2026-11-12-one-software.md` §6, SPEC_RATIFICATIONS §26).
    ///
    /// `ty` is `tensor<E, r>` and `data` a `tensor<E, s>` with `s >= 1`.
    /// `coords` has exactly `s` operands, one COORDINATE TENSOR per data
    /// axis (axis `j` at position `j`), each a tensor of rank `r` with its
    /// own integer element, read as the integer its type denotes (signed
    /// types two's complement, `isize`/`usize` at the module's pointer
    /// width). The result's extents are the coordinate tensors' (which must
    /// all be equal: undefined behaviour otherwise), and at each result
    /// coordinate `p` (row major) the element is `data`'s at `(coords[0][p],
    /// .., coords[s-1][p])`. A coordinate outside its axis (negative, or at
    /// or past the extent) at any `p` is undefined behaviour: the
    /// instruction's BOUNDS PRECONDITION, stated as a `BoundsCheck`
    /// obligation sited on it. One fuel unit.
    ///
    /// Text: `tensor_gather tensor<i32, 1> %x coords [%c0, %c1]`.
    /// Wire: Inst tag 75, read-gated on v69
    /// (`TENSOR_GATHER_SCATTER_FORMAT_VERSION`).
    TensorGather {
        /// The result tensor type.
        ty: TyG<X>,
        /// The tensor read.
        data: ValueId,
        /// One coordinate tensor per data axis, in axis order.
        coords: Vec<ValueId>,
    },
    /// A tensor scatter in coordinate form (PKG-U13d, SPEC_RATIFICATIONS
    /// §26): `src` written over a copy of `init`.
    ///
    /// `ty` is `tensor<E, s>` with `s >= 1`, `init` has type `ty`, and `src`
    /// is a `tensor<E, r>`. `coords` has exactly `s` operands, one coordinate
    /// tensor per axis of `init` (axis `j` at position `j`), each a tensor of
    /// rank `r` with its own integer element, read as [`InstG::TensorGather`]
    /// reads one. Every coordinate tensor's extents must equal `src`'s, and
    /// every coordinate at every source position must be inside its axis of
    /// `init` (undefined behaviour otherwise, decided before any element is
    /// written; the bounds precondition is a `BoundsCheck` obligation sited
    /// on the instruction). The result has `init`'s extents and starts as
    /// `init`'s elements; then, for each source position `p` in row-major
    /// order, the element at `(coords[0][p], .., coords[s-1][p])` becomes
    /// `src`'s at `p`, so where several positions name one coordinate the
    /// row-major-last write wins. That order is part of the instruction's
    /// meaning, never a scheduling choice. One fuel unit.
    ///
    /// Text: `tensor_scatter tensor<i32, 1> %init, %src coords [%c]`.
    /// Wire: Inst tag 76, read-gated on v69.
    TensorScatter {
        /// The result tensor type (also `init`'s).
        ty: TyG<X>,
        /// The tensor written over.
        init: ValueId,
        /// The elements written.
        src: ValueId,
        /// One coordinate tensor per axis of `init`, in axis order.
        coords: Vec<ValueId>,
    },
}

/// One node of an [`InstG::TensorMap`] body (PKG-U13c): a scalar
/// instruction over the map's LANES (operand elements and earlier nodes),
/// with that instruction's fields, typing and semantics. Wire: the
/// `TensorMapNode` tag space (one tag byte, then the fields in order).
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TensorMapNode<X> {
    /// [`InstG::BinOp`] at lanes `lhs`, `rhs`.
    BinOp {
        op: BinOp,
        ty: TyG<X>,
        lhs: u32,
        rhs: u32,
    },
    /// [`InstG::UnOp`] at lane `operand`.
    UnOp { op: UnOp, ty: TyG<X>, operand: u32 },
    /// [`InstG::ICmp`] at lanes `lhs`, `rhs`; its value is a `Bool`.
    ICmp {
        op: ICmpOp,
        ty: TyG<X>,
        lhs: u32,
        rhs: u32,
    },
    /// [`InstG::Select`] at lanes `cond`, `then_lane`, `else_lane`.
    Select {
        ty: TyG<X>,
        cond: u32,
        then_lane: u32,
        else_lane: u32,
    },
    /// [`InstG::Cast`] at lane `operand`.
    Cast {
        op: CastOp,
        src_ty: TyG<X>,
        dst_ty: TyG<X>,
        operand: u32,
    },
}

impl<X: Clone> TensorMapNode<X> {
    /// The lanes this node reads, in field order.
    #[must_use]
    pub fn lanes(&self) -> Vec<u32> {
        match self {
            TensorMapNode::BinOp { lhs, rhs, .. } | TensorMapNode::ICmp { lhs, rhs, .. } => {
                vec![*lhs, *rhs]
            }
            TensorMapNode::UnOp { operand, .. } | TensorMapNode::Cast { operand, .. } => {
                vec![*operand]
            }
            TensorMapNode::Select {
                cond,
                then_lane,
                else_lane,
                ..
            } => vec![*cond, *then_lane, *else_lane],
        }
    }

    /// The type of this node's value: `ty` for `BinOp`, `UnOp` and `Select`,
    /// `Bool` for `ICmp`, `dst_ty` for `Cast`.
    #[must_use]
    pub fn value_ty(&self) -> TyG<X> {
        match self {
            TensorMapNode::BinOp { ty, .. }
            | TensorMapNode::UnOp { ty, .. }
            | TensorMapNode::Select { ty, .. } => ty.clone(),
            TensorMapNode::ICmp { .. } => TyG::Bool,
            TensorMapNode::Cast { dst_ty, .. } => dst_ty.clone(),
        }
    }
}

impl<X> TensorMapNode<X> {
    /// Every type this node spells, in field order.
    pub fn types(&self) -> Vec<&TyG<X>> {
        match self {
            TensorMapNode::BinOp { ty, .. }
            | TensorMapNode::UnOp { ty, .. }
            | TensorMapNode::ICmp { ty, .. }
            | TensorMapNode::Select { ty, .. } => vec![ty],
            TensorMapNode::Cast { src_ty, dst_ty, .. } => vec![src_ty, dst_ty],
        }
    }
}

impl TensorMapNode<crate::level::NoExt> {
    /// Rule M4's operation half (PKG-U13c, SPEC_RATIFICATIONS §25): whether
    /// this node's operation applies at the types it names, or the reason it
    /// does not. The one statement of the rule: the validator
    /// (`InvalidTensorMap`), the reference interpreter (a type error before
    /// any element is read) and SemR's `mapNodeOpOk` all apply it.
    ///
    /// `BinOp`'s Bool connectives apply only at `Bool`, `and`/`or`/`xor` at
    /// an integer or `Bool`, its arithmetic, division, shifts and rotations
    /// only at an integer; every `UnOp` only at an integer (`not` of a `Bool`
    /// is spelled `bxor`, as the scalar rule says); `ICmp` and `Select` at
    /// any lane type. A cast is `trunc` from an integer to a narrower integer
    /// or `Bool`, `zext`/`sext` from an integer or `Bool` to a wider integer,
    /// or `bitcast` to the same type or between integers of one width, with
    /// `isize`/`usize` at `pointer_bits` (`Bool` is one bit). That cast rule
    /// is stricter than the scalar `Cast` rule, which admits a resize in
    /// either direction: each cast it admits, both engines execute without a
    /// type error. A float operation is refused by name. The caller has
    /// already checked that every type the node names is an integer or `Bool`.
    #[must_use]
    pub fn op_refusal(&self, pointer_bits: u32) -> Option<String> {
        match self {
            TensorMapNode::BinOp { op, ty, .. } => {
                let applies = match op {
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::UDiv
                    | BinOp::SDiv
                    | BinOp::URem
                    | BinOp::SRem
                    | BinOp::Shl
                    | BinOp::LShr
                    | BinOp::AShr
                    | BinOp::RotL
                    | BinOp::RotR => ty.is_integer(),
                    BinOp::BAnd | BinOp::BOr | BinOp::BXor => *ty == Ty::Bool,
                    BinOp::And | BinOp::Or | BinOp::Xor => true,
                    BinOp::FAdd
                    | BinOp::FSub
                    | BinOp::FMul
                    | BinOp::FDiv
                    | BinOp::FRem
                    | BinOp::FMin
                    | BinOp::FMax
                    | BinOp::FCopySign => {
                        return Some(format!("{op} is a float operation"));
                    }
                };
                (!applies).then(|| format!("{op} does not apply at {ty}"))
            }
            TensorMapNode::UnOp { op, ty, .. } => match op {
                UnOp::Neg
                | UnOp::Not
                | UnOp::CtPop
                | UnOp::CtLz
                | UnOp::CtTz
                | UnOp::BSwap
                | UnOp::BitReverse => {
                    (!ty.is_integer()).then(|| format!("{op} does not apply at {ty}"))
                }
                UnOp::FNeg
                | UnOp::FAbs
                | UnOp::FSqrt
                | UnOp::FFloor
                | UnOp::FCeil
                | UnOp::FTrunc => Some(format!("{op} is a float operation")),
            },
            TensorMapNode::ICmp { .. } | TensorMapNode::Select { .. } => None,
            TensorMapNode::Cast {
                op, src_ty, dst_ty, ..
            } => {
                let widths = (
                    src_ty.bit_width_with(pointer_bits),
                    dst_ty.bit_width_with(pointer_bits),
                );
                let applies = match (op, widths) {
                    (CastOp::Trunc, (Some(sw), Some(dw))) => src_ty.is_integer() && sw > dw,
                    (CastOp::ZExt | CastOp::SExt, (Some(sw), Some(dw))) => {
                        dst_ty.is_integer() && sw < dw
                    }
                    (CastOp::Bitcast, (Some(sw), Some(dw))) => {
                        src_ty == dst_ty || (src_ty.is_integer() && dst_ty.is_integer() && sw == dw)
                    }
                    (CastOp::Trunc | CastOp::ZExt | CastOp::SExt | CastOp::Bitcast, _) => false,
                    _ => return Some(format!("{op} is not an integer cast")),
                };
                (!applies).then(|| format!("{op} does not cast {src_ty} to {dst_ty}"))
            }
        }
    }
}

impl<X: crate::level::Extension> core::fmt::Display for TensorMapNode<X> {
    /// The scalar instruction's own text spelling with `$lane` for `%value`.
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TensorMapNode::BinOp { op, ty, lhs, rhs } => write!(f, "{op} {ty} ${lhs}, ${rhs}"),
            TensorMapNode::UnOp { op, ty, operand } => write!(f, "{op} {ty} ${operand}"),
            TensorMapNode::ICmp { op, ty, lhs, rhs } => {
                write!(f, "icmp {op} {ty} ${lhs}, ${rhs}")
            }
            TensorMapNode::Select {
                ty,
                cond,
                then_lane,
                else_lane,
            } => write!(f, "select {ty} ${cond}, ${then_lane}, ${else_lane}"),
            TensorMapNode::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => write!(f, "{op} {src_ty} ${operand} to {dst_ty}"),
        }
    }
}

/// The combining operator of an [`InstG::TensorReduce`] (PKG-U13c), on
/// integer elements: `Add`/`Mul` wrap as `BinOp::Add`/`BinOp::Mul` do;
/// `And`/`Or`/`Xor` are bitwise; `SMin`/`SMax` compare signed and
/// `UMin`/`UMax` unsigned. Wire: the `TensorReduceOp` tag space, in this
/// order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TensorReduceOp {
    Add,
    Mul,
    And,
    Or,
    Xor,
    SMin,
    SMax,
    UMin,
    UMax,
}

impl TensorReduceOp {
    /// Every operator, in tag order.
    pub const ALL: [TensorReduceOp; 9] = [
        TensorReduceOp::Add,
        TensorReduceOp::Mul,
        TensorReduceOp::And,
        TensorReduceOp::Or,
        TensorReduceOp::Xor,
        TensorReduceOp::SMin,
        TensorReduceOp::SMax,
        TensorReduceOp::UMin,
        TensorReduceOp::UMax,
    ];

    /// The text spelling (`add`, `mul`, `and`, `or`, `xor`, `smin`, `smax`,
    /// `umin`, `umax`).
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            TensorReduceOp::Add => "add",
            TensorReduceOp::Mul => "mul",
            TensorReduceOp::And => "and",
            TensorReduceOp::Or => "or",
            TensorReduceOp::Xor => "xor",
            TensorReduceOp::SMin => "smin",
            TensorReduceOp::SMax => "smax",
            TensorReduceOp::UMin => "umin",
            TensorReduceOp::UMax => "umax",
        }
    }
}

impl core::fmt::Display for TensorReduceOp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.name())
    }
}

/// The fold order of an [`InstG::TensorReduce`] (PKG-U13c). The order is part
/// of the instruction, never a scheduling choice (Trust
/// `docs/design/2026-11-12-one-software.md` §6.1, Exact). Wire: the
/// `TensorReduceOrder` tag space.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TensorReduceOrder {
    /// A left fold from the identity over the reduced multi-index in
    /// row-major order, the first reduced axis outermost.
    RowMajor,
}

impl core::fmt::Display for TensorReduceOrder {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            TensorReduceOrder::RowMajor => "row_major",
        })
    }
}

/// One node of an [`InstG::TensorView`]'s coordinate function (PKG-U13c):
/// an integer, over the unbounded integers. An arithmetic node names the ids
/// of two earlier nodes. `Div` and `Rem` are Euclidean (the remainder is in
/// `[0, |divisor|)`). Wire: the `TensorIndexExpr` tag space.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum TensorIndexExpr {
    /// A literal.
    Lit(u64),
    /// The `usize` operand `params[k]`, unsigned.
    Param(u32),
    /// The source's extent along axis `j`.
    SrcExtent(u32),
    /// The result coordinate along axis `i`.
    Coord(u32),
    Add(u32, u32),
    Sub(u32, u32),
    Mul(u32, u32),
    /// Euclidean quotient.
    Div(u32, u32),
    /// Euclidean remainder.
    Rem(u32, u32),
    Min(u32, u32),
    Max(u32, u32),
}

impl TensorIndexExpr {
    /// The node ids an arithmetic node reads (none for an atom).
    #[must_use]
    pub const fn operands(self) -> Option<(u32, u32)> {
        match self {
            TensorIndexExpr::Lit(_)
            | TensorIndexExpr::Param(_)
            | TensorIndexExpr::SrcExtent(_)
            | TensorIndexExpr::Coord(_) => None,
            TensorIndexExpr::Add(a, b)
            | TensorIndexExpr::Sub(a, b)
            | TensorIndexExpr::Mul(a, b)
            | TensorIndexExpr::Div(a, b)
            | TensorIndexExpr::Rem(a, b)
            | TensorIndexExpr::Min(a, b)
            | TensorIndexExpr::Max(a, b) => Some((a, b)),
        }
    }

    /// The text name of an arithmetic node, or of an atom.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            TensorIndexExpr::Lit(_) => "lit",
            TensorIndexExpr::Param(_) => "param",
            TensorIndexExpr::SrcExtent(_) => "src_extent",
            TensorIndexExpr::Coord(_) => "coord",
            TensorIndexExpr::Add(..) => "add",
            TensorIndexExpr::Sub(..) => "sub",
            TensorIndexExpr::Mul(..) => "mul",
            TensorIndexExpr::Div(..) => "div",
            TensorIndexExpr::Rem(..) => "rem",
            TensorIndexExpr::Min(..) => "min",
            TensorIndexExpr::Max(..) => "max",
        }
    }
}

impl core::fmt::Display for TensorIndexExpr {
    /// `lit(3)`, `param(0)`, `src_extent(1)`, `coord(0)`, `add($0, $1)`.
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            TensorIndexExpr::Lit(n) => write!(f, "lit({n})"),
            TensorIndexExpr::Param(k)
            | TensorIndexExpr::SrcExtent(k)
            | TensorIndexExpr::Coord(k) => {
                write!(f, "{}({k})", self.name())
            }
            other => {
                let (a, b) = other.operands().unwrap_or_default();
                write!(f, "{}(${a}, ${b})", other.name())
            }
        }
    }
}

/// Which nodes of a [`InstG::TensorView`]'s coordinate function are
/// INDEX-PHASE (PKG-U13c): a `Coord` node, and an arithmetic node with an
/// index-phase operand. Every other node is shape-phase: it has one value for
/// the whole view. An operand id at or past its own node's (a malformed
/// list) reads as shape-phase here; the validator refuses it separately.
#[must_use]
pub fn tensor_view_index_phase(exprs: &[TensorIndexExpr]) -> Vec<bool> {
    let mut phase: Vec<bool> = Vec::with_capacity(exprs.len());
    for expr in exprs {
        let index = match *expr {
            TensorIndexExpr::Coord(_) => true,
            other => other.operands().is_some_and(|(a, b)| {
                phase.get(a as usize).copied().unwrap_or(false)
                    || phase.get(b as usize).copied().unwrap_or(false)
            }),
        };
        phase.push(index);
    }
    phase
}

/// The level-R instruction: [`InstG`] with no extension.
pub type Inst = InstG<crate::level::NoExt>;

impl<X> InstG<X> {
    /// The panic site of a sited check (amendment P, wire v54): `Some` for an
    /// [`Inst::Assert`] carrying one and for every [`Inst::AssertInvoke`],
    /// `None` for everything else.
    #[must_use]
    pub fn panic_site(&self) -> Option<&PanicSite> {
        match self {
            InstG::Assert { site, .. } => site.as_ref(),
            InstG::AssertInvoke { site, .. } => Some(site),
            _ => None,
        }
    }
}

/// Semantic unwind disposition of a non-terminating call. Not a NoPanic fact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CallUnwindDisposition {
    /// The existing ordinary-call behavior; no additional boundary contract.
    Propagate,
    /// An unwind must not cross this call site. Enforce it or refuse it.
    CannotUnwind,
}

/// Borrowed callee shape; indirect signatures and conventions stay explicit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallTarget {
    Direct(FuncId),
    Indirect {
        callee: ValueId,
        sig: crate::value::FuncTyId,
        calling_conv: crate::CallingConv,
    },
}

/// Which kind of control-flow edge an [`Edge`] is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EdgeKind {
    /// An ordinary transfer: a branch, a switch arm, or an invoke's normal
    /// continuation. It may carry block arguments.
    Normal,
    /// An invoke-family instruction's landing-pad edge, taken only when the
    /// operation unwinds. It carries no block arguments (the pad's two
    /// results are the unwinder's registers). Both engines take it under
    /// `PanicStrategy::Unwind` only (`docs/SPEC_RATIFICATIONS.md` §21); under
    /// the `Abort` default, the panic=abort projection, neither does
    /// (`docs/ub-numerics-policy.md` §4).
    Unwind,
}

/// One CFG edge a terminator leaves its block by ([`Inst::successor_edges`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Edge<'a> {
    /// The block entered.
    pub target: BlockId,
    /// The block arguments passed on this edge (always empty on an
    /// [`EdgeKind::Unwind`] edge).
    pub args: &'a [ValueId],
    /// Whether this is a normal or an unwind edge.
    pub kind: EdgeKind,
}

/// One allocation-free view of the four non-terminating call variants.
/// Consumers must preserve `unwind`; this view does not license erasing it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallShape<'a> {
    pub target: CallTarget,
    pub args: &'a [ValueId],
    pub unwind: CallUnwindDisposition,
}

variant_shape! {
    /// The payload-free shape of an [`Inst`]: its variant, as a `Copy` value.
    ///
    /// Decision tables over instructions are stated over this type, because a
    /// table over `&Inst` is not provable in the verified lane (see
    /// `variant_shape!`). The projection [`Inst::shape`] is generated from the
    /// same list as this enum, so a new `Inst` variant is a compile error here
    /// until it is listed — and then every table below must place it.
    pub enum InstShape for Inst {
        BinOp,
        UnOp,
        Overflow,
        ICmp,
        FCmp,
        Cast,
        Load,
        Store,
        Alloca,
        Drop,
        HeapAlloc,
        GEP,
        PtrData,
        PtrMetadata,
        PtrFromParts,
        AtomicLoad,
        AtomicStore,
        AtomicRMW,
        CmpXchg,
        Fence,
        Br,
        CondBr,
        Switch,
        Call,
        CallIndirect,
        Return,
        ExtractField,
        InsertField,
        ExtractElement,
        InsertElement,
        Const,
        NullPtr,
        GlobalAddr,
        Undef,
        Assume,
        Assert,
        Unreachable,
        Copy,
        Select,
        SeqMapAddK,
        SeqMapNot,
        SeqMap,
        Borrow,
        BorrowMut,
        EndBorrow,
        Retain,
        Release,
        IsUnique,
        Dealloc,
        MemCopy,
        MemSet,
        OpenFrame,
        BindSlot,
        LoadSlot,
        CloseFrame,
        CoroSuspend,
        Invoke,
        LandingPad,
        Resume,
        AssertInvoke,
        DialectOp,
        MakeAggregate,
        ArraySplat,
        CallCannotUnwind,
        CallIndirectCannotUnwind,
        DropInvoke,
        InvokeIndirect,
        MakeClosure,
        TensorContract,
        TensorMap,
        TensorReduce,
        TensorView,
        TensorGather,
        TensorScatter,
    }
}

impl InstShape {
    /// Whether an instruction of this shape is a TERMINATOR: it ends its
    /// basic block, and a block ends in exactly one.
    ///
    /// The eleven terminators are the control transfers (`Br`, `CondBr`,
    /// `Switch`, `Return`, `Unreachable`), the coroutine yield (`CoroSuspend`,
    /// a `GEP` + `Store` + `Return` macro-expansion) and the five exception
    /// edges (`Invoke`, `Resume`, `AssertInvoke`, a sited check with an
    /// unwind edge, `DropInvoke`, a drop with one, and `InvokeIndirect`, an
    /// indirect call with one). `LandingPad` is NOT one: it heads a block.
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::terminator_*`, one Trust
    /// contract per shape, kernel-rechecked under `scripts/verified_contracts.py`
    /// (gate 13), whose trust-ir mutants flip them.
    #[inline]
    #[must_use]
    pub const fn is_terminator(self) -> bool {
        matches!(
            self,
            InstShape::Br
                | InstShape::CondBr
                | InstShape::Switch
                | InstShape::Return
                | InstShape::CoroSuspend
                | InstShape::Invoke
                | InstShape::DropInvoke
                | InstShape::InvokeIndirect
                | InstShape::Resume
                | InstShape::AssertInvoke
                | InstShape::Unreachable
        )
    }

    /// Whether an instruction of this shape drives the allocation-keyed
    /// PERMISSION machine: `Borrow`, `BorrowMut` and `EndBorrow`, and nothing
    /// else.
    ///
    /// In the normative interpreter that machine is a live-borrow count that
    /// only `Dealloc` reads (`docs/SPEC_RATIFICATIONS.md`, "Freeing an
    /// allocation under a live borrow is undefined behaviour"); in Lean it is
    /// `Permission` (`Semantics/Borrow.lean`). It is not the semantics of a
    /// Rust reference, so a Rust producer emits none of the three (SPEC "A Rust
    /// reference carries no permission instruction"): the validator refuses
    /// one in a function stamped [`crate::Producer::TRust`], and so does the
    /// bundle check, both through this table. A
    /// `Copy` is not here: it never touches permissions or memory (Lean
    /// `stepInst_copy_preserves_memory_and_permissions`).
    ///
    /// PROVED, every cell: `trust_ir_laws::laws::borrow_permission_*`, one
    /// Trust contract per shape, kernel-rechecked under
    /// `scripts/verified_contracts.py` (gate 13), whose trust-ir mutants flip
    /// them.
    #[inline]
    #[must_use]
    pub const fn uses_borrow_permissions(self) -> bool {
        matches!(
            self,
            InstShape::Borrow | InstShape::BorrowMut | InstShape::EndBorrow
        )
    }
}

// At every level: the writer's block arm, which a module blob (level R) and
// a template blob (level S) share, consults it.
impl<X> InstG<X> {
    /// The construct that keeps this instruction OFF THE BINARY WIRE, if any:
    /// a variant (or a sub-op) that exists in the enums but whose wire tag has
    /// not landed yet. The binary writer's block arm consults this list and
    /// refuses such a node by name (`BinarySink::refuse`, D1a), so a module
    /// carrying one has no `stable_digest`; the one pre-check every
    /// digest-keyed entry point runs, [`crate::Module::wire_image_refusal`],
    /// IS that writer (`trust_ir_build::wire_identity_blocker`,
    /// `ModuleHasNoWireIdentity`; the CLI's `convert --format bin`).
    ///
    /// **Empty since wire v51.** The INST wire batch gave its ten members —
    /// `MakeAggregate` (Inst tag 60), `MemCopy` (61), `MemSet` (62), the
    /// `RotL`/`RotR`/`FCopySign` BinOp tags 23..=25 and the `CtLz`/`CtTz`/
    /// `BSwap`/`BitReverse` UnOp tags 9..=12 — real tags, so every
    /// instruction a producer can build now has a binary spelling and this
    /// answers `None` for all of them (`wire_census` samples every variant
    /// through the real writer; only `Ty::Error` and the feature-gated
    /// `ProofAnnotation::Goal` stay `UNENCODABLE`). It stays the ONE probe
    /// list, available in every feature configuration unlike the `binary`
    /// module's spelling: a future variant landed ahead of its tag gets an arm
    /// here, and the writer — hence every pre-check — picks it up without a
    /// second edit.
    #[must_use]
    pub fn binary_wire_gap(&self) -> Option<&'static str> {
        let _ = self;
        None
    }
}

impl Inst {
    /// Inspect a non-terminating call without cloning operands or losing its
    /// normative boundary. Invoke's distinct CFG edges are not projected here.
    #[must_use]
    pub fn call_shape(&self) -> Option<CallShape<'_>> {
        let (target, args, unwind) = match self {
            Self::Call { callee, args } => (
                CallTarget::Direct(*callee),
                args,
                CallUnwindDisposition::Propagate,
            ),
            Self::CallCannotUnwind { callee, args } => (
                CallTarget::Direct(*callee),
                args,
                CallUnwindDisposition::CannotUnwind,
            ),
            Self::CallIndirect {
                callee,
                sig,
                args,
                calling_conv,
            }
            | Self::CallIndirectCannotUnwind {
                callee,
                sig,
                args,
                calling_conv,
            } => (
                CallTarget::Indirect {
                    callee: *callee,
                    sig: *sig,
                    calling_conv: *calling_conv,
                },
                args,
                if matches!(self, Self::CallIndirectCannotUnwind { .. }) {
                    CallUnwindDisposition::CannotUnwind
                } else {
                    CallUnwindDisposition::Propagate
                },
            ),
            _ => return None,
        };
        Some(CallShape {
            target,
            args,
            unwind,
        })
    }
    /// Try to visit every SSA value consumed by this instruction, stopping at
    /// the first [`ControlFlow::Break`].
    ///
    /// Function, block, global, and binding-frame definition identifiers are
    /// not SSA operands. This is the canonical exhaustive operand walk for
    /// core TrustIr instructions; both full visitors and first-match queries
    /// delegate here so opcode coverage and early-exit behavior cannot drift.
    pub fn try_visit_value_operands<B>(
        &self,
        mut visit: impl FnMut(ValueId) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        macro_rules! try_visit {
            ($operand:expr) => {
                if let ControlFlow::Break(output) = visit($operand) {
                    return ControlFlow::Break(output);
                }
            };
        }

        match self {
            // Trust (wave-DS): the dropped POINTER is a real operand -- it keeps the alloca
            // live and must be renumbered/remapped with every other value use, or a splice
            // would drop through a stale id.
            Inst::Drop { ptr, .. } => {
                try_visit!(*ptr);
            }
            // Amendment D: the dropped pointer, then the normal-edge
            // arguments (the unwind edge carries none).
            Inst::DropInvoke {
                ptr, normal_args, ..
            } => {
                try_visit!(*ptr);
                for &argument in normal_args {
                    try_visit!(argument);
                }
            }
            Inst::BinOp { lhs, rhs, .. }
            | Inst::Overflow { lhs, rhs, .. }
            | Inst::ICmp { lhs, rhs, .. }
            | Inst::FCmp { lhs, rhs, .. } => {
                try_visit!(*lhs);
                try_visit!(*rhs);
            }
            // SeqMap's `fwd` is a FuncId, not an SSA operand.
            Inst::SeqMapAddK { seq, .. }
            | Inst::SeqMapNot { seq, .. }
            | Inst::SeqMap { seq, .. } => try_visit!(*seq),
            Inst::UnOp { operand, .. }
            | Inst::Cast { operand, .. }
            | Inst::Copy { operand, .. } => try_visit!(*operand),
            Inst::Load { ptr, .. }
            | Inst::PtrData { ptr, .. }
            | Inst::PtrMetadata { ptr, .. }
            | Inst::AtomicLoad { ptr, .. }
            | Inst::Borrow { ptr }
            | Inst::BorrowMut { ptr }
            | Inst::Retain { ptr }
            | Inst::Release { ptr }
            | Inst::IsUnique { ptr }
            | Inst::Dealloc { ptr } => try_visit!(*ptr),
            Inst::Store { ptr, value, .. }
            | Inst::AtomicStore { ptr, value, .. }
            | Inst::AtomicRMW { ptr, value, .. } => {
                try_visit!(*ptr);
                try_visit!(*value);
            }
            Inst::MemCopy {
                dst, src, bytes, ..
            } => {
                try_visit!(*dst);
                try_visit!(*src);
                try_visit!(*bytes);
            }
            Inst::MemSet { dst, byte, bytes } => {
                try_visit!(*dst);
                try_visit!(*byte);
                try_visit!(*bytes);
            }
            Inst::Alloca { count, .. } | Inst::HeapAlloc { count, .. } => {
                if let Some(count) = count {
                    try_visit!(*count);
                }
            }
            Inst::GEP { base, indices, .. } => {
                try_visit!(*base);
                for &index in indices {
                    try_visit!(index);
                }
            }
            Inst::PtrFromParts { data, metadata, .. } => {
                try_visit!(*data);
                try_visit!(*metadata);
            }
            Inst::CmpXchg {
                ptr,
                expected,
                desired,
                ..
            } => {
                try_visit!(*ptr);
                try_visit!(*expected);
                try_visit!(*desired);
            }
            Inst::Br { args, .. }
            | Inst::Call { args, .. }
            | Inst::CallCannotUnwind { args, .. } => {
                for &argument in args {
                    try_visit!(argument);
                }
            }
            Inst::CondBr {
                cond,
                then_args,
                else_args,
                ..
            } => {
                try_visit!(*cond);
                for &argument in then_args {
                    try_visit!(argument);
                }
                for &argument in else_args {
                    try_visit!(argument);
                }
            }
            Inst::Switch {
                value,
                default_args,
                cases,
                ..
            } => {
                try_visit!(*value);
                for &argument in default_args {
                    try_visit!(argument);
                }
                for case in cases {
                    for &argument in &case.args {
                        try_visit!(argument);
                    }
                }
            }
            Inst::CallIndirect { callee, args, .. }
            | Inst::CallIndirectCannotUnwind { callee, args, .. } => {
                try_visit!(*callee);
                for &argument in args {
                    try_visit!(argument);
                }
            }
            Inst::Return { values } => {
                for &value in values {
                    try_visit!(value);
                }
            }
            Inst::MakeAggregate { fields, .. }
            | Inst::MakeClosure {
                captures: fields, ..
            } => {
                for &field in fields {
                    try_visit!(field);
                }
            }
            // ONE operand, visited once: the lane count is in the type.
            Inst::ArraySplat { value, .. } => try_visit!(*value),
            // The two tensors, in field order; the axis pairs are not values.
            Inst::TensorContract { lhs, rhs, .. } => {
                try_visit!(*lhs);
                try_visit!(*rhs);
            }
            // The operands in order; the body's lanes are not values.
            Inst::TensorMap { args, .. } => {
                for &argument in args {
                    try_visit!(argument);
                }
            }
            Inst::TensorReduce { src, .. } => try_visit!(*src),
            // The source, the parameters in order, then the fill.
            Inst::TensorView {
                src, params, fill, ..
            } => {
                try_visit!(*src);
                for &param in params {
                    try_visit!(param);
                }
                if let Some(fill) = fill {
                    try_visit!(*fill);
                }
            }
            // The data, then the coordinate tensors in axis order.
            Inst::TensorGather { data, coords, .. } => {
                try_visit!(*data);
                for &coord in coords {
                    try_visit!(coord);
                }
            }
            // The initial tensor, the source, then the coordinate tensors.
            Inst::TensorScatter {
                init, src, coords, ..
            } => {
                try_visit!(*init);
                try_visit!(*src);
                for &coord in coords {
                    try_visit!(coord);
                }
            }
            Inst::ExtractField { aggregate, .. } => try_visit!(*aggregate),
            Inst::InsertField {
                aggregate, value, ..
            } => {
                try_visit!(*aggregate);
                try_visit!(*value);
            }
            Inst::ExtractElement { array, index, .. } => {
                try_visit!(*array);
                try_visit!(*index);
            }
            Inst::InsertElement {
                array,
                index,
                value,
                ..
            } => {
                try_visit!(*array);
                try_visit!(*index);
                try_visit!(*value);
            }
            Inst::Assume { cond } => try_visit!(*cond),
            // Amendment P: the condition, then the kind's operands, then a
            // run-time (`Value`) location; `AssertInvoke` then its edge args.
            Inst::Assert { cond, kind, site } => {
                try_visit!(*cond);
                if let Some(operands) = kind.operands() {
                    for operand in operands {
                        try_visit!(operand);
                    }
                }
                if let Some(location) = site.as_ref().and_then(PanicSite::location_value) {
                    try_visit!(location);
                }
            }
            Inst::AssertInvoke {
                cond,
                kind,
                site,
                normal_args,
                ..
            } => {
                try_visit!(*cond);
                if let Some(operands) = kind.operands() {
                    for operand in operands {
                        try_visit!(operand);
                    }
                }
                if let Some(location) = site.location_value() {
                    try_visit!(location);
                }
                for &argument in normal_args {
                    try_visit!(argument);
                }
            }
            Inst::Select {
                cond,
                then_val,
                else_val,
                ..
            } => {
                try_visit!(*cond);
                try_visit!(*then_val);
                try_visit!(*else_val);
            }
            Inst::EndBorrow { borrow_ptr } => try_visit!(*borrow_ptr),
            Inst::BindSlot { frame, value, .. } | Inst::CoroSuspend { frame, value, .. } => {
                try_visit!(*frame);
                try_visit!(*value);
            }
            Inst::LoadSlot { frame, .. } | Inst::CloseFrame { frame } => try_visit!(*frame),
            Inst::Invoke {
                args, normal_args, ..
            } => {
                for &argument in args {
                    try_visit!(argument);
                }
                for &argument in normal_args {
                    try_visit!(argument);
                }
            }
            // Amendment D, Part 2: `CallIndirect`'s operands, then the
            // normal-edge arguments (the unwind edge carries none).
            Inst::InvokeIndirect {
                callee,
                args,
                normal_args,
                ..
            } => {
                try_visit!(*callee);
                for &argument in args {
                    try_visit!(argument);
                }
                for &argument in normal_args {
                    try_visit!(argument);
                }
            }
            Inst::Resume { exn } => try_visit!(*exn),
            Inst::DialectOp(operation) => {
                for &operand in &operation.operands {
                    try_visit!(operand);
                }
            }
            Inst::Fence { .. }
            | Inst::Const { .. }
            | Inst::NullPtr
            | Inst::GlobalAddr { .. }
            | Inst::Undef { .. }
            | Inst::Unreachable
            | Inst::OpenFrame { .. }
            | Inst::LandingPad { .. } => {}
        }

        ControlFlow::Continue(())
    }

    /// Visit every SSA value consumed by this instruction.
    ///
    /// Function, block, global, and binding-frame definition identifiers are
    /// not SSA operands.  This is the canonical exhaustive operand walk for
    /// core TrustIr instructions; consumers should use it instead of
    /// maintaining a second opcode match that can drift when instructions are
    /// added.
    pub fn visit_value_operands(&self, mut visit: impl FnMut(ValueId)) {
        let _: ControlFlow<()> = self.try_visit_value_operands(|operand| {
            visit(operand);
            ControlFlow::Continue(())
        });
    }

    /// Whether this instruction consumes `value` as an SSA operand.
    #[must_use]
    pub fn uses_value(&self, value: ValueId) -> bool {
        self.try_visit_value_operands(|operand| {
            if operand == value {
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(())
            }
        })
        .is_break()
    }

    /// Required condition type for a select producing `value_ty`.
    pub fn required_select_condition_ty(value_ty: &Ty) -> Ty {
        value_ty.select_condition_ty()
    }

    /// Required condition type for this instruction, if it is a select.
    pub fn select_condition_ty(&self) -> Option<Ty> {
        match self {
            Inst::Select { ty, .. } => Some(Self::required_select_condition_ty(ty)),
            _ => None,
        }
    }

    /// Validate a typed select condition without accepting physical integer
    /// masks as if they were logical TrustIr masks.
    pub fn validate_select_condition_ty(
        select_ty: &Ty,
        cond_ty: &Ty,
    ) -> Result<(), SelectConditionTypeError> {
        let expected_cond_ty = Self::required_select_condition_ty(select_ty);
        if cond_ty == &expected_cond_ty {
            return Ok(());
        }

        if cond_ty.is_integer_vector_mask_for_select_ty(select_ty) {
            return Err(
                SelectConditionTypeError::PhysicalIntegerMaskRequiresCompareToZero {
                    select_ty: select_ty.clone(),
                    mask_ty: cond_ty.clone(),
                    expected_cond_ty,
                },
            );
        }

        Err(SelectConditionTypeError::TypeMismatch {
            select_ty: select_ty.clone(),
            expected_cond_ty,
            actual_cond_ty: cond_ty.clone(),
        })
    }

    /// Returns true if the instruction is a terminator (ends a basic block).
    ///
    /// The table is [`InstShape::is_terminator`], whose every cell is a
    /// proved Trust contract; this is its by-reference spelling.
    #[inline]
    pub fn is_terminator(&self) -> bool {
        self.shape().is_terminator()
    }

    /// Whether the instruction drives the permission machine (`Borrow`,
    /// `BorrowMut`, `EndBorrow`).
    ///
    /// The table is [`InstShape::uses_borrow_permissions`], whose every cell is
    /// a proved Trust contract; this is its by-reference spelling, and the one
    /// predicate the Rust-reference rule's two checks read.
    #[inline]
    #[must_use]
    pub fn uses_borrow_permissions(&self) -> bool {
        self.shape().uses_borrow_permissions()
    }

    /// Every CFG edge this instruction leaves its block by, in the canonical
    /// order [`crate::analysis::DominatorTree::edge_dominates`] numbers them:
    /// `Br` 0; `CondBr` then/else 0/1; `Switch` cases in order, then the
    /// default; an invoke-family terminator normal/unwind 0/1.
    ///
    /// EXHAUSTIVE: every variant is listed and there is no wildcard arm, so a
    /// new terminator is a compile error here rather than a silent sink in a
    /// CFG walk that defaulted it to "no successors" (fail-open: its targets
    /// would go unchecked and unreached). Every in-repo CFG walk reads its
    /// edges from here. A non-terminator answers empty, as do the
    /// terminators that leave the function (`Return`, `Resume`,
    /// `Unreachable`, and `CoroSuspend`, a `GEP` + `Store` + `Return`
    /// expansion).
    #[must_use]
    pub fn successor_edges(&self) -> Vec<Edge<'_>> {
        fn normal<'a>(target: &BlockId, args: &'a [ValueId]) -> Edge<'a> {
            Edge {
                target: *target,
                args,
                kind: EdgeKind::Normal,
            }
        }
        match self {
            Inst::Br { target, args } => vec![normal(target, args)],
            Inst::CondBr {
                then_target,
                then_args,
                else_target,
                else_args,
                ..
            } => vec![
                normal(then_target, then_args),
                normal(else_target, else_args),
            ],
            Inst::Switch {
                default,
                default_args,
                cases,
                ..
            } => cases
                .iter()
                .map(|case| normal(&case.target, &case.args))
                .chain(core::iter::once(normal(default, default_args)))
                .collect(),
            Inst::Invoke {
                normal_dest,
                normal_args,
                unwind_dest,
                ..
            }
            | Inst::AssertInvoke {
                normal_dest,
                normal_args,
                unwind_dest,
                ..
            }
            | Inst::DropInvoke {
                normal_dest,
                normal_args,
                unwind_dest,
                ..
            }
            | Inst::InvokeIndirect {
                normal_dest,
                normal_args,
                unwind_dest,
                ..
            } => vec![
                normal(normal_dest, normal_args),
                Edge {
                    target: *unwind_dest,
                    args: &[],
                    kind: EdgeKind::Unwind,
                },
            ],
            Inst::Return { .. }
            | Inst::Resume { .. }
            | Inst::Unreachable
            | Inst::CoroSuspend { .. }
            | Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::Load { .. }
            | Inst::Store { .. }
            | Inst::Alloca { .. }
            | Inst::Drop { .. }
            | Inst::HeapAlloc { .. }
            | Inst::GEP { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::PtrFromParts { .. }
            | Inst::AtomicLoad { .. }
            | Inst::AtomicStore { .. }
            | Inst::AtomicRMW { .. }
            | Inst::CmpXchg { .. }
            | Inst::Fence { .. }
            | Inst::Call { .. }
            | Inst::CallIndirect { .. }
            | Inst::ExtractField { .. }
            | Inst::InsertField { .. }
            | Inst::ExtractElement { .. }
            | Inst::InsertElement { .. }
            | Inst::Const { .. }
            | Inst::NullPtr
            | Inst::GlobalAddr { .. }
            | Inst::Undef { .. }
            | Inst::Assume { .. }
            | Inst::Assert { .. }
            | Inst::Copy { .. }
            | Inst::Select { .. }
            | Inst::SeqMapAddK { .. }
            | Inst::SeqMapNot { .. }
            | Inst::SeqMap { .. }
            | Inst::Borrow { .. }
            | Inst::BorrowMut { .. }
            | Inst::EndBorrow { .. }
            | Inst::Retain { .. }
            | Inst::Release { .. }
            | Inst::IsUnique { .. }
            | Inst::Dealloc { .. }
            | Inst::MemCopy { .. }
            | Inst::MemSet { .. }
            | Inst::OpenFrame { .. }
            | Inst::BindSlot { .. }
            | Inst::LoadSlot { .. }
            | Inst::CloseFrame { .. }
            | Inst::LandingPad { .. }
            | Inst::DialectOp(_)
            | Inst::MakeAggregate { .. }
            | Inst::MakeClosure { .. }
            | Inst::ArraySplat { .. }
            | Inst::TensorContract { .. }
            | Inst::TensorMap { .. }
            | Inst::TensorReduce { .. }
            | Inst::TensorView { .. }
            | Inst::TensorGather { .. }
            | Inst::TensorScatter { .. }
            | Inst::CallCannotUnwind { .. }
            | Inst::CallIndirectCannotUnwind { .. } => Vec::new(),
        }
    }

    /// The unwind successor, if this instruction has one: the landing-pad
    /// block of an invoke-family terminator (`Invoke`, `AssertInvoke`,
    /// `DropInvoke`, `InvokeIndirect`).
    /// Exactly the target of its [`EdgeKind::Unwind`] edge in
    /// [`Inst::successor_edges`].
    #[must_use]
    pub fn unwind_dest(&self) -> Option<BlockId> {
        self.successor_edges()
            .into_iter()
            .find(|edge| edge.kind == EdgeKind::Unwind)
            .map(|edge| edge.target)
    }

    /// The check identity of an [`Inst::Assert`] or [`Inst::AssertInvoke`]:
    /// its condition and kind. `None` for every other instruction.
    #[must_use]
    pub fn assert_check(&self) -> Option<(ValueId, &AssertKind)> {
        match self {
            Inst::Assert { cond, kind, .. } | Inst::AssertInvoke { cond, kind, .. } => {
                Some((*cond, kind))
            }
            _ => None,
        }
    }

    /// Returns true if the instruction has *observable effects* — effects on
    /// the world (or on other observers) beyond producing its SSA result.
    ///
    /// An instruction with observable effects MUST NOT be removed by dead-code
    /// elimination even if its result is unused, because removing it would
    /// change the program's observable behavior. This is the soundness-critical
    /// predicate DCE consults.
    ///
    /// Observable effects include:
    /// - Memory writes (Store, AtomicStore, AtomicRMW, CmpXchg, Fence)
    /// - Volatile loads — a volatile [`Inst::Load`] is an observable access to
    ///   a memory location whose reads matter to other observers (MMIO, signal
    ///   handlers); the C/LLVM memory model forbids removing it even when the
    ///   loaded value is dead.
    /// - Atomic loads ([`Inst::AtomicLoad`]) — they synchronize-with other
    ///   threads (an `Acquire`/`SeqCst` load establishes a happens-before edge
    ///   and a `SeqCst` load participates in the single total order), so they
    ///   are observable regardless of ordering and must not be elided. We flag
    ///   every ordering, including `Relaxed`, because a relaxed atomic load is
    ///   still a synchronization-visible read of a shared location and the
    ///   conservative choice is sound; only a non-atomic, non-volatile plain
    ///   load is freely removable.
    /// - Calls (may have arbitrary effects)
    /// - Assertions (may trap)
    /// - Terminators (control flow)
    /// - Borrow/BorrowMut/EndBorrow (modify the permission map)
    /// - Retain/Release (modify reference counts)
    /// - DialectOp (opaque; conservatively flagged until lowered)
    pub fn has_observable_effects(&self) -> bool {
        match self {
            // Trust (wave-DS): a DROP runs a destructor -- it frees, and it can run arbitrary
            // user code. It is the definition of an observable effect and must never be
            // removable.
            Inst::Drop { .. } => true,
            // Memory writes and deallocation. The bulk ops (WS3.20) WRITE
            // `bytes` bytes of the destination: exactly as observable as a
            // `Store`, and they produce no SSA result a use count could keep
            // alive, so this arm is the only thing that keeps DCE off them.
            Inst::Store { .. }
            | Inst::AtomicStore { .. }
            | Inst::AtomicRMW { .. }
            | Inst::CmpXchg { .. }
            | Inst::Fence { .. }
            | Inst::Dealloc { .. }
            | Inst::MemCopy { .. }
            | Inst::MemSet { .. } => true,

            // Volatile plain loads are observable accesses (MMIO / signal
            // visibility): the C/LLVM memory model forbids eliding them even
            // when the loaded value is dead. Non-volatile plain loads are pure
            // with respect to DCE.
            Inst::Load { volatile, .. } => *volatile,

            // Atomic loads synchronize-with other threads and (for SeqCst)
            // participate in a single total order. They are observable for
            // every ordering — eliding one can break a happens-before edge —
            // so DCE must never remove them.
            Inst::AtomicLoad { .. } => true,

            // Calls (conservatively side-effecting)
            Inst::Call { .. }
            | Inst::CallIndirect { .. }
            | Inst::CallCannotUnwind { .. }
            | Inst::CallIndirectCannotUnwind { .. } => true,

            // SeqMap invokes an arbitrary element function per element — a call
            // in disguise, so it is conservatively observable exactly like a
            // Call (the fixed-semantics SeqMapAddK/SeqMapNot stay pure).
            Inst::SeqMap { .. } => true,

            // Assertions may trap
            Inst::Assert { .. } => true,

            // Borrow instructions modify the permission map. The row reads the
            // proved table (`InstShape::uses_borrow_permissions`); the variants
            // stay listed because this match is exhaustive.
            inst @ (Inst::Borrow { .. } | Inst::BorrowMut { .. } | Inst::EndBorrow { .. }) => {
                inst.uses_borrow_permissions()
            }

            // ARC instructions modify reference counts
            Inst::Retain { .. } | Inst::Release { .. } => true,

            // Binding-frame close is a discipline marker; DCE must not drop
            // it or dominator-LIFO nesting validation is lost.
            //
            // OpenFrame / BindSlot / LoadSlot are pure SSA ops: they produce
            // values. If their results are unused, DCE may remove them
            // because the absence of an OpenFrame also removes the matching
            // CloseFrame's referent (validation rejects CloseFrame of an
            // undefined frame before DCE).
            Inst::CloseFrame { .. } => true,

            // A landing pad is the structural entry of an exception handler /
            // cleanup block; the unwinder transfers control to it and leaves the
            // exception object in an ABI register. It must never be removed even
            // when its produced values are unused — eliding it would drop the
            // handler the LSDA points at.
            Inst::LandingPad { .. } => true,

            // Dialect ops have opaque semantics by design — conservatively
            // flag them as side-effecting so DCE does not remove them. Passes
            // that know a specific dialect may rewrite these to pure core
            // instructions before DCE runs.
            Inst::DialectOp(_) => true,

            // Terminators are side-effecting (control flow). Listed
            // explicitly rather than via `_ if self.is_terminator()`, because a
            // guarded arm does not count toward exhaustiveness — with a guard
            // here the compiler cannot tell that the match below is total.
            Inst::Br { .. }
            | Inst::CondBr { .. }
            | Inst::Switch { .. }
            | Inst::Return { .. }
            | Inst::CoroSuspend { .. }
            | Inst::Invoke { .. }
            | Inst::Resume { .. }
            | Inst::AssertInvoke { .. }
            | Inst::DropInvoke { .. }
            | Inst::InvokeIndirect { .. }
            | Inst::Unreachable => true,

            // ---------------------------------------------------------------
            // PURE. Everything below produces its SSA result and nothing else.
            //
            // These arms are written out one variant at a time ON PURPOSE.
            // This match is EXHAUSTIVE — there is deliberately no `_` arm — so
            // that adding a variant to `Inst` is a COMPILE ERROR here until
            // somebody classifies it.
            //
            // The previous `_ => false` made "pure" the silent default, which
            // is the unsafe direction for BOTH consumers of this predicate:
            //   - DCE reads `false` as "safe to delete";
            //   - the THIR/MIR differential reads `false` as "safe to admit
            //     into the comparison" (a `true` here is what makes it refuse).
            // A new effectful instruction therefore became deletable AND
            // comparable at once, with no diagnostic. Do not reintroduce a
            // catch-all; classify the variant instead.
            // ---------------------------------------------------------------

            // Arithmetic, comparison, conversion, selection — value -> value.
            Inst::BinOp { .. }
            | Inst::UnOp { .. }
            | Inst::Overflow { .. }
            | Inst::ICmp { .. }
            | Inst::FCmp { .. }
            | Inst::Cast { .. }
            | Inst::Select { .. }
            | Inst::Copy { .. } => false,

            // Aggregate field/element access. `Insert*` are functional updates
            // producing a NEW aggregate value; they do not write memory.
            Inst::ExtractField { .. }
            | Inst::InsertField { .. }
            | Inst::ExtractElement { .. }
            | Inst::InsertElement { .. } => false,

            // Address computation and fat-pointer (data + metadata) surgery.
            // These compute pointer VALUES; they do not dereference.
            Inst::GEP { .. }
            | Inst::PtrData { .. }
            | Inst::PtrMetadata { .. }
            | Inst::PtrFromParts { .. } => false,

            // Allocation. Both merely PRODUCE a fresh address; the observable
            // effects of using storage are carried by the Load/Store that
            // dereference it, and `Dealloc` above is separately observable.
            //
            // NOTE: this is the inherited classification, preserved verbatim
            // by the change that made this match exhaustive. It is the one
            // pair here worth re-examining on its own merits — `Dealloc` is
            // observable while `HeapAlloc` is not, so an allocation whose
            // result goes unused is DCE-removable. That is the usual rule for
            // a pure allocator, but it is a real semantic commitment and it
            // was never stated anywhere until now.
            Inst::Alloca { .. } | Inst::HeapAlloc { .. } => false,

            // Constants and address-of-global: pure producers of a value.
            Inst::Const { .. } | Inst::NullPtr | Inst::GlobalAddr { .. } | Inst::Undef { .. } => {
                false
            }

            // A fresh aggregate value out of register lanes: no memory access,
            // no aliasing, no trap. Total by construction — the validator's
            // lane-typing rule IS its side condition — so an unused result is
            // freely removable.
            Inst::MakeAggregate { .. } | Inst::MakeClosure { .. } => false,

            // `n` copies of one register value: a fresh array value, total and
            // statically typed (the validator's element rule is its side
            // condition), no memory access — pure like `MakeAggregate`.
            Inst::ArraySplat { .. } => false,

            // A tensor contraction computes a fresh tensor value out of two
            // register tensors: no memory access, no trap. Its extent
            // agreement is a PRECONDITION (a violation is undefined
            // behaviour, as a division by zero in `BinOp` is), never a
            // checked effect, so an unused result is freely removable.
            Inst::TensorContract { .. } => false,

            // The map, the reduction and the view compute a fresh tensor
            // value out of register operands: no memory access, no trap.
            // Their preconditions (equal extents, in-range coordinates, a
            // map node's own, such as a nonzero divisor) are undefined
            // behaviour when violated, never checked effects.
            Inst::TensorMap { .. } | Inst::TensorReduce { .. } | Inst::TensorView { .. } => false,

            // The gather and the scatter compute a fresh tensor value out of
            // register tensors: no memory access, no trap. Equal extents and
            // in-range coordinates are preconditions (undefined behaviour
            // when violated, a `BoundsCheck` obligation when stated), never
            // checked effects.
            Inst::TensorGather { .. } | Inst::TensorScatter { .. } => false,

            // An assumption only ADDS information. Dropping it can lose a
            // proof, never change observable behavior.
            Inst::Assume { .. } => false,

            // Fixed-semantics sequence maps (contrast `SeqMap` above, which
            // invokes an arbitrary element function and is a call in disguise).
            Inst::SeqMapAddK { .. } | Inst::SeqMapNot { .. } => false,

            // A uniqueness READ of the reference count; it does not modify it
            // (`Retain`/`Release` above do).
            Inst::IsUnique { .. } => false,

            // Binding-frame producers. See `CloseFrame` above: OpenFrame /
            // BindSlot / LoadSlot are pure SSA ops, and removing an unused
            // OpenFrame also removes the matching CloseFrame's referent.
            Inst::OpenFrame { .. } | Inst::BindSlot { .. } | Inst::LoadSlot { .. } => false,
        }
    }

    /// Returns true if the instruction has side effects.
    ///
    /// This is a soundness-critical alias of [`has_observable_effects`]: an
    /// instruction "has side effects" exactly when it has observable effects,
    /// and DCE must not remove a side-effecting instruction. The name is kept
    /// for the historical call sites in `node.rs` and downstream tools.
    ///
    /// [`has_observable_effects`]: Inst::has_observable_effects
    #[inline]
    pub fn has_side_effects(&self) -> bool {
        self.has_observable_effects()
    }

    /// Returns true if dead-code elimination may safely remove this
    /// instruction *when its result is unused*.
    ///
    /// This is the exact complement of [`has_observable_effects`]: a node is
    /// removable-if-unused iff it has no observable effects. DCE drivers should
    /// call this (together with a use-count check on the node's results) rather
    /// than re-deriving the predicate, so the volatile-load / atomic-load
    /// carve-outs stay in one place.
    ///
    /// [`has_observable_effects`]: Inst::has_observable_effects
    #[inline]
    pub fn is_removable_if_unused(&self) -> bool {
        !self.has_observable_effects()
    }
}

/// One `Switch` arm: the selector value it matches, and the edge it takes.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SwitchCase {
    /// The selector value this arm matches.
    ///
    /// At an integer or `char` selector it is a constant OF THE SELECTOR'S
    /// TYPE, with that type's one spelling (`docs/SPEC_RATIFICATIONS.md`
    /// §3.3): a signed selector's case is its signed value (`-1` at `i8`), an
    /// unsigned selector's its unsigned value (`255` at `u8`), a `u128` value
    /// above `i128::MAX` the canonical `Constant::U128`. `trust-ir-build`
    /// checks it exactly as it checks an `Inst::Const` at that type, through
    /// the one constant funnel, and refuses anything else as
    /// `ValidationError::ConstTypeMismatch` — `switch u8 [ -1: .. ]` and
    /// `switch i8 [ 255: .. ]` included, which the reference interpreter
    /// would wrap and the Lean model would compare as residues. An `isize` /
    /// `usize` selector has the width of the module's target pointer
    /// (`Module::pointer_bits`; 64 bits for a target-free module), so on
    /// wasm32 `switch usize [ 2^32: .. ]` is refused exactly as
    /// `const usize 2^32` is there — it would alias `0`. At a refinement
    /// selector `refine<b, p>` the case is a constant of the base `b`, which
    /// is the selector's representation. A consumer MUST refuse a module that
    /// spells a case outside its selector type, one row per spelling
    /// (`refuse/switch_case_negative_at_unsigned`,
    /// `refuse/switch_case_above_signed_max`,
    /// `refuse/switch_case_negative_at_refined_unsigned`,
    /// `refuse/switch_case_usize_beyond_target_width`,
    /// `refuse/switch_case_isize_beyond_target_width`).
    pub value: Constant,
    pub target: BlockId,
    pub args: Vec<ValueId>,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    #[test]
    fn binop_debug_roundtrip() {
        let inst = Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        };
        let dbg = format!("{:?}", inst);
        assert!(dbg.contains("BinOp"));
        assert!(dbg.contains("Add"));
    }

    #[test]
    fn canonical_operand_walk_distinguishes_ssa_from_other_ids() {
        let call = Inst::CallIndirect {
            callee: v(7),
            sig: crate::value::FuncTyId::new(7),
            args: vec![v(8), v(9)],
            calling_conv: crate::CallingConv::C,
        };
        let mut operands = Vec::new();
        call.visit_value_operands(|value| operands.push(value));
        assert_eq!(operands, vec![v(7), v(8), v(9)]);
        assert!(call.uses_value(v(7)));
        assert!(call.uses_value(v(9)));
        assert!(!call.uses_value(v(10)));

        let seq_map = Inst::SeqMap {
            ty: Ty::Sequence(crate::value::TyId::new(0)),
            seq: v(1),
            fwd: FuncId::new(1),
        };
        operands.clear();
        seq_map.visit_value_operands(|value| operands.push(value));
        assert_eq!(operands, vec![v(1)]);
    }

    #[test]
    fn operand_try_visit_stops_at_first_match_in_a_high_arity_call() {
        let call = Inst::CallIndirect {
            callee: v(7),
            sig: crate::value::FuncTyId::new(0),
            args: (0..4_096).map(|index| v(index + 100)).collect(),
            calling_conv: crate::CallingConv::C,
        };
        let mut visits = 0usize;
        let result = call.try_visit_value_operands(|operand| {
            visits += 1;
            if operand == v(7) {
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(())
            }
        });
        assert!(result.is_break());
        assert_eq!(visits, 1);
        assert!(call.uses_value(v(7)));
    }

    #[test]
    fn unop_debug_roundtrip() {
        let inst = Inst::UnOp {
            op: UnOp::Neg,
            ty: Ty::I32,
            operand: v(0),
        };
        let dbg = format!("{:?}", inst);
        assert!(dbg.contains("UnOp"));
        assert!(dbg.contains("Neg"));
    }

    #[test]
    fn overflow_debug_roundtrip() {
        let inst = Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::I64,
            lhs: v(0),
            rhs: v(1),
        };
        let dbg = format!("{:?}", inst);
        assert!(dbg.contains("Overflow"));
        assert!(dbg.contains("AddOverflow"));
    }

    #[test]
    fn icmp_debug_roundtrip() {
        let inst = Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        };
        let dbg = format!("{:?}", inst);
        assert!(dbg.contains("ICmp"));
    }

    #[test]
    fn fcmp_debug_roundtrip() {
        let inst = Inst::FCmp {
            op: FCmpOp::OLt,
            ty: Ty::F64,
            lhs: v(0),
            rhs: v(1),
        };
        let dbg = format!("{:?}", inst);
        assert!(dbg.contains("FCmp"));
        assert!(dbg.contains("OLt"));
    }

    #[test]
    fn cast_debug_roundtrip() {
        let inst = Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::I32,
            dst_ty: Ty::I64,
            operand: v(0),
        };
        let dbg = format!("{:?}", inst);
        assert!(dbg.contains("Cast"));
        assert!(dbg.contains("ZExt"));
    }

    #[test]
    fn load_store_debug_roundtrip() {
        let load = Inst::Load {
            ty: Ty::I32,
            ptr: v(0),
            volatile: false,
            align: None,
        };
        let store = Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        };
        assert!(format!("{:?}", load).contains("Load"));
        assert!(format!("{:?}", store).contains("Store"));
    }

    #[test]
    fn alloca_debug_roundtrip() {
        let a = Inst::Alloca {
            ty: Ty::I64,
            count: None,
            align: None,
        };
        let b_inst = Inst::Alloca {
            ty: Ty::I64,
            count: Some(v(0)),
            align: None,
        };
        assert!(format!("{:?}", a).contains("Alloca"));
        assert!(format!("{:?}", b_inst).contains("Some"));
    }

    #[test]
    fn gep_debug_roundtrip() {
        let inst = Inst::GEP {
            pointee_ty: Ty::I32,
            base: v(0),
            indices: vec![v(1), v(2)],
            inbounds: false,
        };
        assert!(format!("{:?}", inst).contains("GEP"));
    }

    #[test]
    fn atomic_instructions_debug() {
        let al = Inst::AtomicLoad {
            ty: Ty::I64,
            ptr: v(0),
            ordering: Ordering::Acquire,
        };
        let as_ = Inst::AtomicStore {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            ordering: Ordering::Release,
        };
        let armw = Inst::AtomicRMW {
            op: AtomicRMWOp::Xchg,
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            ordering: Ordering::AcqRel,
        };
        let cx = Inst::CmpXchg {
            ty: Ty::I64,
            ptr: v(0),
            expected: v(1),
            desired: v(2),
            success: Ordering::SeqCst,
            failure: Ordering::Relaxed,
            weak: false,
        };
        let f = Inst::Fence {
            ordering: Ordering::SeqCst,
        };
        assert!(format!("{:?}", al).contains("AtomicLoad"));
        assert!(format!("{:?}", as_).contains("AtomicStore"));
        assert!(format!("{:?}", armw).contains("AtomicRMW"));
        assert!(format!("{:?}", cx).contains("CmpXchg"));
        assert!(format!("{:?}", f).contains("Fence"));
    }

    #[test]
    fn control_flow_debug() {
        let br = Inst::Br {
            target: b(1),
            args: vec![],
        };
        let cbr = Inst::CondBr {
            cond: v(0),
            then_target: b(1),
            then_args: vec![],
            else_target: b(2),
            else_args: vec![],
        };
        let sw = Inst::Switch {
            value: v(0),
            default: b(3),
            default_args: vec![],
            cases: vec![],
            exhaustive_enum_unreachable: false,
        };
        let ret = Inst::Return { values: vec![v(0)] };
        assert!(format!("{:?}", br).contains("Br"));
        assert!(format!("{:?}", cbr).contains("CondBr"));
        assert!(format!("{:?}", sw).contains("Switch"));
        assert!(format!("{:?}", ret).contains("Return"));
    }

    #[test]
    fn call_debug() {
        let c = Inst::Call {
            callee: FuncId::new(0),
            args: vec![v(0), v(1)],
        };
        let ci = Inst::CallIndirect {
            callee: v(0),
            sig: crate::value::FuncTyId::new(0),
            args: vec![v(1)],

            calling_conv: crate::CallingConv::C,
        };
        assert!(format!("{:?}", c).contains("Call"));
        assert!(format!("{:?}", ci).contains("CallIndirect"));
    }

    #[test]
    fn aggregate_debug() {
        let ef = Inst::ExtractField {
            ty: Ty::I32,
            aggregate: v(0),
            field: 1,
        };
        let inf = Inst::InsertField {
            ty: Ty::I32,
            aggregate: v(0),
            field: 1,
            value: v(2),
        };
        let ee = Inst::ExtractElement {
            ty: Ty::I32,
            array: v(0),
            index: v(1),
        };
        let ie = Inst::InsertElement {
            ty: Ty::I32,
            array: v(0),
            index: v(1),
            value: v(2),
        };
        assert!(format!("{:?}", ef).contains("ExtractField"));
        assert!(format!("{:?}", inf).contains("InsertField"));
        assert!(format!("{:?}", ee).contains("ExtractElement"));
        assert!(format!("{:?}", ie).contains("InsertElement"));
    }

    #[test]
    fn constant_and_special_debug() {
        let c = Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(42),
        };
        let np = Inst::NullPtr;
        let u = Inst::Undef { ty: Ty::I32 };
        assert!(format!("{:?}", c).contains("Const"));
        assert!(format!("{:?}", np).contains("NullPtr"));
        assert!(format!("{:?}", u).contains("Undef"));
    }

    #[test]
    fn proof_and_pseudo_debug() {
        let assume = Inst::Assume { cond: v(0) };
        let assert_inst = Inst::Assert {
            cond: v(0),
            kind: crate::inst::AssertKind::Unspecified,
            site: None,
        };
        let unr = Inst::Unreachable;
        let cp = Inst::Copy {
            ty: Ty::I32,
            operand: v(0),
        };
        let sel = Inst::Select {
            ty: Ty::I32,
            cond: v(0),
            then_val: v(1),
            else_val: v(2),
        };
        assert!(format!("{:?}", assume).contains("Assume"));
        assert!(format!("{:?}", assert_inst).contains("Assert"));
        assert!(format!("{:?}", unr).contains("Unreachable"));
        assert!(format!("{:?}", cp).contains("Copy"));
        assert!(format!("{:?}", sel).contains("Select"));
    }

    #[test]
    fn fixed_width_vector_ir_uses_existing_instruction_surface() {
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let v4bool = Ty::Vector(Box::new(Ty::Bool), 4);

        let add = Inst::BinOp {
            op: BinOp::Add,
            ty: v4i32.clone(),
            lhs: v(0),
            rhs: v(1),
        };
        let xor = Inst::BinOp {
            op: BinOp::Xor,
            ty: v4bool.clone(),
            lhs: v(2),
            rhs: v(3),
        };
        let cmp = Inst::ICmp {
            op: ICmpOp::Eq,
            ty: v4i32.clone(),
            lhs: v(0),
            rhs: v(1),
        };
        let select = Inst::Select {
            ty: v4i32.clone(),
            cond: v(4),
            then_val: v(0),
            else_val: v(1),
        };
        let load = Inst::Load {
            ty: v4i32.clone(),
            ptr: v(5),
            volatile: false,
            align: Some(16),
        };
        let store = Inst::Store {
            ty: v4i32,
            ptr: v(5),
            value: v(6),
            volatile: false,
            align: Some(16),
        };

        assert!(!add.has_side_effects());
        assert!(!xor.has_side_effects());
        assert!(!cmp.has_side_effects());
        assert!(!select.has_side_effects());
        assert!(!load.has_side_effects());
        assert!(store.has_side_effects());
        assert_eq!(format!("{:?}", add.clone()), format!("{:?}", add));
        assert!(format!("{:?}", select).contains("Select"));
    }

    #[test]
    fn vector_select_condition_contract_rejects_physical_integer_masks() {
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let v4bool = Ty::Vector(Box::new(Ty::Bool), 4);
        let v8bool = Ty::Vector(Box::new(Ty::Bool), 8);

        assert_eq!(Inst::required_select_condition_ty(&v4i32), v4bool);
        assert_eq!(Inst::required_select_condition_ty(&Ty::I32), Ty::Bool);
        assert!(
            Inst::validate_select_condition_ty(&v4i32, &Ty::Vector(Box::new(Ty::Bool), 4)).is_ok()
        );

        let physical_mask =
            Inst::validate_select_condition_ty(&v4i32, &v4i32).expect_err("i32 mask rejected");
        assert!(matches!(
            &physical_mask,
            SelectConditionTypeError::PhysicalIntegerMaskRequiresCompareToZero { .. }
        ));
        assert!(
            physical_mask.to_string().contains("compared to zero"),
            "{physical_mask}"
        );

        let wrong_lanes =
            Inst::validate_select_condition_ty(&v4i32, &v8bool).expect_err("lane mismatch");
        assert!(matches!(
            &wrong_lanes,
            SelectConditionTypeError::TypeMismatch { .. }
        ));
    }

    #[test]
    fn switch_case_construction() {
        let sc = SwitchCase {
            value: Constant::Int(42),
            target: b(5),
            args: vec![v(0)],
        };
        assert_eq!(sc.value, Constant::Int(42));
        assert_eq!(sc.target, b(5));
        assert_eq!(sc.args, vec![v(0)]);
    }

    #[test]
    fn all_binop_variants() {
        let ops = [
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::UDiv,
            BinOp::SDiv,
            BinOp::URem,
            BinOp::SRem,
            BinOp::FAdd,
            BinOp::FSub,
            BinOp::FMul,
            BinOp::FDiv,
            BinOp::FRem,
            BinOp::And,
            BinOp::Or,
            BinOp::Xor,
            BinOp::Shl,
            BinOp::LShr,
            BinOp::AShr,
        ];
        assert_eq!(ops.len(), 18);
    }

    #[test]
    fn all_icmpop_variants() {
        let ops = [
            ICmpOp::Eq,
            ICmpOp::Ne,
            ICmpOp::Ult,
            ICmpOp::Ule,
            ICmpOp::Ugt,
            ICmpOp::Uge,
            ICmpOp::Slt,
            ICmpOp::Sle,
            ICmpOp::Sgt,
            ICmpOp::Sge,
        ];
        assert_eq!(ops.len(), 10);
    }

    #[test]
    fn all_castop_variants() {
        let ops = [
            CastOp::Trunc,
            CastOp::ZExt,
            CastOp::SExt,
            CastOp::FPTrunc,
            CastOp::FPExt,
            CastOp::FPToUI,
            CastOp::FPToSI,
            CastOp::UIToFP,
            CastOp::SIToFP,
            CastOp::PtrToInt,
            CastOp::IntToPtr,
            CastOp::PtrToPtr,
            CastOp::Bitcast,
            CastOp::Transmute,
            CastOp::ReifyFnPointer,
            CastOp::FPToSISat,
            CastOp::FPToUISat,
        ];
        assert_eq!(ops.len(), 17);
    }

    #[test]
    fn all_ordering_variants() {
        let ords = [
            Ordering::Relaxed,
            Ordering::Acquire,
            Ordering::Release,
            Ordering::AcqRel,
            Ordering::SeqCst,
        ];
        assert_eq!(ords.len(), 5);
    }

    // --- Display impl tests: verify exact string output for every variant ---

    #[test]
    fn binop_display_all_variants() {
        let cases: &[(BinOp, &str)] = &[
            (BinOp::Add, "add"),
            (BinOp::Sub, "sub"),
            (BinOp::Mul, "mul"),
            (BinOp::UDiv, "udiv"),
            (BinOp::SDiv, "sdiv"),
            (BinOp::URem, "urem"),
            (BinOp::SRem, "srem"),
            (BinOp::FAdd, "fadd"),
            (BinOp::FSub, "fsub"),
            (BinOp::FMul, "fmul"),
            (BinOp::FDiv, "fdiv"),
            (BinOp::FRem, "frem"),
            (BinOp::And, "and"),
            (BinOp::Or, "or"),
            (BinOp::Xor, "xor"),
            (BinOp::Shl, "shl"),
            (BinOp::LShr, "lshr"),
            (BinOp::AShr, "ashr"),
            // WS3.20 (F-057): the rotate pair and IEEE copySign.
            (BinOp::RotL, "rotl"),
            (BinOp::RotR, "rotr"),
            (BinOp::FCopySign, "fcopysign"),
        ];
        assert_eq!(cases.len(), 21);
        for (op, expected) in cases {
            assert_eq!(
                format!("{}", op),
                *expected,
                "BinOp::{:?} display mismatch",
                op
            );
        }
    }

    #[test]
    fn unop_display_all_variants() {
        let cases: &[(UnOp, &str)] = &[
            (UnOp::Neg, "neg"),
            (UnOp::FNeg, "fneg"),
            (UnOp::Not, "not"),
            (UnOp::CtPop, "ctpop"),
            // WS3.20 (F-057): the bit intrinsics.
            (UnOp::CtLz, "ctlz"),
            (UnOp::CtTz, "cttz"),
            (UnOp::BSwap, "bswap"),
            (UnOp::BitReverse, "bitreverse"),
        ];
        for (op, expected) in cases {
            assert_eq!(
                format!("{}", op),
                *expected,
                "UnOp::{:?} display mismatch",
                op
            );
        }
    }

    #[test]
    fn overflow_op_display_all_variants() {
        let cases: &[(OverflowOp, &str)] = &[
            (OverflowOp::AddOverflow, "add.overflow"),
            (OverflowOp::SubOverflow, "sub.overflow"),
            (OverflowOp::MulOverflow, "mul.overflow"),
        ];
        for (op, expected) in cases {
            assert_eq!(
                format!("{}", op),
                *expected,
                "OverflowOp::{:?} display mismatch",
                op
            );
        }
    }

    #[test]
    fn icmp_op_display_all_variants() {
        let cases: &[(ICmpOp, &str)] = &[
            (ICmpOp::Eq, "eq"),
            (ICmpOp::Ne, "ne"),
            (ICmpOp::Ult, "ult"),
            (ICmpOp::Ule, "ule"),
            (ICmpOp::Ugt, "ugt"),
            (ICmpOp::Uge, "uge"),
            (ICmpOp::Slt, "slt"),
            (ICmpOp::Sle, "sle"),
            (ICmpOp::Sgt, "sgt"),
            (ICmpOp::Sge, "sge"),
        ];
        assert_eq!(cases.len(), 10);
        for (op, expected) in cases {
            assert_eq!(
                format!("{}", op),
                *expected,
                "ICmpOp::{:?} display mismatch",
                op
            );
        }
    }

    #[test]
    fn fcmp_op_display_all_variants() {
        let cases: &[(FCmpOp, &str)] = &[
            (FCmpOp::OEq, "oeq"),
            (FCmpOp::ONe, "one"),
            (FCmpOp::OLt, "olt"),
            (FCmpOp::OLe, "ole"),
            (FCmpOp::OGt, "ogt"),
            (FCmpOp::OGe, "oge"),
            (FCmpOp::UEq, "ueq"),
            (FCmpOp::UNe, "une"),
            (FCmpOp::ULt, "ult"),
            (FCmpOp::ULe, "ule"),
            (FCmpOp::UGt, "ugt"),
            (FCmpOp::UGe, "uge"),
        ];
        assert_eq!(cases.len(), 12);
        for (op, expected) in cases {
            assert_eq!(
                format!("{}", op),
                *expected,
                "FCmpOp::{:?} display mismatch",
                op
            );
        }
    }

    #[test]
    fn cast_op_display_all_variants() {
        let cases: &[(CastOp, &str)] = &[
            (CastOp::Trunc, "trunc"),
            (CastOp::ZExt, "zext"),
            (CastOp::SExt, "sext"),
            (CastOp::FPTrunc, "fptrunc"),
            (CastOp::FPExt, "fpext"),
            (CastOp::FPToUI, "fptoui"),
            (CastOp::FPToSI, "fptosi"),
            (CastOp::UIToFP, "uitofp"),
            (CastOp::SIToFP, "sitofp"),
            (CastOp::PtrToInt, "ptrtoint"),
            (CastOp::IntToPtr, "inttoptr"),
            (CastOp::PtrToPtr, "ptrtoptr"),
            (CastOp::Bitcast, "bitcast"),
            (CastOp::Transmute, "transmute"),
            (CastOp::ReifyFnPointer, "reify_fn_pointer"),
            (CastOp::FPToSISat, "fptosi.sat"),
            (CastOp::FPToUISat, "fptoui.sat"),
        ];
        assert_eq!(cases.len(), 17);
        for (op, expected) in cases {
            assert_eq!(
                format!("{}", op),
                *expected,
                "CastOp::{:?} display mismatch",
                op
            );
        }
    }

    #[test]
    fn ordering_display_all_variants() {
        let cases: &[(Ordering, &str)] = &[
            (Ordering::Relaxed, "relaxed"),
            (Ordering::Acquire, "acquire"),
            (Ordering::Release, "release"),
            (Ordering::AcqRel, "acq_rel"),
            (Ordering::SeqCst, "seq_cst"),
        ];
        for (ord, expected) in cases {
            assert_eq!(
                format!("{}", ord),
                *expected,
                "Ordering::{:?} display mismatch",
                ord
            );
        }
    }

    #[test]
    fn atomic_rmw_op_display_all_variants() {
        let cases: &[(AtomicRMWOp, &str)] = &[
            (AtomicRMWOp::Xchg, "xchg"),
            (AtomicRMWOp::Add, "add"),
            (AtomicRMWOp::Sub, "sub"),
            (AtomicRMWOp::And, "and"),
            (AtomicRMWOp::Or, "or"),
            (AtomicRMWOp::Xor, "xor"),
            (AtomicRMWOp::Max, "max"),
            (AtomicRMWOp::Min, "min"),
            (AtomicRMWOp::UMax, "umax"),
            (AtomicRMWOp::UMin, "umin"),
        ];
        assert_eq!(cases.len(), 10);
        for (op, expected) in cases {
            assert_eq!(
                format!("{}", op),
                *expected,
                "AtomicRMWOp::{:?} display mismatch",
                op
            );
        }
    }

    // --- Clone and PartialEq tests for Inst ---

    #[test]
    fn inst_clone_equals_original() {
        let inst = Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        };
        let cloned = inst.clone();
        assert_eq!(inst, cloned);
    }

    #[test]
    fn inst_clone_complex_variants() {
        let instructions = vec![
            Inst::GEP {
                pointee_ty: Ty::I32,
                base: v(0),
                indices: vec![v(1), v(2), v(3)],
                inbounds: false,
            },
            Inst::Switch {
                value: v(0),
                default: b(10),
                default_args: vec![v(5)],
                cases: vec![
                    SwitchCase {
                        value: Constant::Int(0),
                        target: b(1),
                        args: vec![],
                    },
                    SwitchCase {
                        value: Constant::Int(1),
                        target: b(2),
                        args: vec![v(1)],
                    },
                ],
                exhaustive_enum_unreachable: false,
            },
            Inst::CmpXchg {
                ty: Ty::I64,
                ptr: v(0),
                expected: v(1),
                desired: v(2),
                success: Ordering::SeqCst,
                failure: Ordering::Acquire,
                weak: false,
            },
            Inst::Select {
                ty: Ty::I32,
                cond: v(0),
                then_val: v(1),
                else_val: v(2),
            },
        ];
        for inst in &instructions {
            let cloned = inst.clone();
            assert_eq!(inst, &cloned, "Clone/PartialEq mismatch for {:?}", inst);
        }
    }

    #[test]
    fn different_inst_variants_not_equal() {
        let add = Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        };
        let sub = Inst::BinOp {
            op: BinOp::Sub,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        };
        assert_ne!(add, sub);

        let load = Inst::Load {
            ty: Ty::I32,
            ptr: v(0),
            volatile: false,
            align: None,
        };
        let store = Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        };
        assert_ne!(load, store);

        let ret_empty = Inst::Return { values: vec![] };
        let ret_one = Inst::Return { values: vec![v(0)] };
        assert_ne!(ret_empty, ret_one);
    }

    #[test]
    fn inst_same_variant_different_operands_not_equal() {
        let a = Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        };
        let b_inst = Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(2),
        };
        assert_ne!(a, b_inst);

        let c = Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: v(0),
            rhs: v(1),
        };
        assert_ne!(a, c); // same op, different type
    }

    // --- SwitchCase tests ---

    #[test]
    fn switch_case_partial_eq() {
        let a = SwitchCase {
            value: Constant::Int(1),
            target: b(1),
            args: vec![],
        };
        let b_case = SwitchCase {
            value: Constant::Int(1),
            target: b(1),
            args: vec![],
        };
        assert_eq!(a, b_case);

        let c = SwitchCase {
            value: Constant::Int(2),
            target: b(1),
            args: vec![],
        };
        assert_ne!(a, c);

        let d = SwitchCase {
            value: Constant::Int(1),
            target: b(2),
            args: vec![],
        };
        assert_ne!(a, d);

        let e = SwitchCase {
            value: Constant::Int(1),
            target: b(1),
            args: vec![v(0)],
        };
        assert_ne!(a, e);
    }

    #[test]
    fn switch_case_clone() {
        let sc = SwitchCase {
            value: Constant::Int(42),
            target: b(5),
            args: vec![v(0), v(1)],
        };
        let cloned = sc.clone();
        assert_eq!(sc, cloned);
    }

    // --- All FCmpOp variant tests (not yet covered) ---

    #[test]
    fn all_fcmpop_variants() {
        let ops = [
            FCmpOp::OEq,
            FCmpOp::ONe,
            FCmpOp::OLt,
            FCmpOp::OLe,
            FCmpOp::OGt,
            FCmpOp::OGe,
            FCmpOp::UEq,
            FCmpOp::UNe,
            FCmpOp::ULt,
            FCmpOp::ULe,
            FCmpOp::UGt,
            FCmpOp::UGe,
        ];
        assert_eq!(ops.len(), 12);
    }

    #[test]
    fn all_unop_variants() {
        let ops = [
            UnOp::Neg,
            UnOp::FNeg,
            UnOp::Not,
            UnOp::CtPop,
            UnOp::CtLz,
            UnOp::CtTz,
            UnOp::BSwap,
            UnOp::BitReverse,
        ];
        assert_eq!(ops.len(), 8);
    }

    #[test]
    fn all_overflow_op_variants() {
        let ops = [
            OverflowOp::AddOverflow,
            OverflowOp::SubOverflow,
            OverflowOp::MulOverflow,
        ];
        assert_eq!(ops.len(), 3);
    }

    #[test]
    fn all_atomic_rmw_op_variants() {
        let ops = [
            AtomicRMWOp::Xchg,
            AtomicRMWOp::Add,
            AtomicRMWOp::Sub,
            AtomicRMWOp::And,
            AtomicRMWOp::Or,
            AtomicRMWOp::Xor,
            AtomicRMWOp::Max,
            AtomicRMWOp::Min,
            AtomicRMWOp::UMax,
            AtomicRMWOp::UMin,
        ];
        assert_eq!(ops.len(), 10);
    }

    // --- Hash tests for enum types ---

    #[test]
    fn binop_hash_consistency() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(BinOp::Add);
        set.insert(BinOp::Sub);
        set.insert(BinOp::Add); // duplicate
        assert_eq!(set.len(), 2);
        assert!(set.contains(&BinOp::Add));
        assert!(set.contains(&BinOp::Sub));
    }

    #[test]
    fn ordering_hash_consistency() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        for ord in &[
            Ordering::Relaxed,
            Ordering::Acquire,
            Ordering::Release,
            Ordering::AcqRel,
            Ordering::SeqCst,
        ] {
            set.insert(*ord);
        }
        assert_eq!(set.len(), 5);
    }

    // --- Inst NullPtr and Unreachable are unit variants ---

    #[test]
    fn nullptr_eq() {
        assert_eq!(Inst::NullPtr, Inst::NullPtr);
    }

    #[test]
    fn unreachable_eq() {
        assert_eq!(Inst::Unreachable, Inst::Unreachable);
    }

    #[test]
    fn nullptr_ne_unreachable() {
        assert_ne!(Inst::NullPtr, Inst::Unreachable);
    }

    // --- Borrow and ARC instruction tests ---

    #[test]
    fn borrow_debug_roundtrip() {
        let inst = Inst::Borrow { ptr: v(0) };
        let dbg = format!("{:?}", inst);
        assert!(dbg.contains("Borrow"));
    }

    #[test]
    fn borrow_mut_debug_roundtrip() {
        let inst = Inst::BorrowMut { ptr: v(0) };
        let dbg = format!("{:?}", inst);
        assert!(dbg.contains("BorrowMut"));
    }

    #[test]
    fn end_borrow_debug_roundtrip() {
        let inst = Inst::EndBorrow { borrow_ptr: v(0) };
        let dbg = format!("{:?}", inst);
        assert!(dbg.contains("EndBorrow"));
    }

    #[test]
    fn retain_debug_roundtrip() {
        let inst = Inst::Retain { ptr: v(0) };
        let dbg = format!("{:?}", inst);
        assert!(dbg.contains("Retain"));
    }

    #[test]
    fn release_debug_roundtrip() {
        let inst = Inst::Release { ptr: v(0) };
        let dbg = format!("{:?}", inst);
        assert!(dbg.contains("Release"));
    }

    #[test]
    fn is_unique_debug_roundtrip() {
        let inst = Inst::IsUnique { ptr: v(0) };
        let dbg = format!("{:?}", inst);
        assert!(dbg.contains("IsUnique"));
    }

    #[test]
    fn borrow_clone_eq() {
        let inst = Inst::Borrow { ptr: v(5) };
        assert_eq!(inst, inst.clone());
    }

    #[test]
    fn arc_clone_eq() {
        let retain = Inst::Retain { ptr: v(3) };
        let release = Inst::Release { ptr: v(3) };
        assert_eq!(retain, retain.clone());
        assert_eq!(release, release.clone());
        assert_ne!(retain, release);
    }

    // --- is_terminator tests ---

    #[test]
    fn is_terminator_true_for_terminators() {
        let terminators = [
            Inst::Br {
                target: b(0),
                args: vec![],
            },
            Inst::CondBr {
                cond: v(0),
                then_target: b(1),
                then_args: vec![],
                else_target: b(2),
                else_args: vec![],
            },
            Inst::Switch {
                value: v(0),
                default: b(0),
                default_args: vec![],
                cases: vec![],
                exhaustive_enum_unreachable: false,
            },
            Inst::Return { values: vec![] },
            Inst::Unreachable,
        ];
        for inst in &terminators {
            assert!(inst.is_terminator(), "{:?} should be a terminator", inst);
        }
    }

    #[test]
    fn is_terminator_false_for_non_terminators() {
        let non_terminators = [
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            },
            Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: None,
            },
            Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            },
            Inst::Call {
                callee: FuncId::new(0),
                args: vec![],
            },
            Inst::Borrow { ptr: v(0) },
            Inst::Retain { ptr: v(0) },
            Inst::NullPtr,
            Inst::Dealloc { ptr: v(0) },
        ];
        for inst in &non_terminators {
            assert!(
                !inst.is_terminator(),
                "{:?} should not be a terminator",
                inst
            );
        }
    }

    // --- has_side_effects tests ---

    #[test]
    fn has_side_effects_memory_writes() {
        let side_effecting = [
            Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            },
            Inst::AtomicStore {
                ty: Ty::I64,
                ptr: v(0),
                value: v(1),
                ordering: Ordering::Release,
            },
            Inst::AtomicRMW {
                op: AtomicRMWOp::Add,
                ty: Ty::I64,
                ptr: v(0),
                value: v(1),
                ordering: Ordering::AcqRel,
            },
            Inst::CmpXchg {
                ty: Ty::I64,
                ptr: v(0),
                expected: v(1),
                desired: v(2),
                success: Ordering::SeqCst,
                failure: Ordering::Relaxed,
                weak: false,
            },
            Inst::Fence {
                ordering: Ordering::SeqCst,
            },
        ];
        for inst in &side_effecting {
            assert!(
                inst.has_side_effects(),
                "{:?} should have side effects",
                inst
            );
        }
    }

    #[test]
    fn has_side_effects_calls() {
        let call = Inst::Call {
            callee: FuncId::new(0),
            args: vec![v(0)],
        };
        let call_indirect = Inst::CallIndirect {
            callee: v(0),
            sig: crate::value::FuncTyId::new(0),
            args: vec![v(1)],

            calling_conv: crate::CallingConv::C,
        };
        assert!(call.has_side_effects());
        assert!(call_indirect.has_side_effects());
    }

    #[test]
    fn has_side_effects_assert() {
        let assert_inst = Inst::Assert {
            cond: v(0),
            kind: crate::inst::AssertKind::Unspecified,
            site: None,
        };
        assert!(assert_inst.has_side_effects());
    }

    #[test]
    fn has_side_effects_borrow_instructions() {
        let borrow = Inst::Borrow { ptr: v(0) };
        let borrow_mut = Inst::BorrowMut { ptr: v(0) };
        let end_borrow = Inst::EndBorrow { borrow_ptr: v(0) };

        assert!(
            borrow.has_side_effects(),
            "Borrow modifies permission map, must be side-effecting"
        );
        assert!(
            borrow_mut.has_side_effects(),
            "BorrowMut modifies permission map, must be side-effecting"
        );
        assert!(
            end_borrow.has_side_effects(),
            "EndBorrow modifies permission map, must be side-effecting"
        );
    }

    /// `Inst::uses_borrow_permissions` is the proved shape table read through
    /// `shape()`, and the table is exactly the three permission instructions
    /// (gate 13 proves each cell; this pins the by-reference spelling and the
    /// set from the unverified lane too).
    #[test]
    fn uses_borrow_permissions_delegates_to_the_shape() {
        let permission: Vec<InstShape> = InstShape::ALL
            .iter()
            .copied()
            .filter(|shape| shape.uses_borrow_permissions())
            .collect();
        assert_eq!(
            permission,
            [
                InstShape::Borrow,
                InstShape::BorrowMut,
                InstShape::EndBorrow
            ]
        );
        for inst in [
            Inst::Borrow { ptr: v(0) },
            Inst::BorrowMut { ptr: v(0) },
            Inst::EndBorrow { borrow_ptr: v(0) },
            Inst::Copy {
                ty: Ty::Ptr,
                operand: v(0),
            },
            Inst::Load {
                ty: Ty::Ptr,
                ptr: v(0),
                volatile: false,
                align: None,
            },
            Inst::Dealloc { ptr: v(0) },
            Inst::Retain { ptr: v(0) },
        ] {
            assert_eq!(
                inst.uses_borrow_permissions(),
                inst.shape().uses_borrow_permissions(),
                "{inst:?}"
            );
            assert_eq!(
                inst.uses_borrow_permissions(),
                matches!(
                    inst,
                    Inst::Borrow { .. } | Inst::BorrowMut { .. } | Inst::EndBorrow { .. }
                ),
                "{inst:?}"
            );
        }
    }

    #[test]
    fn has_side_effects_arc_instructions() {
        let retain = Inst::Retain { ptr: v(0) };
        let release = Inst::Release { ptr: v(0) };

        assert!(
            retain.has_side_effects(),
            "Retain modifies refcount, must be side-effecting"
        );
        assert!(
            release.has_side_effects(),
            "Release modifies refcount, must be side-effecting"
        );
    }

    #[test]
    fn has_side_effects_terminators() {
        let br = Inst::Br {
            target: b(0),
            args: vec![],
        };
        let ret = Inst::Return { values: vec![] };
        let unr = Inst::Unreachable;

        assert!(br.has_side_effects());
        assert!(ret.has_side_effects());
        assert!(unr.has_side_effects());
    }

    #[test]
    fn has_side_effects_dealloc() {
        let dealloc = Inst::Dealloc { ptr: v(0) };
        assert!(
            dealloc.has_side_effects(),
            "Dealloc frees memory, must be side-effecting"
        );
    }

    #[test]
    fn has_side_effects_volatile_and_atomic_loads() {
        // A plain non-volatile load is pure (DCE may remove it if unused).
        let plain = Inst::Load {
            ty: Ty::I32,
            ptr: v(0),
            volatile: false,
            align: None,
        };
        assert!(
            !plain.has_observable_effects(),
            "non-volatile plain load is pure"
        );
        assert!(plain.is_removable_if_unused());

        // A volatile load is an observable access (MMIO / signal visibility);
        // DCE must NOT remove it even when the loaded value is dead.
        let volatile = Inst::Load {
            ty: Ty::I32,
            ptr: v(0),
            volatile: true,
            align: None,
        };
        assert!(
            volatile.has_observable_effects(),
            "volatile load is observable and must not be DCE'd"
        );
        assert!(volatile.has_side_effects());
        assert!(!volatile.is_removable_if_unused());

        // Atomic loads synchronize-with other threads regardless of ordering;
        // every ordering must be treated as observable.
        for ordering in [
            Ordering::Relaxed,
            Ordering::Acquire,
            Ordering::Release,
            Ordering::AcqRel,
            Ordering::SeqCst,
        ] {
            let al = Inst::AtomicLoad {
                ty: Ty::I64,
                ptr: v(0),
                ordering,
            };
            assert!(
                al.has_observable_effects(),
                "atomic load ({ordering:?}) is observable and must not be DCE'd"
            );
            assert!(al.has_side_effects());
            assert!(!al.is_removable_if_unused());
        }
    }

    #[test]
    fn dealloc_debug_roundtrip() {
        let inst = Inst::Dealloc { ptr: v(0) };
        let dbg = format!("{:?}", inst);
        assert!(dbg.contains("Dealloc"));
    }

    #[test]
    fn dealloc_clone_eq() {
        let inst = Inst::Dealloc { ptr: v(3) };
        assert_eq!(inst, inst.clone());
    }

    #[test]
    fn dealloc_ne_other_variants() {
        let dealloc = Inst::Dealloc { ptr: v(0) };
        let release = Inst::Release { ptr: v(0) };
        assert_ne!(dealloc, release);
    }

    #[test]
    fn dealloc_is_not_terminator() {
        let inst = Inst::Dealloc { ptr: v(0) };
        assert!(!inst.is_terminator());
    }

    #[test]
    fn no_side_effects_pure_instructions() {
        let pure_insts = [
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            },
            Inst::UnOp {
                op: UnOp::Neg,
                ty: Ty::I32,
                operand: v(0),
            },
            Inst::ICmp {
                op: ICmpOp::Eq,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            },
            Inst::FCmp {
                op: FCmpOp::OEq,
                ty: Ty::F64,
                lhs: v(0),
                rhs: v(1),
            },
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I32,
                dst_ty: Ty::I64,
                operand: v(0),
            },
            // Only a non-volatile plain load is freely removable by DCE.
            // Volatile loads and atomic loads (any ordering) are observable
            // and are covered by `has_side_effects_volatile_and_atomic_loads`.
            Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: None,
            },
            Inst::Alloca {
                ty: Ty::I32,
                count: None,
                align: None,
            },
            Inst::GEP {
                pointee_ty: Ty::I32,
                base: v(0),
                indices: vec![v(1)],
                inbounds: false,
            },
            Inst::Overflow {
                op: OverflowOp::AddOverflow,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            },
            Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(0),
                field: 0,
            },
            Inst::InsertField {
                ty: Ty::I32,
                aggregate: v(0),
                field: 0,
                value: v(1),
            },
            // WS3.5: a fresh aggregate out of register lanes — total, no
            // memory effect, freely removable when unused.
            Inst::MakeAggregate {
                ty: Ty::Tuple(vec![Ty::I32, Ty::I32]),
                variant: None,
                fields: vec![v(0), v(1)],
            },
            // `n` copies of one register value — pure like MakeAggregate.
            Inst::ArraySplat {
                ty: Ty::Array(crate::TyId::new(0), 1 << 40),
                value: v(0),
            },
            // A matrix multiply as a contraction: a fresh tensor value out
            // of two register tensors, extent agreement a precondition.
            Inst::TensorContract {
                ty: Ty::Tensor(Box::new(Ty::I32), 2),
                lhs: v(0),
                rhs: v(1),
                batch: Vec::new(),
                contract: vec![(1, 0)],
            },
            Inst::ExtractElement {
                ty: Ty::I32,
                array: v(0),
                index: v(1),
            },
            Inst::InsertElement {
                ty: Ty::I32,
                array: v(0),
                index: v(1),
                value: v(2),
            },
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(42),
            },
            Inst::NullPtr,
            Inst::Undef { ty: Ty::I32 },
            Inst::Assume { cond: v(0) },
            Inst::Copy {
                ty: Ty::I32,
                operand: v(0),
            },
            Inst::Select {
                ty: Ty::I32,
                cond: v(0),
                then_val: v(1),
                else_val: v(2),
            },
            Inst::IsUnique { ptr: v(0) },
        ];
        for inst in &pure_insts {
            assert!(
                !inst.has_side_effects(),
                "{:?} should NOT have side effects",
                inst
            );
        }
    }

    // --- Binding frame tests ---

    fn bf(id: u32) -> crate::value::BindingFrameId {
        crate::value::BindingFrameId::new(id)
    }

    fn i_slot() -> BindingSlot {
        BindingSlot::new("i", Ty::I64)
    }

    #[test]
    fn binding_slot_stores_name_and_ty() {
        let s = BindingSlot::new("i", Ty::I64);
        assert_eq!(s.name, "i");
        assert_eq!(s.ty, Ty::I64);
    }

    #[test]
    fn binding_frame_def_exposes_arity_and_slot_ty() {
        let def = BindingFrameDef::new(
            bf(0),
            "exists_i_frame",
            vec![
                BindingSlot::new("i", Ty::I64),
                BindingSlot::new("p", Ty::Bool),
            ],
        );
        assert_eq!(def.arity(), 2);
        assert_eq!(def.slot_ty(0), Some(&Ty::I64));
        assert_eq!(def.slot_ty(1), Some(&Ty::Bool));
        assert_eq!(def.slot_ty(2), None);
    }

    #[test]
    fn open_frame_is_not_terminator_and_pure() {
        let inst = Inst::OpenFrame {
            def: BindingFrameDef::new(bf(0), "f", vec![i_slot()]),
        };
        assert!(!inst.is_terminator());
        assert!(!inst.has_side_effects());
    }

    #[test]
    fn bind_slot_is_not_terminator_and_pure() {
        let inst = Inst::BindSlot {
            frame: v(0),
            slot: 0,
            value: v(1),
        };
        assert!(!inst.is_terminator());
        assert!(!inst.has_side_effects());
    }

    #[test]
    fn load_slot_is_not_terminator_and_pure() {
        let inst = Inst::LoadSlot {
            frame: v(0),
            slot: 0,
            ty: Ty::I64,
        };
        assert!(!inst.is_terminator());
        assert!(!inst.has_side_effects());
    }

    #[test]
    fn close_frame_is_not_terminator_but_side_effecting() {
        let inst = Inst::CloseFrame { frame: v(0) };
        assert!(!inst.is_terminator());
        // Must not be elided by DCE — dominator-LIFO nesting would break.
        assert!(inst.has_side_effects());
    }

    /// `has_observable_effects` must stay EXHAUSTIVE over `Inst`.
    ///
    /// The match deliberately has no `_` arm, so adding a variant to `Inst` is
    /// a compile error until somebody classifies it. That property is enforced
    /// by the compiler — but only for as long as the catch-all stays gone, and
    /// the tempting way to clear that compile error is to paste `_ => false`
    /// back in. This test makes doing so a TEST failure with an explanation,
    /// rather than a silent return to the old fail-open default.
    ///
    /// Fail-open in both directions, which is why it is worth a guard:
    ///   - DCE reads `false` as "safe to delete";
    ///   - the THIR/MIR differential reads `false` as "safe to admit into the
    ///     comparison" (only `true` makes it refuse).
    ///
    /// A new effectful instruction defaulting to `false` becomes deletable and
    /// comparable at once, with no diagnostic anywhere.
    #[test]
    fn has_observable_effects_has_no_catch_all_arm() {
        let src = include_str!("inst.rs");
        let start = src
            .find("pub fn has_observable_effects")
            .expect("has_observable_effects not found — did it get renamed?");

        // Walk to the end of the function by brace matching from its body.
        let body_start = start + src[start..].find('{').expect("no fn body brace");
        let mut depth = 0usize;
        let mut end = body_start;
        for (off, ch) in src[body_start..].char_indices() {
            match ch {
                '{' => depth += 1,
                '}' => {
                    depth -= 1;
                    if depth == 0 {
                        end = body_start + off;
                        break;
                    }
                }
                _ => {}
            }
        }
        assert!(end > body_start, "failed to brace-match the fn body");
        let body = &src[body_start..end];

        // Strip line comments so the prose above (which quotes `_ => false`)
        // does not trip the scan; only real code arms count.
        let code: String = body
            .lines()
            .map(|l| match l.find("//") {
                Some(i) => &l[..i],
                None => l,
            })
            .collect::<Vec<_>>()
            .join("\n");

        for pat in ["_ =>", "_ if"] {
            assert!(
                !code.contains(pat),
                "`has_observable_effects` regained a `{pat}` catch-all arm.\n\
                 Do not reintroduce one: it silently reclassifies every future \
                 instruction as PURE, which makes it BOTH DCE-removable AND \
                 admissible into the THIR/MIR differential comparison.\n\
                 Classify the new variant with an explicit arm instead."
            );
        }
    }
}
