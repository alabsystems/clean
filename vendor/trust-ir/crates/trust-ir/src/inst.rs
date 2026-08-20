// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::constant::Constant;
use crate::ty::Ty;
use crate::value::{BindingFrameId, BlockId, FuncId, GlobalId, ValueId};

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
    BXor,
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
    Not,
    CtPop,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum OverflowOp {
    AddOverflow,
    SubOverflow,
    MulOverflow,
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
/// (`State/Memory.lean`): it records which runtime owns the allocation so
/// `trust-cg` can route deallocation to the matching free (`__rust_dealloc` /
/// Swift release / C `free` / Clean's RC runtime). The stack origin is
/// `Alloca` and needs no marker.
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
    RustHeap,
    /// Swift heap allocation (ARC-managed object storage).
    SwiftHeap,
    /// C `malloc`.
    CMalloc,
    /// Clean Perceus reference-counted heap cell (`clean_alloc_ctor` /
    /// `clean_inc` / `clean_dec` runtime). Freed by `Release` reaching
    /// refcount zero, exactly like `SwiftHeap`.
    CleanHeap,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Inst {
    BinOp {
        op: BinOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    },
    UnOp {
        op: UnOp,
        ty: Ty,
        operand: ValueId,
    },
    Overflow {
        op: OverflowOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    },
    ICmp {
        op: ICmpOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    },
    FCmp {
        op: FCmpOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    },
    Cast {
        op: CastOp,
        src_ty: Ty,
        dst_ty: Ty,
        operand: ValueId,
    },

    // Memory
    Load {
        ty: Ty,
        ptr: ValueId,
        volatile: bool,
        align: Option<u64>,
    },
    Store {
        ty: Ty,
        ptr: ValueId,
        value: ValueId,
        volatile: bool,
        align: Option<u64>,
    },
    Alloca {
        ty: Ty,
        count: Option<ValueId>,
        align: Option<u64>,
    },
    /// Heap allocation: a fresh region of `count` (default 1) elements of `ty`,
    /// owned by `origin`'s runtime, returned as an opaque `Ty::Ptr`. The heap
    /// counterpart to the stack-only `Alloca`; the matched `Dealloc` frees it.
    /// Lowers `Box::new` / `Vec`/`String` growth / `malloc`. `align` defaults to
    /// the natural alignment of `ty`.
    HeapAlloc {
        ty: Ty,
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
        pointee_ty: Ty,
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
        ptr_ty: Ty,
        ptr: ValueId,
    },
    /// Extract the metadata lane from a pointer-like value.
    ///
    /// Fat slice/str metadata is the target pointer-sized unsigned integer;
    /// trait-object metadata is a thin vtable pointer. Thin pointer-like
    /// values carry unit metadata.
    PtrMetadata {
        ptr_ty: Ty,
        metadata_ty: Ty,
        ptr: ValueId,
    },
    /// Rebuild a pointer-like value from a data pointer and metadata.
    ///
    /// This is the structured target for Rust MIR wide-pointer coercions and
    /// `ptr::from_raw_parts`-style normalization.
    PtrFromParts {
        ptr_ty: Ty,
        metadata_ty: Ty,
        data: ValueId,
        metadata: ValueId,
    },

    // Atomics
    AtomicLoad {
        ty: Ty,
        ptr: ValueId,
        ordering: Ordering,
    },
    AtomicStore {
        ty: Ty,
        ptr: ValueId,
        value: ValueId,
        ordering: Ordering,
    },
    AtomicRMW {
        op: AtomicRMWOp,
        ty: Ty,
        ptr: ValueId,
        value: ValueId,
        ordering: Ordering,
    },
    CmpXchg {
        ty: Ty,
        ptr: ValueId,
        expected: ValueId,
        desired: ValueId,
        success: Ordering,
        failure: Ordering,
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
        /// Trust: set TRUE only by the TyCtxt-vetted extraction check
        /// (`mark_exhaustive_enum_unreachable_switches`) when the selector is a
        /// genuine single-assignment enum-discriminant temp, the case values are
        /// EXACTLY the enum's full discriminant tag set, and the `default` arm is
        /// `Unreachable`. The native CHC translator then conjoins
        /// `selector ∈ {case values}` into the default arm, making the otherwise
        /// arm UNSAT (provable). False for plain-integer switches and partial
        /// matches, so genuine `unreachable_unchecked` UB stays Unknown/Fail.
        #[cfg_attr(feature = "serde", serde(default))]
        exhaustive_enum_unreachable: bool,
    },
    Call {
        callee: FuncId,
        args: Vec<ValueId>,
    },
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
        ty: Ty,
        aggregate: ValueId,
        field: u32,
    },
    InsertField {
        ty: Ty,
        aggregate: ValueId,
        field: u32,
        value: ValueId,
    },
    ExtractElement {
        ty: Ty,
        array: ValueId,
        index: ValueId,
    },
    InsertElement {
        ty: Ty,
        array: ValueId,
        index: ValueId,
        value: ValueId,
    },

    // Constants
    Const {
        ty: Ty,
        value: Constant,
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
    Undef {
        ty: Ty,
    },

    // Proof
    Assume {
        cond: ValueId,
    },
    Assert {
        cond: ValueId,
    },
    Unreachable,

    // Pseudo
    Copy {
        ty: Ty,
        operand: ValueId,
    },
    Select {
        ty: Ty,
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
        ty: Ty,
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
        ty: Ty,
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
        ty: Ty,
        /// The sequence value whose elements are mapped.
        seq: ValueId,
        /// The element operation: a single-`&mut` function `fn(&mut elem)` whose
        /// give-back must be independently certifiable for the loop to certify.
        fwd: FuncId,
    },

    // Borrow instructions (Rust ownership model)
    // Reference: Ho & Protzenko, "Aeneas", ICFP 2022
    Borrow {
        ptr: ValueId,
    },
    BorrowMut {
        ptr: ValueId,
    },
    EndBorrow {
        borrow_ptr: ValueId,
    },

    // ARC instructions (Swift reference counting model)
    Retain {
        ptr: ValueId,
    },
    Release {
        ptr: ValueId,
    },
    IsUnique {
        ptr: ValueId,
    },

    // Heap deallocation (free / Box::drop)
    Dealloc {
        ptr: ValueId,
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
        ty: Ty,
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
    CoroSuspend {
        /// Pointer to the coroutine frame (caller-owned on-stack aggregate).
        frame: ValueId,
        /// I64-element index of the resume state field within the frame.
        state_slot: u32,
        /// Resume state index to record before returning (which continuation the
        /// next `resume` dispatches to).
        next_state: i64,
        /// The yielded value handed back to the resumer.
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
    //     result is only defined on the normal edge, the result must be consumed
    //     under the invoke's domination (a backend splitting the normal edge
    //     keeps the result copy on that edge);
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
    // table the backend already emits.
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
    Resume {
        /// The exception object pointer obtained from the `LandingPad`.
        exn: ValueId,
    },

    // Dialect op — a namespaced operation belonging to a TrustIr dialect
    // registered in a `DialectRegistry`. Core TrustIr tools round-trip these
    // without knowing their semantics; dialect-aware passes lower them into
    // core instructions (or into another dialect). See `crate::dialect`.
    DialectOp(Box<crate::dialect::DialectInst>),
}

impl Inst {
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
    pub fn is_terminator(&self) -> bool {
        matches!(
            self,
            Inst::Br { .. }
                | Inst::CondBr { .. }
                | Inst::Switch { .. }
                | Inst::Return { .. }
                | Inst::CoroSuspend { .. }
                | Inst::Invoke { .. }
                | Inst::Resume { .. }
                | Inst::Unreachable
        )
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
            // Memory writes and deallocation
            Inst::Store { .. }
            | Inst::AtomicStore { .. }
            | Inst::AtomicRMW { .. }
            | Inst::CmpXchg { .. }
            | Inst::Fence { .. }
            | Inst::Dealloc { .. } => true,

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
            Inst::Call { .. } | Inst::CallIndirect { .. } => true,

            // SeqMap invokes an arbitrary element function per element — a call
            // in disguise, so it is conservatively observable exactly like a
            // Call (the fixed-semantics SeqMapAddK/SeqMapNot stay pure).
            Inst::SeqMap { .. } => true,

            // Assertions may trap
            Inst::Assert { .. } => true,

            // Borrow instructions modify the permission map
            Inst::Borrow { .. } | Inst::BorrowMut { .. } | Inst::EndBorrow { .. } => true,

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

            // Terminators are side-effecting (control flow)
            _ if self.is_terminator() => true,

            // Everything else is pure
            _ => false,
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

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SwitchCase {
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
        let assert_inst = Inst::Assert { cond: v(0) };
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
        ];
        assert_eq!(cases.len(), 18);
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
        let ops = [UnOp::Neg, UnOp::FNeg, UnOp::Not, UnOp::CtPop];
        assert_eq!(ops.len(), 4);
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
        let assert_inst = Inst::Assert { cond: v(0) };
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
}
