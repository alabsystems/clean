// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! In-process bridge metadata for frontends and verifier backends.
//!
//! Frontends such as tRust already construct canonical `trust-ir::Module` values in
//! memory. These helpers expose the typed SSA facts that downstream consumers
//! need without requiring a text/JSON round trip or duplicating result-type
//! inference in every adapter.
//!
//! # Frontend-emission handshake
//!
//! This module is also the documented entry point for the producer side of the
//! contract: how a frontend (tRust, Clean) emits a TrustIr [`Module`] and
//! hands it to the verifier/backend. The handshake has three steps, all of which
//! are exercisable in this crate today:
//!
//! 1. **Build with provenance threaded.** Construct the module with the
//!    `trust-ir-build` builder and stamp a [`SourceSpan`] onto every emitted
//!    node via the builder's span-threading API (`FunctionBuilder::set_span` /
//!    `clear_span`, which centralize stamping so every `InstrNode` created while
//!    a span is set carries it). A `SourceSpan` is `{ file, line, col }`, where
//!    `file` indexes the module's debug-info source-file table. The data model
//!    is identical to setting [`InstrNode::span`] directly (see the
//!    worked-example test below, which threads spans without the builder so the
//!    example stays inside this dependency-free crate). The resulting
//!    per-instruction provenance is surfaced back through
//!    [`Function::typed_values`] ([`TypedValueMetadata::span`]).
//!
//! 2. **Validate against the pinned conformance subset.** A conforming frontend
//!    must restrict itself to the instruction / type surface that the backend is
//!    required to consume and that the Lean operational semantics fully model.
//!    Call [`Module::check_conformance_subset`] (or
//!    [`ConformanceSubset::check`]) to confirm the module stays inside that
//!    surface; it returns location-rich [`SubsetViolation`]s for any
//!    out-of-subset construct. The current subset version is
//!    [`ConformanceSubset::CURRENT`]. The AUTHORITY for the in/out boundary
//!    is `lowering-target-subset.md` (repo root) with its machine-readable
//!    mirror `trust_ir_conformance::subset`; this classifier restates the
//!    same v2 boundary for in-process producers, and the conformance crate's
//!    bridge-agreement gate (`tests/bridge_subset_agreement.rs`) pins the two
//!    spellings verdict- and version-identical, so neither can drift alone.
//!    The *wire-format* corpus a producer must round-trip bit-for-bit is the
//!    same crate's fixture set (see `TRUST.md` §"Frontend emission handshake").
//!
//! 3. **Hand off for verification.** Structural well-formedness is checked by
//!    `trust_ir_build::validate_module`; the typed in-process verification
//!    request/evidence surface is `trust_ir::request::NativeVerificationBundle`.
//!    Neither is re-implemented here.
//!
//! Frontends OWN the MIR / Swift-SIL / C-AST → TrustIr translation bodies;
//! TrustIr DEFINES the typed pen (the builder, the span data model, and the
//! conformance subset). See `docs/roadmap/integration-frontend-emission.md`.

use std::collections::BTreeMap;

use crate::{
    BlockId, CastOp, FuncId, Function, Inst, InstrNode, Module, ProofAnnotation, SourceSpan, Ty,
    ValueId, inst::SelectConditionTypeError,
};

/// Origin of a typed SSA value inside a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ValueMetadataOrigin {
    /// A basic-block parameter.
    BlockParam { block: BlockId, param_index: usize },
    /// A result produced by an instruction node.
    InstrResult {
        block: BlockId,
        instruction_index: usize,
        result_index: usize,
    },
}

/// Typed SSA metadata preserved for in-process consumers.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct TypedValueMetadata {
    pub value: ValueId,
    pub ty: Ty,
    pub origin: ValueMetadataOrigin,
    /// Proof annotations attached to the producing instruction. Block params
    /// have no producer, so this is empty for [`ValueMetadataOrigin::BlockParam`].
    #[cfg_attr(feature = "serde", serde(default))]
    pub proofs: Vec<ProofAnnotation>,
    /// Source span attached to the producing instruction, when present.
    #[cfg_attr(feature = "serde", serde(default))]
    pub span: Option<SourceSpan>,
}

/// Why a vector select condition failed the explicit mask contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum VectorSelectContractErrorKind {
    /// The condition value has no known type at the select site.
    UnknownConditionType,
    /// The condition type is known but is not `<N x bool>`.
    TypeMismatch,
    /// The condition is a same-lane integer vector mask and must be compared to
    /// zero before select.
    PhysicalIntegerMaskRequiresCompareToZero,
}

/// Location-rich vector select contract violation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VectorSelectContractError {
    pub function: FuncId,
    pub block: BlockId,
    pub instruction_index: usize,
    pub cond: ValueId,
    pub select_ty: Ty,
    pub expected_cond_ty: Ty,
    pub actual_cond_ty: Option<Ty>,
    pub kind: VectorSelectContractErrorKind,
}

impl core::fmt::Display for VectorSelectContractError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.kind {
            VectorSelectContractErrorKind::UnknownConditionType => write!(
                f,
                "vector select in function {:?}, block {:?}, instruction {} uses condition {:?} \
                 with unknown type; expected {} for select over {}",
                self.function,
                self.block,
                self.instruction_index,
                self.cond,
                self.expected_cond_ty,
                self.select_ty
            ),
            VectorSelectContractErrorKind::TypeMismatch => write!(
                f,
                "vector select in function {:?}, block {:?}, instruction {} requires condition {}, \
                 got {}",
                self.function,
                self.block,
                self.instruction_index,
                self.expected_cond_ty,
                self.actual_cond_ty
                    .as_ref()
                    .map_or_else(|| "<unknown>".to_string(), ToString::to_string)
            ),
            VectorSelectContractErrorKind::PhysicalIntegerMaskRequiresCompareToZero => write!(
                f,
                "vector select in function {:?}, block {:?}, instruction {} requires logical \
                 condition {}; physical integer mask {} must be compared to zero before select",
                self.function,
                self.block,
                self.instruction_index,
                self.expected_cond_ty,
                self.actual_cond_ty
                    .as_ref()
                    .map_or_else(|| "<unknown>".to_string(), ToString::to_string)
            ),
        }
    }
}

/// The pinned lowering-target conformance subset a conforming frontend emits
/// and a conforming backend consumes.
///
/// # What the subset is
///
/// TrustIr's full `Inst` / `Ty` / `CastOp` surface is the canonical schema, and
/// the `crates/trust-ir/tests/lean_schema_parity.rs` B3 gate keeps a Lean
/// *constructor* present for every Rust variant (its allowlists are now empty).
/// A constructor existing in Lean is necessary but not sufficient for a frontend
/// to safely emit a construct: a handful of constructs only have *partial* Lean
/// operational semantics (documented in `docs/roadmap/B3-lean-ir-parity.md` and
/// the parity-test comments). The conformance subset is the stricter, *versioned*
/// promise: the surface whose semantics are fully modelled, so a producer that
/// stays inside it is guaranteed a backend can lower it and the proof layer can
/// reason about it.
///
/// # Excluded constructs (subset v2 — `lowering-target-subset.md` is the authority)
///
/// The boundary is the ratified lowering-target subset v2 (repo-root doc;
/// machine mirror `trust_ir_conformance::subset`, agreement pinned by that
/// crate's `bridge_subset_agreement` gate):
///
/// - **Types**: [`Ty::F16`] (rounding semantics pending), pointer-width
///   integers / `char` pending their depth-ledger adoption, producer-only
///   [`Ty::Error`], and [`Ty::Refine`] (never ratified into the subset;
///   fail-closed until a version bump admits it). First-class [`Ty::FatPtr`]
///   is admitted on the model's pinned 64-bit little-endian target in v2.
/// - **Casts**: [`CastOp::ReifyFnPointer`] (fn-item partial) and
///   [`CastOp::FPToSISat`] / [`CastOp::FPToUISat`] (no proven bridge/ay
///   lowering). [`CastOp::Transmute`] is in-subset **scalar-to-scalar only**
///   (structural condition); [`CastOp::PtrToPtr`] is fully in-subset.
/// - **Instructions**: [`Inst::Resume`], [`Inst::LandingPad`],
///   [`Inst::CoroSuspend`] — host-unwinding / coroutine depth-ledger partials.
/// - **Dialect ops**: [`Inst::DialectOp`] except the six proven fast-4
///   `vector.*` ops (`pack_lanes`, `extract_lane`, `insert_lane`,
///   `mask_to_bits`, `reduce`, `shuffle`).
/// - **Proof annotations**: [`ProofAnnotation::Custom`] (producer-defined,
///   unpinned) and any unratified or feature-gated variant (fail-closed).
///
/// Everything else — scalar/vector arithmetic, comparisons, memory, atomics,
/// borrow, ARC, control flow, calls (`Invoke` on the normal-path contract),
/// aggregates, binding frames, and the 36 ratified proof annotations — is
/// in-subset.
///
/// The classifier ([`ConformanceSubset::ty_excluded`] /
/// [`ConformanceSubset::inst_excluded`] /
/// [`ConformanceSubset::proof_annotation_excluded`]) matches the `Ty` /
/// `Inst` / `CastOp` / `ProofAnnotation` enums *exhaustively*, so adding a
/// new IR variant forces an explicit in/out decision here at compile time —
/// the subset cannot silently drift.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ConformanceSubset {
    /// Monotonic subset version. Bump when the in/out boundary changes (e.g.
    /// when a previously-excluded construct gains full Lean semantics and is
    /// promoted into the subset). Frontends pin against a version.
    pub version: u32,
}

fn ty_contains_fat_ptr(ty: &Ty) -> bool {
    match ty {
        Ty::FatPtr(_) => true,
        Ty::Vector(elem, _)
        | Ty::Ref(elem)
        | Ty::RefMut(elem)
        | Ty::PtrConst(elem)
        | Ty::PtrMut(elem)
        | Ty::Rc(elem) => ty_contains_fat_ptr(elem),
        Ty::Tuple(elems) => elems.iter().any(ty_contains_fat_ptr),
        _ => false,
    }
}

fn inst_contains_fat_ptr(inst: &Inst) -> bool {
    match inst {
        Inst::Cast { src_ty, dst_ty, .. } => {
            ty_contains_fat_ptr(src_ty) || ty_contains_fat_ptr(dst_ty)
        }
        Inst::PtrData { ptr_ty, .. } => ty_contains_fat_ptr(ptr_ty),
        Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ..
        }
        | Inst::PtrFromParts {
            ptr_ty,
            metadata_ty,
            ..
        } => ty_contains_fat_ptr(ptr_ty) || ty_contains_fat_ptr(metadata_ty),
        Inst::BinOp { ty, .. }
        | Inst::SeqMapAddK { ty, .. }
        | Inst::SeqMapNot { ty, .. }
        | Inst::SeqMap { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Overflow { ty, .. }
        | Inst::ICmp { ty, .. }
        | Inst::FCmp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::Store { ty, .. }
        | Inst::Alloca { ty, .. }
        | Inst::HeapAlloc { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicStore { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::CmpXchg { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Const { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::LoadSlot { ty, .. } => ty_contains_fat_ptr(ty),
        Inst::GEP { pointee_ty, .. } => ty_contains_fat_ptr(pointee_ty),
        Inst::OpenFrame { def } => def.slots.iter().any(|slot| ty_contains_fat_ptr(&slot.ty)),
        Inst::DialectOp(op) => op.result_tys.iter().any(ty_contains_fat_ptr),
        _ => false,
    }
}

fn ptr_trio_ty_supported(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Ptr
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Rc(_)
            | Ty::FatPtr(_)
    )
}

fn module_supports_fat_ptr_layout(module: &Module) -> bool {
    module.pointer_bits() == crate::shape::DEFAULT_POINTER_BITS
        && module
            .target_info
            .as_ref()
            .is_none_or(|target| target.endianness == crate::Endianness::Little)
}

impl Default for ConformanceSubset {
    fn default() -> Self {
        Self::CURRENT
    }
}

/// Dialect ops with a proven trust-ir lowering (the ratified fast-4 set).
/// Mirrors `trust_ir_conformance::subset::DIALECT_OP_ALLOWLIST_V2`; the
/// conformance crate's bridge-agreement gate pins the two lists identical.
const SUBSET_DIALECT_OPS: &[&str] = &[
    "vector.extract_lane",
    "vector.insert_lane",
    "vector.mask_to_bits",
    "vector.pack_lanes",
    "vector.reduce",
    "vector.shuffle",
];

/// The scalar types a `Transmute` may reinterpret between — the Lean `semCast`
/// scalar partial (`lowering-target-subset.md` §"Structural conditions",
/// condition 1): `I8`–`I128` / `U8`–`U128` / `F32` / `F64` / `Bool` / `Ptr`.
/// Mirrors `trust_ir_conformance::subset::is_transmute_scalar`.
fn transmute_scalar_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
    )
}

impl ConformanceSubset {
    /// The current pinned subset. Frontends target this version.
    pub const CURRENT: Self = Self { version: 2 };

    /// Reason a construct is outside the conformance subset.
    ///
    /// Returns the human-readable exclusion reason for a [`Ty`], or `None` if the
    /// type (recursing into element/aggregate types) is fully in-subset.
    pub fn ty_excluded(ty: &Ty) -> Option<&'static str> {
        match ty {
            Ty::F16 => Some("Ty::F16 has only partial Lean semantics (rounding pending)"),
            // v25 B1 scalars: name-level Lean parity landed with the format;
            // EXECUTABLE Lean semantics (pointer-width arithmetic, char range)
            // are the B1 depth-ledger follow-up - out of subset until then.
            Ty::Isize | Ty::Usize => {
                Some("Ty::Isize/Usize executable Lean semantics pending (B1 depth ledger)")
            }
            Ty::Char => Some("Ty::Char executable Lean semantics pending (B1 depth ledger)"),
            Ty::Error => Some("Ty::Error is producer-internal and never wire-legal"),
            Ty::FatPtr(_) => None,
            // Composite types are in-subset iff their components are. Recurse so
            // e.g. `Tuple(F16, I32)` or `Vector<F16>` is correctly rejected.
            Ty::Vector(elem, _)
            | Ty::Ref(elem)
            | Ty::RefMut(elem)
            | Ty::PtrConst(elem)
            | Ty::PtrMut(elem)
            | Ty::Rc(elem) => Self::ty_excluded(elem),
            Ty::Tuple(elems) => elems.iter().find_map(Self::ty_excluded),
            // Fully in-subset (named-aggregate element types live in the module
            // tables, validated structurally elsewhere; the subset gate inspects
            // the inline type surface only).
            Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
            | Ty::Unit
            | Ty::Never
            | Ty::Struct(_)
            | Ty::Array(_, _)
            | Ty::Enum(_)
            | Ty::Func(_)
            | Ty::Set(_, _)
            | Ty::Sequence(_)
            | Ty::Record(_)
            | Ty::Closure(_) => None,
            // Representation-preserving over its table-resolved base, but the
            // ratified v2 subset never admitted it (`lowering-target-subset.md`
            // does not list it; the machine allowlist refuses it fail-closed).
            // Admitting it is an expansion under the doc's bump policy — do
            // not re-include it here without a version bump in BOTH spellings.
            Ty::Refine(_, _) => {
                Some("Ty::Refine is not ratified into lowering-target subset v2 (fail-closed)")
            }
        }
    }

    /// Reason a [`CastOp`] is outside the subset, or `None` if in-subset.
    ///
    /// `Transmute` is in-subset at the op level but **scalar-to-scalar only**;
    /// that structural condition needs the cast's `src_ty`/`dst_ty`, so it is
    /// enforced by [`ConformanceSubset::inst_excluded`] (condition 1 of
    /// `lowering-target-subset.md` §"Structural conditions"). `PtrToPtr` has
    /// full `semCast` semantics and is in-subset (it is NOT one of the
    /// depth-ledger partials — see the spec doc §"Why these exclusions").
    pub fn cast_op_excluded(op: CastOp) -> Option<&'static str> {
        match op {
            CastOp::ReifyFnPointer => {
                Some("CastOp::ReifyFnPointer has only fn-item-partial Lean semantics")
            }
            CastOp::FPToSISat | CastOp::FPToUISat => Some(
                "CastOp::FP*Sat has no proven bridge/ay cast lowering yet (Lean semCast semantics landed 2026-07-10)",
            ),
            CastOp::Trunc
            | CastOp::ZExt
            | CastOp::SExt
            | CastOp::FPTrunc
            | CastOp::FPExt
            | CastOp::FPToUI
            | CastOp::FPToSI
            | CastOp::UIToFP
            | CastOp::SIToFP
            | CastOp::PtrToInt
            | CastOp::IntToPtr
            | CastOp::PtrToPtr
            | CastOp::Transmute
            | CastOp::Bitcast => None,
        }
    }

    /// Reason an [`Inst`] is outside the subset, or `None` if in-subset.
    ///
    /// Inspects the instruction's *own* opcode plus the inline types it carries.
    pub fn inst_excluded(inst: &Inst) -> Option<&'static str> {
        match inst {
            Inst::Cast {
                op, src_ty, dst_ty, ..
            } => Self::cast_op_excluded(*op)
                .or_else(|| {
                    (*op == CastOp::Transmute
                        && !(transmute_scalar_ty(src_ty) && transmute_scalar_ty(dst_ty)))
                    .then_some(
                        "CastOp::Transmute is scalar-to-scalar only in the subset (Lean semCast scalar partial)",
                    )
                })
                .or_else(|| Self::ty_excluded(src_ty))
                .or_else(|| Self::ty_excluded(dst_ty)),
            Inst::PtrData { ptr_ty, .. } => Self::ty_excluded(ptr_ty).or_else(|| {
                (!ptr_trio_ty_supported(ptr_ty))
                    .then_some("Inst::PtrData requires an executable pointer-trio type")
            }),
            Inst::PtrMetadata {
                ptr_ty,
                metadata_ty,
                ..
            }
            | Inst::PtrFromParts {
                ptr_ty,
                metadata_ty,
                ..
            } => Self::ty_excluded(ptr_ty)
                .or_else(|| Self::ty_excluded(metadata_ty))
                .or_else(|| {
                    (!ptr_trio_ty_supported(ptr_ty)).then_some(
                        "pointer-trio instruction requires an executable pointer-trio type",
                    )
                })
                .or_else(|| {
                    (ptr_ty
                        .pointer_metadata_ty(crate::shape::DEFAULT_POINTER_BITS)
                        .as_ref()
                        != Some(metadata_ty))
                    .then_some(
                        "pointer-trio metadata type does not match the canonical 64-bit lane",
                    )
                }),
            Inst::DialectOp(op) => {
                if !SUBSET_DIALECT_OPS.contains(&op.qualified_name().as_str()) {
                    return Some(
                        "dialect op has no proven trust-ir lowering (only the ratified fast-4 `vector.*` set is in-subset)",
                    );
                }
                op.result_tys.iter().find_map(Self::ty_excluded)
            }
            Inst::CoroSuspend { .. } => Some(
                "Inst::CoroSuspend: the whole-module resume state-machine theorem is open (B3 depth ledger)",
            ),
            Inst::LandingPad { .. } => Some(
                "Inst::LandingPad: taken-unwind-edge selector dispatch is unmodelled (B3 depth ledger)",
            ),
            Inst::Resume { .. } => Some(
                "Inst::Resume: host unwinding is structured `unsupported.host_unwind` in the executable model (B3 depth ledger)",
            ),
            // Every other instruction is in-subset, but each one that carries an
            // inline `Ty` must still have that type be in-subset (e.g. a `Load`
            // of an `F16`). Surface that type via `Inst::result_tys` plus the
            // operand-type accessors the instruction exposes.
            other => Self::inst_inline_ty_excluded(other),
        }
    }

    /// Exclusion reason coming from an inline `Ty` an otherwise-in-subset
    /// instruction carries (operand or result type), or `None`.
    fn inst_inline_ty_excluded(inst: &Inst) -> Option<&'static str> {
        match inst {
            Inst::BinOp { ty, .. }
            | Inst::SeqMapAddK { ty, .. }
            | Inst::SeqMapNot { ty, .. }
            | Inst::SeqMap { ty, .. }
            | Inst::UnOp { ty, .. }
            | Inst::Overflow { ty, .. }
            | Inst::ICmp { ty, .. }
            | Inst::FCmp { ty, .. }
            | Inst::Load { ty, .. }
            | Inst::Store { ty, .. }
            | Inst::Alloca { ty, .. }
            | Inst::HeapAlloc { ty, .. }
            | Inst::AtomicLoad { ty, .. }
            | Inst::AtomicStore { ty, .. }
            | Inst::AtomicRMW { ty, .. }
            | Inst::CmpXchg { ty, .. }
            | Inst::ExtractField { ty, .. }
            | Inst::InsertField { ty, .. }
            | Inst::ExtractElement { ty, .. }
            | Inst::InsertElement { ty, .. }
            | Inst::Const { ty, .. }
            | Inst::Undef { ty }
            | Inst::Copy { ty, .. }
            | Inst::Select { ty, .. }
            | Inst::LoadSlot { ty, .. } => Self::ty_excluded(ty),
            Inst::GEP { pointee_ty, .. } => Self::ty_excluded(pointee_ty),
            Inst::OpenFrame { def } => def
                .slots
                .iter()
                .find_map(|slot| Self::ty_excluded(&slot.ty)),
            _ => None,
        }
    }

    /// Reason a [`ProofAnnotation`] is outside the subset, or `None`.
    ///
    /// The subset pins the annotation VOCABULARY only — a claim stays a claim
    /// (back it with `ProofRef`). Excluded: the producer-defined
    /// [`ProofAnnotation::Custom`] tag, whose meaning no spec pins, plus any
    /// variant the ratified v2 list never admitted (fail-closed). EXHAUSTIVE:
    /// a new annotation variant must take an explicit in/out decision here.
    pub fn proof_annotation_excluded(proof: &ProofAnnotation) -> Option<&'static str> {
        match proof {
            ProofAnnotation::Custom(_) => Some(
                "ProofAnnotation::Custom is producer-defined and not pinned by the subset contract",
            ),
            ProofAnnotation::FreshSymbolicHavoc => Some(
                "ProofAnnotation::FreshSymbolicHavoc is not ratified into lowering-target subset v2 (fail-closed)",
            ),
            #[cfg(feature = "clean-expr")]
            ProofAnnotation::Goal(_) => Some(
                "ProofAnnotation::Goal is feature-gated off the pinned default surface (fail-closed)",
            ),
            ProofAnnotation::InBounds
            | ProofAnnotation::NotNull
            | ProofAnnotation::ValidBorrow
            | ProofAnnotation::UniqueBorrow
            | ProofAnnotation::SharedBorrow
            | ProofAnnotation::ValidDealloc
            | ProofAnnotation::NoOverflow
            | ProofAnnotation::NoWrap
            | ProofAnnotation::DivNonZero
            | ProofAnnotation::ShiftInRange
            | ProofAnnotation::Wrapping
            | ProofAnnotation::Pure
            | ProofAnnotation::Terminates
            | ProofAnnotation::Deterministic
            | ProofAnnotation::Associative
            | ProofAnnotation::Commutative
            | ProofAnnotation::DataRaceFree
            | ProofAnnotation::AtomicOrdering(_)
            | ProofAnnotation::BoundedOutput { .. }
            | ProofAnnotation::Monotonic
            | ProofAnnotation::NoAlias
            | ProofAnnotation::Aligned(_)
            | ProofAnnotation::NoPanic
            | ProofAnnotation::NoUndef
            | ProofAnnotation::Tainted
            | ProofAnnotation::TrustedSink
            | ProofAnnotation::ReadonlyTable
            | ProofAnnotation::AppendOnlyBuffer
            | ProofAnnotation::AtomicSetInsert
            | ProofAnnotation::ParallelMap
            | ProofAnnotation::BoundedLoop(_)
            | ProofAnnotation::DivergenceClass(_)
            | ProofAnnotation::ProofRef(_)
            | ProofAnnotation::ValueRange { .. }
            | ProofAnnotation::KnownBits { .. }
            | ProofAnnotation::BranchWeights(_) => None,
        }
    }

    /// Check every function in `module` against this subset, returning all
    /// out-of-subset constructs as location-rich [`SubsetViolation`]s.
    ///
    /// Scope: block-parameter types, instruction opcodes + inline types, and
    /// proof annotations (function- and instruction-level) — the function
    /// emission surface. The whole-module wire surface (interned type tables,
    /// signatures, struct/enum/record fields, globals) is walked by the
    /// superset checker
    /// `trust_ir_conformance::subset::module_subset_violations`; the
    /// PER-CONSTRUCT verdicts of the two are pinned identical by that crate's
    /// `bridge_subset_agreement` gate.
    pub fn check(&self, module: &Module) -> Result<(), Vec<SubsetViolation>> {
        let mut violations = Vec::new();
        let fat_ptr_layout_supported = module_supports_fat_ptr_layout(module);
        for function in &module.functions {
            for (proof_index, proof) in function.proofs.iter().enumerate() {
                if let Some(reason) = Self::proof_annotation_excluded(proof) {
                    violations.push(SubsetViolation {
                        function: function.id,
                        block: function.entry,
                        instruction_index: None,
                        site: SubsetSite::FunctionProof { proof_index },
                        reason,
                    });
                }
            }
            for block in &function.blocks {
                for (param_index, (_value, ty)) in block.params.iter().enumerate() {
                    let reason = Self::ty_excluded(ty).or_else(|| {
                        (!fat_ptr_layout_supported && ty_contains_fat_ptr(ty))
                        .then_some(
                            "Ty::FatPtr conformance is pinned to the 64-bit little-endian executable model",
                        )
                    });
                    if let Some(reason) = reason {
                        violations.push(SubsetViolation {
                            function: function.id,
                            block: block.id,
                            instruction_index: None,
                            site: SubsetSite::BlockParamType { param_index },
                            reason,
                        });
                    }
                }
                for (instruction_index, node) in block.body.iter().enumerate() {
                    let reason = Self::inst_excluded(&node.inst).or_else(|| {
                        (!fat_ptr_layout_supported && inst_contains_fat_ptr(&node.inst))
                        .then_some(
                            "fat-pointer instruction conformance is pinned to the 64-bit little-endian executable model",
                        )
                    });
                    if let Some(reason) = reason {
                        violations.push(SubsetViolation {
                            function: function.id,
                            block: block.id,
                            instruction_index: Some(instruction_index),
                            site: SubsetSite::Instruction,
                            reason,
                        });
                    }
                    for (proof_index, proof) in node.proofs.iter().enumerate() {
                        if let Some(reason) = Self::proof_annotation_excluded(proof) {
                            violations.push(SubsetViolation {
                                function: function.id,
                                block: block.id,
                                instruction_index: Some(instruction_index),
                                site: SubsetSite::InstructionProof { proof_index },
                                reason,
                            });
                        }
                    }
                }
            }
        }
        if violations.is_empty() {
            Ok(())
        } else {
            Err(violations)
        }
    }
}

/// Where in a function a conformance-subset violation was found.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum SubsetSite {
    /// A block-parameter type is out of subset.
    BlockParamType { param_index: usize },
    /// An instruction (its opcode or an inline type it carries) is out of subset.
    Instruction,
    /// A proof annotation attached to an instruction is out of subset.
    InstructionProof { proof_index: usize },
    /// A function-level proof annotation is out of subset.
    /// `SubsetViolation::block` carries the function's entry block (the site
    /// is function-scoped; the variant is the discriminator).
    FunctionProof { proof_index: usize },
}

/// A single out-of-subset construct, located precisely for diagnostics.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SubsetViolation {
    pub function: FuncId,
    pub block: BlockId,
    /// Instruction index within the block when `site` is an instruction.
    pub instruction_index: Option<usize>,
    pub site: SubsetSite,
    /// Static, human-readable reason the construct is excluded.
    pub reason: &'static str,
}

impl core::fmt::Display for SubsetViolation {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.site {
            SubsetSite::BlockParamType { param_index } => write!(
                f,
                "conformance-subset violation in function {:?}, block {:?}, block-param {}: {}",
                self.function, self.block, param_index, self.reason
            ),
            SubsetSite::Instruction => write!(
                f,
                "conformance-subset violation in function {:?}, block {:?}, instruction {}: {}",
                self.function,
                self.block,
                self.instruction_index
                    .map_or_else(|| "?".to_string(), |i| i.to_string()),
                self.reason
            ),
            SubsetSite::InstructionProof { proof_index } => write!(
                f,
                "conformance-subset violation in function {:?}, block {:?}, instruction {}, proof {}: {}",
                self.function,
                self.block,
                self.instruction_index
                    .map_or_else(|| "?".to_string(), |i| i.to_string()),
                proof_index,
                self.reason
            ),
            SubsetSite::FunctionProof { proof_index } => write!(
                f,
                "conformance-subset violation in function {:?}, function-level proof {}: {}",
                self.function, proof_index, self.reason
            ),
        }
    }
}

impl Module {
    /// Return typed SSA metadata for the function identified by `id`.
    pub fn typed_values_for_function(&self, id: FuncId) -> Option<Vec<TypedValueMetadata>> {
        self.function_by_id(id)
            .map(|function| function.typed_values(self))
    }

    /// Check this module against the current pinned conformance subset
    /// ([`ConformanceSubset::CURRENT`]).
    ///
    /// This is the frontend-emission gate: a conforming producer (tRust,
    /// Clean) calls this after building and before handoff to confirm the module
    /// uses only the fully-modelled instruction/type surface. See the
    /// module-level "Frontend-emission handshake" docs.
    pub fn check_conformance_subset(&self) -> Result<(), Vec<SubsetViolation>> {
        ConformanceSubset::CURRENT.check(self)
    }

    /// Validate the x86 CHC vector-select mask contract for every function.
    ///
    /// This is deliberately narrow: it only checks vector selects. Scalar select
    /// behavior is unchanged, and physical integer masks are never accepted as
    /// logical vector conditions.
    pub fn validate_vector_select_contracts(&self) -> Result<(), Vec<VectorSelectContractError>> {
        let mut errors = Vec::new();
        for function in &self.functions {
            errors.extend(function.vector_select_contract_errors(self));
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

impl Function {
    /// Return typed SSA metadata for this function.
    ///
    /// The result includes block parameters and instruction results in module
    /// order. Call and indirect-call result types are resolved through
    /// `module`; result types that cannot be resolved are omitted rather than
    /// guessed.
    pub fn typed_values(&self, module: &Module) -> Vec<TypedValueMetadata> {
        let mut values = Vec::new();

        for block in &self.blocks {
            for (param_index, (value, ty)) in block.params.iter().enumerate() {
                values.push(TypedValueMetadata {
                    value: *value,
                    ty: ty.clone(),
                    origin: ValueMetadataOrigin::BlockParam {
                        block: block.id,
                        param_index,
                    },
                    proofs: Vec::new(),
                    span: None,
                });
            }

            for (instruction_index, node) in block.body.iter().enumerate() {
                for (result_index, (value, ty)) in
                    node.results.iter().zip(node.result_tys(module)).enumerate()
                {
                    values.push(TypedValueMetadata {
                        value: *value,
                        ty,
                        origin: ValueMetadataOrigin::InstrResult {
                            block: block.id,
                            instruction_index,
                            result_index,
                        },
                        proofs: node.proofs.clone(),
                        span: node.span,
                    });
                }
            }
        }

        // Phase 2: a borrow's result type depends on its operand, and block
        // order does not guarantee the operand's definition was walked first.
        // The snapshot deliberately carries the PROVISIONAL `Ty::Ptr` that
        // phase 1 wrote for every borrow; `borrow_result_types` never consults
        // it for a borrow result, so a borrow-of-borrow chain still collapses
        // to its true root.
        let declared: BTreeMap<ValueId, Ty> = values
            .iter()
            .map(|entry| (entry.value, entry.ty.clone()))
            .collect();
        let resolved: BTreeMap<ValueId, Ty> =
            borrow_result_types(self, &|value| declared.get(&value).cloned())
                .into_iter()
                .collect();
        for entry in &mut values {
            if let Some(ty) = resolved.get(&entry.value) {
                entry.ty = ty.clone();
            }
        }

        values
    }

    /// Resolve a typed SSA value in this function.
    pub fn typed_value(&self, module: &Module, value: ValueId) -> Option<TypedValueMetadata> {
        self.typed_values(module)
            .into_iter()
            .find(|metadata| metadata.value == value)
    }

    /// Return all vector-select condition type violations in this function.
    pub fn vector_select_contract_errors(&self, module: &Module) -> Vec<VectorSelectContractError> {
        let mut errors = Vec::new();
        let mut value_tys = BTreeMap::<ValueId, Ty>::new();

        // Borrow result types are resolved up front against a FULL snapshot,
        // because block order does not guarantee a borrow's operand is walked
        // before the borrow.
        //
        // This upgrades only the type this pass REPORTS for a borrow. Which
        // conditions get checked still follows the walk below — a cond whose
        // definition has not been reached is still `UnknownConditionType` — so
        // no verdict moves: neither `Ty::Ptr` nor `Ty::FatPtr` is a vector, so
        // `validate_select_condition_ty` rejects a borrow cond either way.
        // What changes is that `actual_cond_ty` names the fat type the value
        // really has instead of a thin `ptr` it does not, and a diagnostic
        // that states a falsehood is a defect even when the verdict is right.
        let mut declared = BTreeMap::<ValueId, Ty>::new();
        for block in &self.blocks {
            for (value, ty) in &block.params {
                declared.insert(*value, ty.clone());
            }
            for node in &block.body {
                for (value, ty) in node.results.iter().zip(node.result_tys(module)) {
                    declared.insert(*value, ty);
                }
            }
        }
        let resolved: BTreeMap<ValueId, Ty> =
            borrow_result_types(self, &|value| declared.get(&value).cloned())
                .into_iter()
                .collect();

        for block in &self.blocks {
            for (value, ty) in &block.params {
                value_tys.insert(*value, ty.clone());
            }

            for (instruction_index, node) in block.body.iter().enumerate() {
                if let Inst::Select { ty, cond, .. } = &node.inst
                    && ty.is_vector()
                {
                    let expected_cond_ty = Inst::required_select_condition_ty(ty);
                    match value_tys.get(cond) {
                        Some(actual_cond_ty) => {
                            if let Err(reason) =
                                Inst::validate_select_condition_ty(ty, actual_cond_ty)
                            {
                                errors.push(VectorSelectContractError {
                                    function: self.id,
                                    block: block.id,
                                    instruction_index,
                                    cond: *cond,
                                    select_ty: ty.clone(),
                                    expected_cond_ty,
                                    actual_cond_ty: Some(actual_cond_ty.clone()),
                                    kind: vector_select_error_kind(reason),
                                });
                            }
                        }
                        None => errors.push(VectorSelectContractError {
                            function: self.id,
                            block: block.id,
                            instruction_index,
                            cond: *cond,
                            select_ty: ty.clone(),
                            expected_cond_ty,
                            actual_cond_ty: None,
                            kind: VectorSelectContractErrorKind::UnknownConditionType,
                        }),
                    }
                }

                for (value, ty) in node.results.iter().zip(node.result_tys(module)) {
                    value_tys.insert(*value, resolved.get(value).cloned().unwrap_or(ty));
                }
            }
        }

        errors
    }
}

fn vector_select_error_kind(reason: SelectConditionTypeError) -> VectorSelectContractErrorKind {
    match reason {
        SelectConditionTypeError::TypeMismatch { .. } => {
            VectorSelectContractErrorKind::TypeMismatch
        }
        SelectConditionTypeError::PhysicalIntegerMaskRequiresCompareToZero { .. } => {
            VectorSelectContractErrorKind::PhysicalIntegerMaskRequiresCompareToZero
        }
    }
}

impl InstrNode {
    /// Return declared result types for this node, in result order.
    ///
    /// Multi-result instructions (`Overflow`, `CmpXchg`, calls, dialect ops)
    /// are expanded so consumers can keep result metadata aligned with
    /// `InstrNode::results`.
    pub fn result_tys(&self, module: &Module) -> Vec<Ty> {
        inst_result_tys(&self.inst, module)
    }
}

/// The result type of a `Borrow` / `BorrowMut` over an operand of type
/// `operand_ty`: the operand's own type when that type is FAT, `Ty::Ptr`
/// otherwise.
///
/// This is THE statement of the borrow result rule. Both the bridge's
/// [`InstrNode::result_tys`] and `trust-ir-build`'s `infer_result_type` call
/// it rather than restating it — a drifted mirror of this rule is what let a
/// fat borrow be typed `ptr` while the interpreter passed the fat value
/// through, so every fat consumer downstream reported a bogus mismatch.
///
/// # Why not simply follow the operand
///
/// The rule is deliberately NOT "the result has the operand's type". The
/// operational semantics normalise the THIN spellings: `interpret.rs` (the
/// `Inst::Borrow { ptr } | Inst::BorrowMut { ptr }` arm) returns the operand
/// value VERBATIM — same `ty`, both lanes untouched — only when the value is
/// a `FatPtr`, and otherwise constructs a fresh `InterpretValue` at
/// `ty: Ty::Ptr`, discarding the operand's `Ty::Ref` / `Ty::PtrConst` /
/// `Ty::Rc` spelling. Returning the operand's spelling for a thin borrow
/// would therefore be a NEW static/dynamic drift of exactly the kind this
/// function exists to end.
///
/// # Residues (both fail CLOSED)
///
/// * An operand whose type this pass cannot give — a `Call`, `CallIndirect`
///   or `LandingPad` result, or a value with no definition — answers `None`
///   here and so `Ty::Ptr`. That is unchanged from the behaviour before this
///   rule existed. If the value is really fat, the first fat consumer reports
///   a mismatch and the module is REFUSED; refusal strips proof authority, it
///   never grants it.
/// * `Ty::Refine(base, pred)` over a fat pointer is NOT fat here, because
///   [`Ty::is_fat_pointer`] is `matches!(self, Ty::FatPtr(_))` and does not
///   peel a refinement. A refined fat borrow therefore answers `Ty::Ptr` and
///   produces a false RED at its first fat consumer — never a false green.
///   Peeling the refinement is a real extension, and whoever makes it owes a
///   derivation that the peeled type is the one the interpreter passes
///   through.
pub fn borrow_result_ty(operand_ty: Option<&Ty>) -> Ty {
    match operand_ty {
        Some(ty) if ty.is_fat_pointer() => ty.clone(),
        _ => Ty::Ptr,
    }
}

/// Resolve the result type of every `Borrow` / `BorrowMut` in `func`, given a
/// lookup `known` for the types this caller has already established.
///
/// `Borrow` is the only instruction whose result type depends on an OPERAND,
/// so it cannot be answered by the per-instruction interface
/// ([`InstrNode::result_tys`]) at all. Every caller that owns a whole function
/// runs this as a second phase over its own value-type map and OVERWRITES the
/// provisional `Ty::Ptr` that phase one wrote.
///
/// # Why two phases
///
/// A [`Function`] carries its entry block as `Function::entry`, so the order
/// of `Function::blocks` is free: a borrow may be walked before the block that
/// defines its operand. One forward pass would therefore read the operand as
/// absent and answer `Ty::Ptr` for a fat borrow, which is the defect this
/// resolves.
///
/// # Why the chain walk ignores `known` until the root
///
/// `known` is typically a PARTIALLY BUILT map that already holds the
/// provisional `Ty::Ptr` for other borrows. Consulting it for a value that is
/// itself a borrow result would short-circuit a borrow-of-borrow chain at that
/// provisional entry and answer `Ty::Ptr` for a chain whose root is fat. So the
/// walk follows `operand_of` FIRST and UNCONDITIONALLY, and consults `known`
/// only on reaching a value no borrow defines.
///
/// A malformed borrow cycle (`%1 = Borrow %1`) has no root. The walk is bounded
/// by the number of borrow results, so it TERMINATES and answers `Ty::Ptr`
/// rather than looping; the cycle itself is a dominance/SSA defect that the
/// passes owning that question report.
///
/// Returns owned pairs rather than mutating a map: that ends the borrow `known`
/// holds before the caller mutates the map `known` reads.
pub fn borrow_result_types(
    func: &Function,
    known: &dyn Fn(ValueId) -> Option<Ty>,
) -> Vec<(ValueId, Ty)> {
    // Phase A: every borrow result, mapped to the value it borrows.
    let mut operand_of = BTreeMap::<ValueId, ValueId>::new();
    for block in &func.blocks {
        for node in &block.body {
            if let Inst::Borrow { ptr } | Inst::BorrowMut { ptr } = &node.inst
                && let Some(result) = node.results.first()
            {
                operand_of.insert(*result, *ptr);
            }
        }
    }

    // Phase B: collapse each chain to its root, then apply the shared rule.
    let bound = operand_of.len();
    let mut resolved = Vec::with_capacity(operand_of.len());
    for result in operand_of.keys() {
        let mut cursor = *result;
        let mut steps = 0usize;
        let root = loop {
            match operand_of.get(&cursor) {
                Some(operand) => {
                    steps += 1;
                    if steps > bound {
                        // Pigeonhole: more hops than there are borrow results
                        // means a cycle, which has no root to type from.
                        break None;
                    }
                    cursor = *operand;
                }
                None => break Some(cursor),
            }
        };
        let operand_ty = root.and_then(known);
        resolved.push((*result, borrow_result_ty(operand_ty.as_ref())));
    }

    resolved
}

fn inst_result_tys(inst: &Inst, module: &Module) -> Vec<Ty> {
    match inst {
        Inst::BinOp { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::Const { ty, .. }
        | Inst::Undef { ty }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::LoadSlot { ty, .. }
        | Inst::PtrMetadata {
            metadata_ty: ty, ..
        }
        | Inst::PtrFromParts { ptr_ty: ty, .. }
        | Inst::SeqMapAddK { ty, .. }
        | Inst::SeqMapNot { ty, .. }
        | Inst::SeqMap { ty, .. } => vec![ty.clone()],
        Inst::Cast { dst_ty, .. } => vec![dst_ty.clone()],
        Inst::Overflow { ty, .. } | Inst::CmpXchg { ty, .. } => {
            vec![ty.clone(), Ty::Bool]
        }
        Inst::ICmp { ty, .. } | Inst::FCmp { ty, .. } => vec![ty.comparison_result_ty()],
        Inst::IsUnique { .. } => vec![Ty::Bool],
        Inst::Alloca { .. }
        | Inst::HeapAlloc { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. } => vec![Ty::Ptr],
        // A borrow's result type depends on its OPERAND, which this
        // per-instruction interface cannot see. It answers the thin default,
        // which `borrow_result_types` then OVERWRITES at every site that owns
        // the whole function. This arm holds no independent statement of the
        // rule; it defers to `borrow_result_ty`, and its arity stays 1 for
        // `validate_instruction_result_arities`.
        Inst::Borrow { .. } | Inst::BorrowMut { .. } => vec![borrow_result_ty(None)],
        // Invoke produces the callee's return values on the normal edge,
        // exactly like a direct `Call`.
        Inst::Call { callee, .. } | Inst::Invoke { callee, .. } => module
            .function_by_id(*callee)
            .and_then(|callee| module.func_type(callee.ty))
            .map(|ty| ty.returns.clone())
            .unwrap_or_default(),
        Inst::CallIndirect { sig, .. } => module
            .func_type(*sig)
            .map(|ty| ty.returns.clone())
            .unwrap_or_default(),
        Inst::DialectOp(op) => op.result_tys.clone(),
        // A landing pad produces the exception object pointer and the type
        // selector the unwinder leaves in the platform ABI registers.
        Inst::LandingPad { .. } => vec![Ty::Ptr, Ty::I32],
        Inst::Store { .. }
        | Inst::AtomicStore { .. }
        | Inst::Fence { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Return { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::Unreachable
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::Dealloc { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        // Resume produces no result.
        | Inst::Resume { .. } => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BinOp, Constant, FuncTy, ProofAnnotation};

    fn v(index: u32) -> ValueId {
        ValueId::new(index)
    }

    fn b(index: u32) -> BlockId {
        BlockId::new(index)
    }

    #[test]
    fn typed_values_include_params_results_and_producer_metadata() {
        let mut module = Module::new("bridge-metadata");
        let callee_ty = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::U64, Ty::Bool],
            is_vararg: false,
        });
        let caller_ty = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        let mut callee = Function::new(FuncId::new(0), "callee", callee_ty, b(0));
        callee.blocks.push(crate::Block::new(b(0)));
        module.add_function(callee);

        let mut caller = Function::new(FuncId::new(1), "caller", caller_ty, b(1));
        let mut block = crate::Block::new(b(1)).with_param(v(0), Ty::I32);
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(1))
            .with_proof(ProofAnnotation::NoOverflow)
            .with_span(SourceSpan {
                file: 7,
                line: 11,
                col: 3,
            }),
        );
        block.body.push(
            InstrNode::new(Inst::Overflow {
                op: crate::OverflowOp::AddOverflow,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_results([v(2), v(3)]),
        );
        block.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![v(2)],
            })
            .with_results([v(4), v(5)]),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(6)),
        );
        caller.blocks.push(block);
        module.add_function(caller);

        let metadata = module
            .typed_values_for_function(FuncId::new(1))
            .expect("caller metadata");
        let ty_of = |value| {
            metadata
                .iter()
                .find(|entry| entry.value == value)
                .map(|entry| entry.ty.clone())
        };

        assert_eq!(ty_of(v(0)), Some(Ty::I32));
        assert_eq!(ty_of(v(1)), Some(Ty::I32));
        assert_eq!(ty_of(v(2)), Some(Ty::I32));
        assert_eq!(ty_of(v(3)), Some(Ty::Bool));
        assert_eq!(ty_of(v(4)), Some(Ty::U64));
        assert_eq!(ty_of(v(5)), Some(Ty::Bool));
        assert_eq!(ty_of(v(6)), Some(Ty::I32));

        let produced_const = metadata.iter().find(|entry| entry.value == v(1)).unwrap();
        assert_eq!(
            produced_const.origin,
            ValueMetadataOrigin::InstrResult {
                block: b(1),
                instruction_index: 0,
                result_index: 0,
            }
        );
        assert_eq!(produced_const.proofs, vec![ProofAnnotation::NoOverflow]);
        assert_eq!(
            produced_const.span,
            Some(SourceSpan {
                file: 7,
                line: 11,
                col: 3,
            })
        );
    }

    #[test]
    fn vector_compare_results_are_vector_bool_masks() {
        let module = Module::new("vector-bridge");
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let v4bool = Ty::Vector(Box::new(Ty::Bool), 4);
        let node = InstrNode::new(Inst::ICmp {
            op: crate::ICmpOp::Eq,
            ty: v4i32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(2));

        assert_eq!(node.result_tys(&module), vec![v4bool]);
    }

    #[test]
    fn vector_select_contract_accepts_compare_to_zero_condition() {
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let mut module = Module::new("vector-select-valid");
        let ft = module.add_func_type(FuncTy {
            params: vec![v4i32.clone(), v4i32.clone(), v4i32.clone()],
            returns: vec![v4i32.clone()],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "select_valid", ft, b(0));
        let mut block = crate::Block::new(b(0))
            .with_param(v(0), v4i32.clone())
            .with_param(v(1), v4i32.clone())
            .with_param(v(2), v4i32.clone());
        block.body.push(
            InstrNode::new(Inst::ICmp {
                op: crate::ICmpOp::Ne,
                ty: v4i32.clone(),
                lhs: v(0),
                rhs: v(2),
            })
            .with_result(v(3)),
        );
        block.body.push(
            InstrNode::new(Inst::Select {
                ty: v4i32,
                cond: v(3),
                then_val: v(1),
                else_val: v(2),
            })
            .with_result(v(4)),
        );
        func.blocks.push(block);
        module.add_function(func);

        module
            .validate_vector_select_contracts()
            .expect("compare result is <4 x bool>");
    }

    #[test]
    fn vector_select_contract_rejects_physical_i32_mask_condition() {
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let mut module = Module::new("vector-select-invalid");
        let ft = module.add_func_type(FuncTy {
            params: vec![v4i32.clone(), v4i32.clone(), v4i32.clone()],
            returns: vec![v4i32.clone()],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "select_invalid", ft, b(0));
        let mut block = crate::Block::new(b(0))
            .with_param(v(0), v4i32.clone())
            .with_param(v(1), v4i32.clone())
            .with_param(v(2), v4i32.clone());
        block.body.push(
            InstrNode::new(Inst::Select {
                ty: v4i32,
                cond: v(0),
                then_val: v(1),
                else_val: v(2),
            })
            .with_result(v(3)),
        );
        func.blocks.push(block);
        module.add_function(func);

        let errors = module
            .validate_vector_select_contracts()
            .expect_err("physical i32 masks must not be select conditions");
        assert_eq!(errors.len(), 1);
        assert_eq!(
            errors[0].kind,
            VectorSelectContractErrorKind::PhysicalIntegerMaskRequiresCompareToZero
        );
        assert!(
            errors[0].to_string().contains("compared to zero"),
            "{}",
            errors[0]
        );
    }

    // --- Frontend-emission handshake: worked example + subset gate ---------

    /// Build a small two-function module the way a frontend (tRust) does:
    /// intern a source file, thread a [`SourceSpan`] onto every emitted node,
    /// and emit only in-subset constructs. Then walk the documented handshake:
    ///
    ///   build-with-spans  ->  `check_conformance_subset`  ->  spans surface
    ///   back through `typed_values`  ->  round-trips bit-identically.
    ///
    /// This mirrors what `ModuleBuilder::intern_file` + `FunctionBuilder::set_span`
    /// produce; spans are set on the `InstrNode` directly here so the worked
    /// example stays inside the dependency-free `trust-ir` crate.
    fn emit_two_function_module_with_spans() -> Module {
        let mut module = Module::new("frontend-emission-demo");
        // Step 1a: the source-file index every node's `SourceSpan::file` points
        // at (a frontend interns its file table once; here we use index 0).
        let file = 0u32;

        // fn#0 `inc`: x: i32 -> i32, returns x + 1, every node carries a span.
        let inc_ty = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let main_ty = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        let mut inc = Function::new(FuncId::new(0), "inc", inc_ty, b(0));
        let mut blk = crate::Block::new(b(0)).with_param(v(0), Ty::I32);
        blk.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(1))
            .with_span(SourceSpan {
                file,
                line: 2,
                col: 13,
            }),
        );
        blk.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2))
            .with_proof(ProofAnnotation::NoOverflow)
            .with_span(SourceSpan {
                file,
                line: 2,
                col: 5,
            }),
        );
        blk.body.push(
            InstrNode::new(Inst::Return { values: vec![v(2)] }).with_span(SourceSpan {
                file,
                line: 2,
                col: 5,
            }),
        );
        inc.blocks.push(blk);
        module.add_function(inc);

        // fn#1 `main`: () -> i32, calls inc(41).
        let mut main = Function::new(FuncId::new(1), "main", main_ty, b(0));
        let mut blk = crate::Block::new(b(0));
        blk.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(41),
            })
            .with_result(v(0))
            .with_span(SourceSpan {
                file,
                line: 5,
                col: 18,
            }),
        );
        blk.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![v(0)],
            })
            .with_result(v(1))
            .with_span(SourceSpan {
                file,
                line: 5,
                col: 5,
            }),
        );
        blk.body.push(
            InstrNode::new(Inst::Return { values: vec![v(1)] }).with_span(SourceSpan {
                file,
                line: 5,
                col: 5,
            }),
        );
        main.blocks.push(blk);
        module.add_function(main);

        module
    }

    #[test]
    fn frontend_emission_handshake_worked_example() {
        let module = emit_two_function_module_with_spans();

        // Step 2: the module stays inside the pinned conformance subset.
        module
            .check_conformance_subset()
            .expect("worked-example module is in-subset");
        assert_eq!(ConformanceSubset::CURRENT.version, 2);

        // Step 1c: per-instruction provenance is recoverable. Every produced
        // value carries the threaded span (no node was emitted span-less).
        let inc_meta = module
            .typed_values_for_function(FuncId::new(0))
            .expect("inc metadata");
        let produced: Vec<_> = inc_meta
            .iter()
            .filter(|m| matches!(m.origin, ValueMetadataOrigin::InstrResult { .. }))
            .collect();
        assert!(!produced.is_empty());
        assert!(
            produced.iter().all(|m| m.span.is_some()),
            "every emitted node carries a threaded span"
        );
        // The add carries both its proof and its span.
        let add = inc_meta.iter().find(|m| m.value == v(2)).unwrap();
        assert_eq!(add.proofs, vec![ProofAnnotation::NoOverflow]);
        assert_eq!(
            add.span,
            Some(SourceSpan {
                file: 0,
                line: 2,
                col: 5
            })
        );
    }

    #[cfg(all(feature = "binary", feature = "serde"))]
    #[test]
    fn frontend_emission_module_round_trips() {
        let module = emit_two_function_module_with_spans();

        // Binary codec round-trip preserves the module (including threaded spans
        // and the debug-info file table).
        let bytes = crate::binary::serialize_module(&module);
        let back = crate::binary::deserialize_module(&bytes).expect("binary round-trips");
        assert_eq!(back, module);
        // Idempotent re-encode is byte-identical (the wire-format guarantee a
        // downstream consumer pins against).
        assert_eq!(crate::binary::serialize_module(&back), bytes);

        // JSON round-trip via serde.
        let json = serde_json::to_string(&module).expect("serialize json");
        let from_json: Module = serde_json::from_str(&json).expect("deserialize json");
        assert_eq!(from_json, module);

        // The round-tripped module is still in-subset.
        back.check_conformance_subset()
            .expect("round-tripped module stays in-subset");
    }

    #[test]
    fn conformance_subset_rejects_partial_semantics_constructs_with_locations() {
        let mut module = Module::new("out-of-subset");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "bad", ft, b(0));
        // A block param typed F16 (out of subset).
        let mut blk = crate::Block::new(b(0))
            .with_param(v(0), Ty::Ptr)
            .with_param(v(1), Ty::F16);
        // A NON-SCALAR Transmute (scalar-to-scalar is in-subset; aggregate
        // transmutes are the depth-ledger partial that stays out).
        blk.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::Transmute,
                src_ty: Ty::Tuple(vec![Ty::I32, Ty::I32]),
                dst_ty: Ty::I64,
                operand: v(0),
            })
            .with_result(v(2)),
        );
        // A pointer-width integer value (depth-ledger adoption still pending).
        blk.body
            .push(InstrNode::new(Inst::Undef { ty: Ty::Usize }).with_result(v(3)));
        // A Load of an F16 — in-subset opcode, out-of-subset inline type.
        blk.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::F16,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(4)),
        );
        func.blocks.push(blk);
        module.add_function(func);

        let violations = module
            .check_conformance_subset()
            .expect_err("module uses partial-semantics constructs");

        // F16 block param.
        assert!(violations.iter().any(|x| matches!(
            x.site,
            SubsetSite::BlockParamType { param_index: 1 }
        ) && x.reason.contains("F16")));
        // Transmute at instruction 0.
        assert!(
            violations
                .iter()
                .any(|x| x.instruction_index == Some(0) && x.reason.contains("Transmute"))
        );
        // Usize at instruction 1.
        assert!(
            violations
                .iter()
                .any(|x| x.instruction_index == Some(1) && x.reason.contains("Usize"))
        );
        // F16 Load at instruction 2 (inline-type exclusion on an in-subset op).
        assert!(
            violations
                .iter()
                .any(|x| x.instruction_index == Some(2) && x.reason.contains("F16"))
        );

        // Violations are precisely located + Display-able.
        let any = &violations[0];
        assert_eq!(any.function, FuncId::new(0));
        assert!(!any.to_string().is_empty());
    }

    #[test]
    fn conformance_subset_recurses_into_composite_types() {
        // A vector/tuple/ref whose element is F16 is out of subset; an all-clean
        // composite is in subset.
        assert!(ConformanceSubset::ty_excluded(&Ty::Vector(Box::new(Ty::F16), 4)).is_some());
        assert!(ConformanceSubset::ty_excluded(&Ty::Tuple(vec![Ty::I32, Ty::F16])).is_some());
        assert!(ConformanceSubset::ty_excluded(&Ty::Ref(Box::new(Ty::F16))).is_some());
        assert!(ConformanceSubset::ty_excluded(&Ty::Tuple(vec![Ty::I32, Ty::I64])).is_none());
        assert!(ConformanceSubset::ty_excluded(&Ty::Vector(Box::new(Ty::I32), 4)).is_none());
        assert!(ConformanceSubset::ty_excluded(&Ty::FatPtr(crate::FatPtrKind::Str)).is_none());
        // ReifyFnPointer / FP*Sat casts are out; PtrToPtr, Transmute (op
        // level — the scalar condition is structural) and ZExt are in.
        assert!(ConformanceSubset::cast_op_excluded(CastOp::ReifyFnPointer).is_some());
        assert!(ConformanceSubset::cast_op_excluded(CastOp::FPToSISat).is_some());
        assert!(ConformanceSubset::cast_op_excluded(CastOp::FPToUISat).is_some());
        assert!(ConformanceSubset::cast_op_excluded(CastOp::PtrToPtr).is_none());
        assert!(ConformanceSubset::cast_op_excluded(CastOp::Transmute).is_none());
        assert!(ConformanceSubset::cast_op_excluded(CastOp::ZExt).is_none());
    }

    #[test]
    fn conformance_subset_v2_admits_fat_pointer_trio_on_64_bit_only() {
        let fat = Ty::FatPtr(crate::FatPtrKind::Str);
        let wrong_metadata = Inst::PtrMetadata {
            ptr_ty: fat.clone(),
            metadata_ty: Ty::U32,
            ptr: v(0),
        };
        assert!(
            ConformanceSubset::inst_excluded(&wrong_metadata)
                .is_some_and(|reason| reason.contains("canonical 64-bit")),
            "v2 must reject a non-canonical fat-pointer metadata lane"
        );
        let mut module = Module::new("fatptr-subset-v2");
        let ft = module.add_func_type(FuncTy {
            params: vec![fat.clone(), Ty::Ptr, Ty::U64],
            returns: vec![],
            is_vararg: false,
        });
        let mut function = Function::new(FuncId::new(0), "fat", ft, b(0));
        let mut block = crate::Block::new(b(0))
            .with_param(v(0), fat.clone())
            .with_param(v(1), Ty::Ptr)
            .with_param(v(2), Ty::U64);
        block.body.push(
            InstrNode::new(Inst::PtrData {
                ptr_ty: fat.clone(),
                ptr: v(0),
            })
            .with_result(v(3)),
        );
        block.body.push(
            InstrNode::new(Inst::PtrMetadata {
                ptr_ty: fat.clone(),
                metadata_ty: Ty::U64,
                ptr: v(0),
            })
            .with_result(v(4)),
        );
        block.body.push(
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty: fat,
                metadata_ty: Ty::U64,
                data: v(1),
                metadata: v(2),
            })
            .with_result(v(5)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        module.add_function(function);

        module
            .check_conformance_subset()
            .expect("v2 admits first-class fat pointers on the default 64-bit target");

        module.target_info = Some(crate::TargetInfo {
            triple: "i686-unknown-linux-gnu".into(),
            pointer_size: 4,
            endianness: crate::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        let violations = module
            .check_conformance_subset()
            .expect_err("v2 must fail closed on non-64-bit fat pointers");
        assert!(
            violations
                .iter()
                .any(|violation| violation.reason.contains("pinned to the 64-bit")),
            "{violations:?}"
        );

        let target = module.target_info.as_mut().expect("target");
        target.pointer_size = 8;
        target.endianness = crate::Endianness::Big;
        let violations = module
            .check_conformance_subset()
            .expect_err("v2 must fail closed on big-endian fat pointers");
        assert!(
            violations
                .iter()
                .any(|violation| violation.reason.contains("little-endian")),
            "{violations:?}"
        );
    }

    // ── Fat-borrow result typing ──────────────────────────────────────────
    //
    // `Borrow` is the only instruction whose result type depends on an
    // OPERAND. `interpret.rs` has passed a fat borrow through verbatim since
    // submodule commit 5129223; the STATIC half of that rule is
    // `borrow_result_ty` + `borrow_result_types`, and these are its guards.
    //
    // Every one of these tests uses a FAT operand deliberately. Under the
    // OVERWRITE structure a THIN borrow answers `Ty::Ptr` whether or not phase
    // 2 ran, so a thin-operand test is BLIND to a deleted resolve call and
    // would guard nothing.
    //
    // NOT CLAIMED, stated so no one mistakes silence for coverage: no test
    // here catches reverting `inst_result_tys`'s
    // `Inst::Borrow { .. } | Inst::BorrowMut { .. } => vec![borrow_result_ty(None)]`
    // arm to a literal `vec![Ty::Ptr]`. That revert is a genuine NO-OP —
    // `borrow_result_ty(None)` IS `Ty::Ptr` — so no observation can separate
    // them. The arm's value is deferral of the STATEMENT, not of the value.

    /// A one-function module whose entry block takes `operand_ty` as its only
    /// parameter, `%1 = Borrow %0`, and nothing else.
    fn module_borrowing_a_param(operand_ty: Ty) -> Module {
        let mut module = Module::new("borrow-result-ty");
        let ft = module.add_func_type(FuncTy {
            params: vec![operand_ty.clone()],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "borrows", ft, b(0));
        let mut block = crate::Block::new(b(0)).with_param(v(0), operand_ty);
        block
            .body
            .push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
        func.blocks.push(block);
        module.add_function(func);
        module
    }

    fn ty_of(module: &Module, value: ValueId) -> Option<Ty> {
        module
            .typed_values_for_function(FuncId::new(0))
            .expect("function metadata")
            .into_iter()
            .find(|entry| entry.value == value)
            .map(|entry| entry.ty)
    }

    /// THE HEADLINE. A borrow over a fat pointer is typed at the FAT type, not
    /// `ptr` — which is exactly what `bb10: cast bitcast operand type ptr does
    /// not match declared source type fatptr<slice ty.0>` was reporting.
    ///
    /// MUTATION A — delete the fat arm of `borrow_result_ty`, leaving
    /// `_ => Ty::Ptr`. NOT NEUTRALISED: `typed_values` writes this value's type
    /// exactly twice, and BOTH writes bottom out in `borrow_result_ty`. Phase 1
    /// is `inst_result_tys`, whose borrow arm is `vec![borrow_result_ty(None)]`
    /// and therefore `Ty::Ptr` under this mutation; phase 2 is
    /// `borrow_result_types`, whose only source of a type is the same mutated
    /// function. No third path can supply `FatPtr`.
    ///
    /// MUTATION B — delete the phase-2 block in `typed_values`. NOT
    /// NEUTRALISED: phase 1 answers `borrow_result_ty(None)` = `Ty::Ptr` for
    /// every borrow unconditionally, because the per-instruction interface
    /// cannot see the operand at all. This is the mutation that a previous
    /// attempt's headline guard SURVIVED, because that design let phase 1
    /// answer the fat type on its own; under overwrite it cannot.
    #[test]
    fn borrow_of_a_fat_pointer_keeps_the_fat_type() {
        let fat = Ty::FatPtr(crate::FatPtrKind::Str);
        let module = module_borrowing_a_param(fat.clone());
        assert_eq!(ty_of(&module, v(1)), Some(fat));
    }

    /// The rule is NOT "follow the operand": the interpreter rewrites every
    /// THIN spelling to `Ty::Ptr` (it constructs a fresh
    /// `InterpretValue { ty: Ty::Ptr, .. }` for a non-`FatPtr` operand), so
    /// answering `Ty::Ref(i32)` here would be a NEW static/dynamic drift of
    /// exactly the kind this change exists to end.
    ///
    /// MUTATION — make `borrow_result_ty` follow the operand unconditionally
    /// (`Some(ty) => ty.clone()`). NOT NEUTRALISED: phase 2 OVERWRITES phase
    /// 1's `Ty::Ptr` for every borrow, so the mutated answer is the one that
    /// survives into the metadata. The `assert_ne!` names the wrong answer
    /// explicitly so the failure reads as the drift it is.
    #[test]
    fn borrow_of_a_thin_reference_normalises_to_ptr() {
        let thin = Ty::Ref(Box::new(Ty::I32));
        let module = module_borrowing_a_param(thin.clone());
        assert_eq!(ty_of(&module, v(1)), Some(Ty::Ptr));
        assert_ne!(ty_of(&module, v(1)), Some(thin));
    }

    /// `Function::entry` carries the entry block, so the ORDER of
    /// `Function::blocks` is free: a borrow can be walked before the block that
    /// defines its operand. Blocks are listed `[bb1, bb0]` with `entry = bb0`,
    /// and the borrow in bb1 is walked FIRST.
    ///
    /// MUTATION — resolve borrows inline during the phase-1 walk of
    /// `typed_values` (compute each borrow's type from the values pushed so
    /// far) instead of in a second phase, i.e. ANY single forward pass. The
    /// operand `%0` has not been pushed when the borrow is reached, so the
    /// lookup answers `None` and the borrow types as `Ty::Ptr`.
    ///
    /// NOT NEUTRALISED, and specifically NOT caught by
    /// `borrow_of_a_fat_pointer_keeps_the_fat_type`, whose operand is a
    /// parameter of the SAME block and therefore already pushed. That is why
    /// this test exists separately.
    #[test]
    fn a_fat_operand_defined_in_a_later_listed_block_still_resolves() {
        let fat = Ty::FatPtr(crate::FatPtrKind::Str);
        let mut module = Module::new("borrow-block-order");
        let ft = module.add_func_type(FuncTy {
            params: vec![fat.clone()],
            returns: vec![],
            is_vararg: false,
        });
        // entry is bb0, but bb1 is LISTED first.
        let mut func = Function::new(FuncId::new(0), "late_operand", ft, b(0));
        let mut bb1 = crate::Block::new(b(1));
        bb1.body
            .push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
        func.blocks.push(bb1);
        func.blocks
            .push(crate::Block::new(b(0)).with_param(v(0), fat.clone()));
        module.add_function(func);

        assert_eq!(ty_of(&module, v(1)), Some(fat));
    }

    /// A borrow of a borrow collapses to the CHAIN ROOT. Both results are fat.
    ///
    /// MUTATION — in `borrow_result_types` phase B, consult `known` for the
    /// borrow's direct operand instead of walking `operand_of` first (or,
    /// equivalently, reorder the walk to try `known` before `operand_of`).
    ///
    /// NOT NEUTRALISED — and this is the load-bearing part: `known` is backed
    /// by a snapshot that already holds the PROVISIONAL `Ty::Ptr` phase 1 wrote
    /// for `%1`. So the mutated lookup does not merely miss the fat type, it
    /// finds a WRONG one, and `%2` answers `Ty::Ptr`. Nothing later overwrites
    /// `%2`, because phase 2 is the last write in `typed_values`.
    #[test]
    fn a_borrow_of_a_borrow_collapses_to_the_chain_root() {
        let fat = Ty::FatPtr(crate::FatPtrKind::Str);
        let mut module = Module::new("borrow-chain");
        let ft = module.add_func_type(FuncTy {
            params: vec![fat.clone()],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "reborrow", ft, b(0));
        let mut block = crate::Block::new(b(0)).with_param(v(0), fat.clone());
        block
            .body
            .push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(1) }).with_result(v(2)));
        func.blocks.push(block);
        module.add_function(func);

        assert_eq!(ty_of(&module, v(1)), Some(fat.clone()));
        assert_eq!(ty_of(&module, v(2)), Some(fat));
    }

    /// A malformed borrow CYCLE has no root to type from. The walk is bounded,
    /// so it terminates and answers the conservative thin spelling.
    ///
    /// MUTATION — remove the `steps > bound` break in `borrow_result_types`.
    /// NOT NEUTRALISED: nothing else bounds that loop, and `operand_of` maps
    /// each of these values to the other forever.
    ///
    /// HONEST CAVEAT: under that mutation this test HANGS rather than failing
    /// an assertion — the red signal is a timeout. The assertion below is still
    /// a real one about the VALUE, which is why the test is a normal green
    /// today rather than a timing observation.
    #[test]
    fn a_borrow_cycle_terminates_at_ptr() {
        let mut module = Module::new("borrow-cycle");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "cyclic", ft, b(0));
        let mut block = crate::Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Borrow { ptr: v(2) }).with_result(v(1)));
        block
            .body
            .push(InstrNode::new(Inst::Borrow { ptr: v(1) }).with_result(v(2)));
        func.blocks.push(block);
        module.add_function(func);

        assert_eq!(ty_of(&module, v(1)), Some(Ty::Ptr));
        assert_eq!(ty_of(&module, v(2)), Some(Ty::Ptr));
    }

    /// PER-SITE PLANTED VIOLATION for `vector_select_contract_errors`.
    ///
    /// The VERDICT does not move — neither `Ty::Ptr` nor `Ty::FatPtr` is a
    /// vector, so `validate_select_condition_ty` rejects a borrow condition
    /// either way — but `actual_cond_ty` is a REPORTED diagnostic, and one that
    /// names `ptr` for a value that is fat ships a false statement in an error
    /// message.
    ///
    /// MUTATION — revert that site's result insert to
    /// `value_tys.insert(*value, ty)`, dropping the `resolved` consult.
    /// NOT NEUTRALISED: `node.result_tys(module)` answers `Ty::Ptr` for a
    /// borrow unconditionally (the per-instruction interface cannot see the
    /// operand), so `actual_cond_ty` becomes `Some(Ty::Ptr)` and the equality
    /// below fails. The assertion is on the fat type specifically, not on the
    /// presence of an error, so it cannot be satisfied by the verdict alone.
    #[test]
    fn a_fat_borrow_select_condition_is_reported_at_its_fat_type() {
        let fat = Ty::FatPtr(crate::FatPtrKind::Str);
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let mut module = Module::new("borrow-select-cond");
        let ft = module.add_func_type(FuncTy {
            params: vec![fat.clone(), v4i32.clone(), v4i32.clone()],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "fat_cond", ft, b(0));
        let mut block = crate::Block::new(b(0))
            .with_param(v(0), fat.clone())
            .with_param(v(1), v4i32.clone())
            .with_param(v(2), v4i32.clone());
        // The borrow precedes the select, so the walk has already recorded it.
        block
            .body
            .push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(3)));
        block.body.push(
            InstrNode::new(Inst::Select {
                ty: v4i32,
                cond: v(3),
                then_val: v(1),
                else_val: v(2),
            })
            .with_result(v(4)),
        );
        func.blocks.push(block);
        module.add_function(func);

        let errors = module
            .validate_vector_select_contracts()
            .expect_err("a borrow is never a legal vector select condition");
        let reported = errors
            .iter()
            .find(|error| error.cond == v(3))
            .expect("the fat borrow condition is reported");
        assert_eq!(reported.actual_cond_ty, Some(fat));
    }

    /// The ratified v2 verdicts on every construct where this classifier
    /// historically drifted from `lowering-target-subset.md`. The machine
    /// cross-check against `trust_ir_conformance::subset` lives in that
    /// crate's `bridge_subset_agreement` gate; these are the core-crate
    /// statements of the same verdicts.
    #[test]
    fn ratified_v2_boundary_verdicts() {
        // Scalar-to-scalar Transmute is IN (Lean semCast scalar partial).
        assert!(
            ConformanceSubset::inst_excluded(&Inst::Cast {
                op: CastOp::Transmute,
                src_ty: Ty::I32,
                dst_ty: Ty::U32,
                operand: v(0),
            })
            .is_none()
        );
        // Aggregate transmutes stay OUT, named as the structural condition.
        assert!(
            ConformanceSubset::inst_excluded(&Inst::Cast {
                op: CastOp::Transmute,
                src_ty: Ty::Tuple(vec![Ty::I32, Ty::I32]),
                dst_ty: Ty::I64,
                operand: v(0),
            })
            .is_some_and(|reason| reason.contains("scalar-to-scalar"))
        );
        // PtrToPtr is IN (full semCast semantics; interpret.rs executes it).
        assert!(
            ConformanceSubset::inst_excluded(&Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Ptr,
                operand: v(0),
            })
            .is_none()
        );
        // The unwinding/coroutine partials are OUT (the pre-unification
        // fallthrough silently admitted all three).
        assert!(ConformanceSubset::inst_excluded(&Inst::Resume { exn: v(0) }).is_some());
        assert!(
            ConformanceSubset::inst_excluded(&Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![],
            })
            .is_some()
        );
        assert!(
            ConformanceSubset::inst_excluded(&Inst::CoroSuspend {
                frame: v(0),
                state_slot: 0,
                next_state: 1,
                value: v(0),
            })
            .is_some()
        );
        // A ratified fast-4 vector op is IN; any other dialect op is OUT.
        let allowed = crate::DialectInst::new("vector", "reduce").with_result_ty(Ty::I32);
        assert!(ConformanceSubset::inst_excluded(&Inst::DialectOp(Box::new(allowed))).is_none());
        let refused = crate::DialectInst::new("clean", "rc_inc");
        assert!(ConformanceSubset::inst_excluded(&Inst::DialectOp(Box::new(refused))).is_some());
        // Refine is fail-closed until a version bump ratifies it.
        assert!(
            ConformanceSubset::ty_excluded(
                &Ty::Refine(crate::TyId::new(0), crate::PredId::new(0),)
            )
            .is_some()
        );
        // Custom proof annotations are refused, located at their site.
        let mut module = Module::new("custom-proof");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "tagged", ft, b(0));
        let mut block = crate::Block::new(b(0));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(0))
            .with_proof(ProofAnnotation::Custom(crate::ProofTag::new(0))),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);
        let violations = module
            .check_conformance_subset()
            .expect_err("Custom proof tags are outside the pinned vocabulary");
        assert!(violations.iter().any(|violation| matches!(
            violation.site,
            SubsetSite::InstructionProof { proof_index: 0 }
        )));
    }
}
