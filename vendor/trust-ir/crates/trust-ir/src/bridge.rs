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
//!    same v3 boundary for in-process producers, and the conformance crate's
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

mod observed_borrows;
pub use observed_borrows::{borrow_result_ty_observed, borrow_result_types_observed};

use crate::reach::{Reach, ReachMemo};

use crate::{
    BlockId, CastOp, Constant, FuncId, Function, Inst, InstrNode, Module, ProofAnnotation,
    SourceSpan, Ty, ValueId, inst::SelectConditionTypeError,
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
/// # Excluded constructs (subset v5 — `lowering-target-subset.md` is the authority)
///
/// The boundary is the ratified lowering-target subset v5 (repo-root doc;
/// machine mirror `trust_ir_conformance::subset`, agreement pinned by that
/// crate's `bridge_subset_agreement` gate):
///
/// - **Module target** (v5 structural condition5): target-free/default64,
///   explicit little-endian64, or canonical little-endian wasm32/4-byte
///   pointers. Big-endian, other32-bit ABIs and malformed sizes stay out as
///   whole modules ([`SubsetSite::ModuleTarget`]), including empty bodies.
/// - **Char origin** (v4 structural condition 6): a [`Ty::Char`] value may
///   originate only from a range-validated `Const` or from `Cast ZExt` of a
///   `U8` ([`ConformanceSubset::char_origin_excluded`]). A `Transmute` /
///   `Bitcast` / other cast into `Char`, or a `Load` / `AtomicLoad` /
///   `LoadSlot` at a `Char`-carrying type, is out of subset.
/// - **Types**: [`Ty::F16`] (subset/native admission pending), producer-only
///   [`Ty::Error`], and [`Ty::Refine`] (never ratified into the subset;
///   fail-closed until a version bump admits it). First-class [`Ty::FatPtr`]
///   has been admitted since v2 (on the pinned target, now condition 5); the
///   v25 B1 scalars [`Ty::Isize`] / [`Ty::Usize`] / [`Ty::Char`] since v4.
/// - **Casts**: [`CastOp::ReifyFnPointer`] (fn-item partial) and
///   [`CastOp::FPToSISat`] / [`CastOp::FPToUISat`] (no proven bridge/ay
///   lowering). [`CastOp::Transmute`] is in-subset **integer/pointer
///   scalar-to-scalar only** (`I8`–`I128` / `U8`–`U128` / `Ptr` on BOTH
///   sides — v3 removed `F32` / `F64` / `Bool`, which the executable model
///   mistranslated at the destination; use `Bitcast` for int↔float);
///   [`CastOp::PtrToPtr`] is fully in-subset.
/// - **Instructions**: [`Inst::Dealloc`] (dropped in v2, G18-1: the format
///   states neither the allocation origin nor the layout a release needs;
///   this classifier only caught up in v3 — F-042), [`Inst::Resume`],
///   [`Inst::LandingPad`], [`Inst::CoroSuspend`] — host-unwinding /
///   coroutine depth-ledger partials.
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

/// Structural condition5, expanded in v5: preserve the legacy64-bit
/// little-endian model and select the proved32-bit model for wasm32 only.
/// No word-size inference admits another32-bit scalar ABI. Read raw target
/// fields; `pointer_bits` has a fallback that must not admit malformed sizes.
/// The independent conformance mirror is pinned verdict-identical by tests.
fn module_targets_pinned_byte_model(module: &Module) -> bool {
    module.target_info.as_ref().is_none_or(|target| {
        target.endianness == crate::Endianness::Little
            && (target.pointer_size == PINNED_POINTER_SIZE_BYTES
                || (target.pointer_size == 4 && target.triple.split('-').next() == Some("wasm32")))
    })
}

/// True when a value of `ty` CARRIES a `Char` by value — `Char` itself, a
/// vector of them, or a tuple with one inside.
///
/// Deliberately NOT true through a pointer arm (`Ref` / `RefMut` /
/// `PtrConst` / `PtrMut` / `Rc`): loading a `&char` produces a POINTER, not a
/// `Char`, so subset v4 condition 6 has nothing to say about it and refusing
/// it would over-refuse. This is the INLINE surface only: a named aggregate
/// (`Struct` / `Enum` / `Array` / `Record` / `Sequence` / `Set` / `Closure`)
/// names its members through a module table, which is resolved by
/// [`ty_carries_char_value_in`] — the form the module walk uses.
///
/// Mirrors `trust_ir_conformance::subset::ty_carries_char_value`.
fn ty_carries_char_value(ty: &Ty) -> bool {
    match ty {
        Ty::Char => true,
        Ty::Vector(inner, _) => ty_carries_char_value(inner),
        Ty::Tuple(xs) => xs.iter().any(ty_carries_char_value),
        _ => false,
    }
}

/// True when a value of `ty` CARRIES a `Char` by value, **resolving named
/// aggregates through the module tables** (WS2.17 review).
///
/// [`ty_carries_char_value`] sees the inline type surface only, which lets a
/// producer spell the refused origin one level down — `load { char }` or
/// `load [char; 1]` followed by an `ExtractField` / `ExtractElement` makes a
/// `Char` out of arbitrary memory bytes while every single instruction looks
/// in-subset. Condition 6 is about the ORIGIN of a `Char`, so the walk must
/// follow the member tables the load actually reads.
///
/// Pointer arms still stop the walk (a `&{char}` is a pointer, not a char).
/// An id that resolves to nothing answers **true** (a dangling table
/// reference is a malformed module, and the subset verdict fails closed), and
/// so does a type that reaches a by-value cycle (`struct S { s: S }`, an
/// infinitely large type the validator refuses on its own). There is no
/// depth limit: `reach`'s memo decides each node once per `memo` (its
/// `Reach::CharValue` predicate), on the heap, so a module walk asking it of
/// every load costs O(the module). It replaced a native recursion with a
/// 24-level budget that answered "carries a `Char`" when the budget ran out,
/// refusing every char-free type nested 24 levels deep and walking a shared
/// sub-type once per path.
///
/// Mirrors `trust_ir_conformance::subset::CharCarriers`, which decides the
/// same predicate by another algorithm.
fn ty_carries_char_value_in(module: &Module, memo: &mut ReachMemo, ty: &Ty) -> bool {
    memo.reaches(module, Reach::CharValue, ty)
}

/// Reason string for a `Char` produced by anything but the two admitted
/// origins (subset v4 condition 6).
const CHAR_ORIGIN_VIOLATION: &str = "a `Char` may originate only from a range-validated `Const` or `Cast ZExt` of a `U8` \
     (subset v4 condition 6)";

/// Reason string for a `Char` read out of memory (subset v4 condition 6).
const CHAR_LOAD_VIOLATION: &str = "a `Char` may not be READ FROM MEMORY: its Unicode-scalar-value invariant is not \
     re-established by a load (subset v4 condition 6)";

/// The executable model's pointer width in bytes: eight little-endian bytes
/// per pointer (`TrustIr/State/Memory.lean`), i.e. `DEFAULT_POINTER_BITS / 8`.
const PINNED_POINTER_SIZE_BYTES: u32 = crate::shape::DEFAULT_POINTER_BITS / 8;

/// Reason string for a `CallIndirect` whose callee is a `Ty::Closure` value —
/// closure APPLICATION (subset structural condition 4).
///
/// The format admits the application (G18-2) and the reference interpreter
/// executes it by spreading the captures as leading arguments, but the Lean
/// executable model's `CallIndirect` resolves a function-POINTER value and has
/// no closure-application rule, so the construct is not covered as emitted.
/// Condition 4 has said so since G18-2 (2026-09-01), but neither checker
/// enforced it: the codegen refusal was the construct's only gate, and no
/// subset fixture applied a closure until the v58 `closure_layout` golden did
/// — which the Lean executable differential then refused as a type error.
/// Closure INTRODUCTION and capture PROJECTION are untouched. The mirror
/// (`trust_ir_conformance::subset`) reports this same text.
pub const CLOSURE_APPLICATION_VIOLATION: &str = "CallIndirect over a Ty::Closure callee (closure \
     application) is outside the subset: the Lean executable model's CallIndirect resolves a \
     function-pointer value and has no closure-application rule (subset condition 4)";

/// Reason string for a module that fails [`module_targets_pinned_byte_model`].
const MODULE_TARGET_VIOLATION: &str = "module target is outside the executable model's pinned byte models (subset v5 condition 5: \
     `target_info` absent, or little-endian with pointer_size == 8, or wasm32 with pointer_size == 4)";

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
/// condition 1): `I8`–`I128` / `U8`–`U128` / `Ptr`.
/// Mirrors `trust_ir_conformance::subset::is_transmute_scalar`.
///
/// **v3 narrows this on BOTH sides** (soundness erratum, F-036/F-042 review).
/// v2 also admitted `F32` / `F64` / `Bool`, which the executable model cannot
/// byte-reinterpret: Lean's `semCast .Transmute` only accepts an `.int` /
/// `.ptr` *operand*, so a float or bool SOURCE was already refused, while a
/// float or bool DESTINATION was MISTRANSLATED — it asked only
/// `getTyWidth dstTy`, so `transmute u32 -> f32` bound an *integer* value at
/// a float type and `transmute u8 -> bool` bound `.int 1 v` with `v` possibly
/// greater than 1. The narrowing and the Lean destination gate land together;
/// the sanctioned replacement for an int↔float reinterpret is `Bitcast`,
/// which both engines model through the IEEE bit pattern.
pub(crate) fn transmute_scalar_ty(ty: &Ty) -> bool {
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
            | Ty::Ptr
    )
}

impl ConformanceSubset {
    /// The current pinned subset. Frontends target this version.
    ///
    /// v3 (2026-09-19) is a breaking SHRINK under the bump policy's
    /// "soundness hole" clause: `Transmute` loses its float/bool operands on
    /// both sides, `Inst::Dealloc` is refused here as well as by the
    /// machine-readable mirror (the v2 `Dealloc` drop this classifier never
    /// read), and the whole module must target the pinned 64-bit
    /// little-endian byte model.
    ///
    /// v4 (2026-09-22, WS2.17) is an EXPANSION under the bump policy: the
    /// three v25 B1 scalars `Isize` / `Usize` / `Char` enter the type subset,
    /// and one structural condition is ADDED
    /// ([`ConformanceSubset::char_origin_excluded`], condition 6). Every v3
    /// module is a valid v4 module — condition 6 can only fire on a `Char`,
    /// which no v3 module could carry. `FPToSISat` / `FPToUISat` stay
    /// excluded: their ay bit-blast encoding is still fail-closed, so the
    /// interpreter/solver cross-check their admission is gated on does not
    /// exist yet.
    /// v5 adds the target-indexed wasm32 model. No construct allowlist or
    /// unrelated structural exclusion changes; the default64 path is retained.
    pub const CURRENT: Self = Self { version: 5 };

    /// Reason an instruction violates subset v4 structural **condition 6** —
    /// a `Char` value may originate only from a range-validated `Const` or
    /// from `Cast ZExt` of a `U8` — or `None`.
    ///
    /// `Ty::Char` is a 32-bit carrier whose inhabitants are the Unicode
    /// scalar values (`0..=0x10FFFF` minus the surrogates `0xD800..=0xDFFF`),
    /// so admitting the TYPE is only sound while every way of MAKING one
    /// re-establishes that invariant. `Const` is checked by
    /// `validate_module`; `ZExt` from `U8` holds by construction (every `u8`
    /// is a Unicode scalar value). A `Transmute` / `Bitcast` into `Char`
    /// reinterprets an arbitrary 32-bit pattern, a `Trunc` drops high bits
    /// from one, and a `Load` / `AtomicLoad` / `LoadSlot` reads bytes the
    /// model cannot constrain — all three are refused here. The reference
    /// interpreter independently reports an invalid `Char` as UB at every
    /// bind site, so an out-of-subset module still fails closed.
    ///
    /// Mirrors `trust_ir_conformance::subset::char_origin_violation`; the
    /// conformance crate's `bridge_subset_agreement` gate pins the two
    /// verdict-identical.
    pub fn char_origin_excluded(inst: &Inst) -> Option<&'static str> {
        match inst {
            Inst::Cast {
                op, src_ty, dst_ty, ..
            } if ty_carries_char_value(dst_ty) => {
                (!(*op == CastOp::ZExt && *src_ty == Ty::U8 && *dst_ty == Ty::Char))
                    .then_some(CHAR_ORIGIN_VIOLATION)
            }
            Inst::Load { ty, .. } | Inst::AtomicLoad { ty, .. } | Inst::LoadSlot { ty, .. }
                if ty_carries_char_value(ty) =>
            {
                Some(CHAR_LOAD_VIOLATION)
            }
            _ => None,
        }
    }

    /// Condition 6 with the module's member tables RESOLVED — the form the
    /// module walk ([`ConformanceSubset::check`]) uses (WS2.17 review).
    ///
    /// [`ConformanceSubset::char_origin_excluded`] classifies one instruction
    /// from its inline types alone, which is all a caller without a module
    /// can do. That is not enough for the memory arm: `load { char }` or
    /// `load [char; 1]` reads a `Char` out of arbitrary bytes, and a
    /// following `ExtractField` / `ExtractElement` hands it to the rest of
    /// the program — with every single instruction looking in-subset, because
    /// the member type lives in a module table the inline surface never
    /// names. Resolving the tables closes that spelling. The cast arm needs
    /// no resolution: a cast's `dst_ty` is inline by construction.
    ///
    /// This one-shot form decides what the instruction's type reaches (plus
    /// one pass over each definition table it meets); the module walk
    /// ([`ConformanceSubset::check`]) asks one memo for every instruction,
    /// so a whole module costs O(its types) however many loads share them.
    ///
    /// Mirrors `trust_ir_conformance::subset::char_origin_violation_in`.
    pub fn char_origin_excluded_in(module: &Module, inst: &Inst) -> Option<&'static str> {
        Self::char_origin_excluded_with(module, &mut ReachMemo::default(), inst)
    }

    /// [`ConformanceSubset::char_origin_excluded_in`] over `memo`, a
    /// reachability memo for `module` that a pass shares.
    fn char_origin_excluded_with(
        module: &Module,
        memo: &mut ReachMemo,
        inst: &Inst,
    ) -> Option<&'static str> {
        if let Some(reason) = Self::char_origin_excluded(inst) {
            return Some(reason);
        }
        match inst {
            Inst::Load { ty, .. } | Inst::AtomicLoad { ty, .. } | Inst::LoadSlot { ty, .. }
                if ty_carries_char_value_in(module, memo, ty) =>
            {
                Some(CHAR_LOAD_VIOLATION)
            }
            _ => None,
        }
    }

    /// Reason a construct is outside the conformance subset.
    ///
    /// Returns the human-readable exclusion reason for a [`Ty`], or `None` if the
    /// type (recursing into element/aggregate types) is fully in-subset.
    pub fn ty_excluded(ty: &Ty) -> Option<&'static str> {
        match ty {
            Ty::Storage(_) => Some("storage-only type has no by-value Core lowering"),
            Ty::F16 => Some("Ty::F16 awaits versioned subset admission and native lowering"),
            Ty::Error => Some("Ty::Error is producer-internal and never wire-legal"),
            Ty::Dialect(_) => {
                Some("dialect types require explicit semantic legalization before Core lowering")
            }
            // v43: one pointer word at the machine level, but its meaning lives
            // in a linked runtime the reference interpreter cannot execute
            // in-format (only HOST-ASSISTED, through a trusted `HostCalls`
            // model — WS2.12 — which is no origin for proof purposes) and the
            // Lean model does not define, so no module carrying one is in the
            // proven subset.
            Ty::Handle(_) => Some(
                "handle types are runtime-opaque: no interpreter or Lean origin; outside the proven \
                 subset",
            ),
            Ty::FatPtr(_) => None,
            // PKG-U13a: a tensor has no memory layout and no machine lowering,
            // and the W5b Lean model defines no tensor (SemR judges the
            // tensor region), so no module carrying one is in the subset,
            // whatever its element.
            Ty::Tensor(..) => Some(
                "Ty::Tensor has no memory layout or machine lowering yet (PKG-U13: outside the \
                 lowering-target subset)",
            ),
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
            // v4 (WS2.17): the v25 B1 scalars. `Isize`/`Usize` execute at the
            // Lean model's 64-bit pin, which v3's structural condition 5
            // already pins the whole module to; `Char` is admitted together
            // with structural condition 6
            // ([`ConformanceSubset::char_origin_excluded`]), which is what
            // keeps its Unicode-scalar-value invariant true at every origin.
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
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
            Ty::Refine(_, _) => Some(
                "Ty::Refine is not ratified into the lowering-target subset (fail-closed; never admitted, v2 or v3)",
            ),
            Ty::Ext(e) => e.unreachable(),
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
    /// Inspects its opcode and inline types at the legacy default64 width.
    /// Module checks select the actual module width before checking metadata.
    pub fn inst_excluded(inst: &Inst) -> Option<&'static str> {
        Self::inst_excluded_at(inst, crate::shape::DEFAULT_POINTER_BITS)
    }

    fn inst_excluded_at(inst: &Inst, pointer_bits: u32) -> Option<&'static str> {
        // Subset v4 structural condition 6 runs FIRST: a `Char` origin that
        // does not re-establish the Unicode-scalar-value invariant is out of
        // subset for that reason, not for its operand types (which are all
        // in-subset since v4 admitted `Char`).
        if let Some(reason) = Self::char_origin_excluded(inst) {
            return Some(reason);
        }
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
                        .pointer_metadata_ty(pointer_bits)
                        .as_ref()
                        != Some(metadata_ty))
                    .then_some(
                        "pointer-trio metadata type does not match the canonical target-width lane",
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
            // Dropped from the subset in v2 (G18-1, `lowering-target-subset.md`
            // §"Deallocation"): the instruction names ONE field, `ptr`, so it
            // states neither the `AllocOrigin` nor the layout a correct release
            // needs, and trust-cg fails closed on it. The machine-readable
            // mirror dropped it then; this classifier did not, which made the
            // "verdict-identical" claim false (F-042). Aligned in v3.
            Inst::Dealloc { .. } => Some(
                "Inst::Dealloc: dropped from the subset in v2 (G18-1) — the format states neither the AllocOrigin nor the layout a release needs",
            ),
            // The resume state-machine theorem LANDED (WS2.25,
            // `CoroGen.coro_two_state_roundtrip` in the Lean package); the
            // instruction stays excluded until a subset version bump admits
            // it with the WS2.1 validator arm as its precondition.
            Inst::CoroSuspend { .. } => Some(
                "Inst::CoroSuspend: proved (WS2.25 resume state-machine theorem) but not yet admitted — awaits a subset version bump (B3 depth ledger)",
            ),
            // WS3.20 (F-057): the bulk-memory pair has Lean semantics
            // (`semMemCopy` / `semMemSet`, Semantics/Memory.lean) and executes
            // in the reference interpreter, but ADMITTING a new opcode is a
            // subset-contract expansion (`lowering-target-subset.md`,
            // "Versioning and bump policy": allowlist + doc + SUBSET_VERSION in
            // lockstep, consumer lowering in trust-cg). Until that bump lands
            // they are outside the subset — fail closed, never silently in.
            Inst::MemCopy { .. } => Some(
                "Inst::MemCopy: not yet admitted to the lowering-target subset (WS3.20 landed the semantics; admission is a subset-contract bump with the consumer)",
            ),
            Inst::MemSet { .. } => Some(
                "Inst::MemSet: not yet admitted to the lowering-target subset (WS3.20 landed the semantics; admission is a subset-contract bump with the consumer)",
            ),
            // Amendment D (wire v55, `docs/SPEC_RATIFICATIONS.md` §20): a drop
            // RESOLVES through the module drop-glue table and executes in both
            // models as a call of its glue (Lean: `stepNWithContext_resolveDrops`);
            // an unresolved one is refused by both. No backend lowers a drop
            // yet, so both spellings of the subset exclude it by name until the
            // v5 expansion (the inline-type fallthrough below would otherwise
            // admit it).
            Inst::Drop { .. } => Some(
                "Inst::Drop: executes in both models as a call of its drop_glue row (§20, stepNWithContext_resolveDrops); awaiting a backend lowering",
            ),
            // Its unwinding twin, the same (and, like `Invoke`, its unwind edge
            // is unlowered).
            Inst::DropInvoke { .. } => Some(
                "Inst::DropInvoke: executes in both models as an invoke of its drop_glue row (§20, stepNWithContext_resolveDrops); awaiting a backend lowering",
            ),
            // Amendment D, Part 2 (wire v56, §21): `CallIndirect`'s unwinding
            // twin. Both models execute it (its unwind edge under
            // `PanicStrategy::Unwind` only); no backend lowers it, and, like
            // `Invoke`, it is gated by `LandingPad`'s exclusion. Excluded by
            // name until the v5 expansion.
            Inst::InvokeIndirect { .. } => Some(
                "Inst::InvokeIndirect: executes in both models (§21; its unwind edge under PanicStrategy::Unwind); awaiting a backend lowering",
            ),
            // Crystal lane (D3): the WEAK form of an allowlisted variant. A weak
            // compare-exchange may fail spuriously, a nondeterministic choice
            // neither executable model makes, so both refuse it; a strong
            // `CmpXchg` falls through to the inline-type check as before.
            Inst::CmpXchg { weak: true, .. } => Some(
                "Inst::CmpXchg weak: spurious failure is nondeterministic; both executable models refuse it",
            ),
            // Crystal lane (E3b): a `Const` carrying an UNWRITTEN lane. Both
            // executable models define it, but no backend lowers it (the Trust
            // callee sidecar emits it for execution only). Both spellings of
            // the subset exclude it (structural condition 8).
            Inst::Const { value, .. }
                if value
                    .try_visit_constants(|c| {
                        if matches!(c, crate::Constant::Uninit) {
                            core::ops::ControlFlow::Break(())
                        } else {
                            core::ops::ControlFlow::Continue(())
                        }
                    })
                    .is_break() =>
            {
                Some(
                    "Inst::Const carrying an unwritten lane (uninit): executable in both models, lowered by no backend",
                )
            }
            // Amendment D, Part 2 (§21): both models execute a pad and
            // `Resume` under `PanicStrategy::Unwind` (selector 1 catch-all, 0
            // cleanup, typed catch refused); no consumer lowers a
            // panic=unwind build yet, so both stay excluded by name.
            Inst::LandingPad { .. } => Some(
                "Inst::LandingPad: modelled under PanicStrategy::Unwind (§21: selector 1 catch-all, 0 cleanup, typed catch refused); awaiting admission with a panic=unwind lowering",
            ),
            Inst::Resume { .. } => Some(
                "Inst::Resume: modelled under PanicStrategy::Unwind (§21: re-raises the exception at its operand's address); awaiting admission with a panic=unwind lowering",
            ),
            // Amendment P (wire v54): the sited check with an unwind edge
            // landed with its wire tag and the semantics of both engines, but
            // no consumer lowers it (trust-cg compiles only panic=abort and has
            // no EH lowering for it), and "admitting an opcode no consumer
            // lowers is not admission". Outside the subset BY NAME until a
            // subset bump admits it with the lowering. A plain sited `Assert`
            // is inside, whatever its kind and site.
            Inst::AssertInvoke { .. } => Some(
                "Inst::AssertInvoke: not yet admitted to the lowering-target subset (amendment P landed the wire tag and both engines' semantics; no consumer lowers its unwind edge yet; admission is a subset-contract bump with the lowering)",
            ),
            // WS3.5: the register-level aggregate seed landed after subset v3
            // was cut, without its wire tag (since landed: Inst tag 60, the
            // v51 INST wire batch) and without a backend lowering (trust-cg
            // refuses it until WS7). Its Lean semantics are an honest partial
            // too: enum and record construction fail closed
            // (`unsupported.enum_def_table`), since the Lean machine state
            // carries no definition tables. Admission is a later subset bump
            // once the lowering and the Lean depth land; until then it is
            // outside, whatever its lane types are.
            Inst::MakeAggregate { .. } => Some(
                "Inst::MakeAggregate: no backend lowering, and enum/record construction is an honest Lean partial (B3 depth ledger); admission is a subset-contract bump (the v51 INST wire batch landed its wire tag)",
            ),
            Inst::MakeClosure { .. } => Some(
                "Inst::MakeClosure: runtime closure construction awaits native lowering and operational Lean closure semantics before subset admission",
            ),
            // v50: the constant-size uniform array landed with its wire tag,
            // Lean semantics (`semArraySplat`, `List.replicate`) and a lazy
            // reference-interpreter value, but NOT with a backend lowering, and
            // admitting a new opcode is a subset-contract expansion
            // (`lowering-target-subset.md`, "Versioning and bump policy"). So
            // it is outside the subset — explicitly, never by default — until
            // that bump lands with the trust-cg lowering.
            Inst::ArraySplat { .. } => Some(
                "Inst::ArraySplat: not yet admitted to the lowering-target subset (v50 landed the wire tag, Lean and interpreter semantics; admission is a subset-contract bump with the trust-cg lowering)",
            ),
            // PKG-U13a: the tensor contraction executes in the reference
            // interpreter and SemR, but the subset has no tensor type
            // (`ty_excluded`) and no backend lowers one. Excluded by name, so
            // the verdict never rests on the inline-type fallthrough below.
            Inst::TensorContract { .. } => Some(
                "Inst::TensorContract: a tensor contraction has no machine lowering yet (PKG-U13: outside the lowering-target subset)",
            ),
            // PKG-U13c: the map, the reduction and the view likewise, each by
            // name.
            Inst::TensorMap { .. } => Some(
                "Inst::TensorMap: a tensor map has no machine lowering yet (PKG-U13: outside the lowering-target subset)",
            ),
            Inst::TensorReduce { .. } => Some(
                "Inst::TensorReduce: a tensor reduction has no machine lowering yet (PKG-U13: outside the lowering-target subset)",
            ),
            Inst::TensorView { .. } => Some(
                "Inst::TensorView: a tensor view has no machine lowering yet (PKG-U13: outside the lowering-target subset)",
            ),
            // PKG-U13d: the gather and the scatter likewise, each by name.
            Inst::TensorGather { .. } => Some(
                "Inst::TensorGather: a tensor gather has no machine lowering yet (PKG-U13: outside the lowering-target subset)",
            ),
            Inst::TensorScatter { .. } => Some(
                "Inst::TensorScatter: a tensor scatter has no machine lowering yet (PKG-U13: outside the lowering-target subset)",
            ),
            // The constant twin, wherever a constant is emitted: a
            // `Constant::Splat` at any depth of an `Inst::Const` value is
            // outside the subset for the same reason. The walk visits each
            // written node once (a splat's element is one child), so it is
            // proportional to the constant's text.
            Inst::Const { ty, value } => constant_splat_excluded(value).or_else(|| Self::ty_excluded(ty)),
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
            | Inst::MakeAggregate { ty, .. }
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
                "ProofAnnotation::FreshSymbolicHavoc is not ratified into the lowering-target subset (fail-closed; never admitted, v2 or v3)",
            ),
            ProofAnnotation::RegionHavocStore => Some(
                "ProofAnnotation::RegionHavocStore is not ratified into the lowering-target subset (fail-closed; never admitted, v2 or v3)",
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
        // Condition 6's `Char`-by-value verdicts, decided once per type node
        // for the whole module.
        let mut char_memo = ReachMemo::default();
        // Condition 5 is a WHOLE-MODULE property, so it is reported once, with
        // no function/block site, and it holds even for a module with no
        // functions at all (its type table and globals are still emitted
        // against a byte model the proven semantics do not describe).
        if !module_targets_pinned_byte_model(module) {
            violations.push(SubsetViolation {
                function: None,
                block: None,
                instruction_index: None,
                site: SubsetSite::ModuleTarget,
                reason: MODULE_TARGET_VIOLATION,
            });
        }
        for function in &module.functions {
            // Condition 4 needs the callee's TYPE, which only the function's
            // value typing gives; computed once, and only for a function that
            // has an indirect call at all.
            let mut value_types: Option<BTreeMap<ValueId, Ty>> = None;
            for (proof_index, proof) in function.proofs.iter().enumerate() {
                if let Some(reason) = Self::proof_annotation_excluded(proof) {
                    violations.push(SubsetViolation {
                        function: Some(function.id),
                        block: Some(function.entry),
                        instruction_index: None,
                        site: SubsetSite::FunctionProof { proof_index },
                        reason,
                    });
                }
            }
            for block in &function.blocks {
                for (param_index, (_value, ty)) in block.params.iter().enumerate() {
                    if let Some(reason) = Self::ty_excluded(ty) {
                        violations.push(SubsetViolation {
                            function: Some(function.id),
                            block: Some(block.id),
                            instruction_index: None,
                            site: SubsetSite::BlockParamType { param_index },
                            reason,
                        });
                    }
                }
                for (instruction_index, node) in block.body.iter().enumerate() {
                    // Condition 6 runs against the RESOLVED member tables
                    // here (WS2.17 review): `inst_excluded` alone sees the
                    // inline type surface, which `load { char }` escapes.
                    if let Some(reason) =
                        Self::char_origin_excluded_with(module, &mut char_memo, &node.inst)
                            .or_else(|| Self::inst_excluded_at(&node.inst, module.pointer_bits()))
                    {
                        violations.push(SubsetViolation {
                            function: Some(function.id),
                            block: Some(block.id),
                            instruction_index: Some(instruction_index),
                            site: SubsetSite::Instruction,
                            reason,
                        });
                    }
                    // Condition 4: closure APPLICATION is outside the subset.
                    if let Inst::CallIndirect { callee, .. } = &node.inst {
                        let types = value_types.get_or_insert_with(|| {
                            function
                                .typed_values(module)
                                .into_iter()
                                .map(|entry| (entry.value, entry.ty))
                                .collect()
                        });
                        if matches!(types.get(callee), Some(Ty::Closure(_))) {
                            violations.push(SubsetViolation {
                                function: Some(function.id),
                                block: Some(block.id),
                                instruction_index: Some(instruction_index),
                                site: SubsetSite::Instruction,
                                reason: CLOSURE_APPLICATION_VIOLATION,
                            });
                        }
                    }
                    for (proof_index, proof) in node.proofs.iter().enumerate() {
                        if let Some(reason) = Self::proof_annotation_excluded(proof) {
                            violations.push(SubsetViolation {
                                function: Some(function.id),
                                block: Some(block.id),
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

/// Where a conformance-subset violation was found.
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
    /// The MODULE, not a construct inside it, is out of subset: subset v3
    /// structural condition5 (the selected64-bit or wasm32 little-endian byte model).
    /// `function` and `block` are `None` — the violation has no site.
    ModuleTarget,
}

/// A single out-of-subset construct, located precisely for diagnostics.
///
/// `function` / `block` are `None` exactly for [`SubsetSite::ModuleTarget`],
/// which is a property of the whole module and names no construct.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SubsetViolation {
    pub function: Option<FuncId>,
    pub block: Option<BlockId>,
    /// Instruction index within the block when `site` is an instruction.
    pub instruction_index: Option<usize>,
    pub site: SubsetSite,
    /// Static, human-readable reason the construct is excluded.
    pub reason: &'static str,
}

impl core::fmt::Display for SubsetViolation {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        // The sited variants print the bare id (`FuncId(0)`, `BlockId(0)`),
        // never the `Option` wrapper: `function` / `block` are `None` only
        // for `ModuleTarget`, which has its own arm.
        let function = self
            .function
            .map_or_else(|| "?".to_string(), |id| format!("{id:?}"));
        let block = self
            .block
            .map_or_else(|| "?".to_string(), |id| format!("{id:?}"));
        match self.site {
            SubsetSite::ModuleTarget => {
                write!(f, "conformance-subset violation in module: {}", self.reason)
            }
            SubsetSite::BlockParamType { param_index } => write!(
                f,
                "conformance-subset violation in function {function}, block {block}, block-param {param_index}: {}",
                self.reason
            ),
            SubsetSite::Instruction => write!(
                f,
                "conformance-subset violation in function {function}, block {block}, instruction {}: {}",
                self.instruction_index
                    .map_or_else(|| "?".to_string(), |i| i.to_string()),
                self.reason
            ),
            SubsetSite::InstructionProof { proof_index } => write!(
                f,
                "conformance-subset violation in function {function}, block {block}, instruction {}, proof {proof_index}: {}",
                self.instruction_index
                    .map_or_else(|| "?".to_string(), |i| i.to_string()),
                self.reason
            ),
            SubsetSite::FunctionProof { proof_index } => write!(
                f,
                "conformance-subset violation in function {function}, function-level proof {proof_index}: {}",
                self.reason
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
/// A malformed borrow cycle (`%1 = Borrow %1`) has no root. Visiting marks
/// detect cycles, and memoized terminal root identities collapse shared paths.
/// Each distinct borrow edge is expanded once; cycles and their incoming
/// prefixes answer `Ty::Ptr`. The cycle itself is a dominance/SSA defect that
/// the passes owning that question report. Callback answers are not cached.
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

    // Cache root identities, not the callback's answers. Each borrow edge is
    // expanded once, while `known` still runs once per acyclic result in the
    // original sorted order (including repeated roots and missing types).
    let mut roots = BorrowRoots::default();
    let mut resolved = Vec::with_capacity(operand_of.len());
    for result in operand_of.keys() {
        let root = roots.resolve(*result, &operand_of);
        let operand_ty = root.and_then(known);
        resolved.push((*result, borrow_result_ty(operand_ty.as_ref())));
    }
    resolved
}

#[derive(Clone, Copy)]
enum BorrowRoot {
    Visiting,
    Resolved(Option<ValueId>),
}

#[derive(Default)]
struct BorrowRoots {
    memo: BTreeMap<ValueId, BorrowRoot>,
    path: Vec<ValueId>,
    #[cfg(test)]
    expanded: usize,
}

impl BorrowRoots {
    fn resolve(
        &mut self,
        result: ValueId,
        operands: &BTreeMap<ValueId, ValueId>,
    ) -> Option<ValueId> {
        self.path.clear();
        let mut cursor = result;
        let root = loop {
            match self.memo.get(&cursor) {
                Some(BorrowRoot::Resolved(root)) => break *root,
                Some(BorrowRoot::Visiting) => break None,
                None => {}
            }
            match operands.get(&cursor) {
                None => break Some(cursor),
                Some(operand) => {
                    self.memo.insert(cursor, BorrowRoot::Visiting);
                    self.path.push(cursor);
                    #[cfg(test)]
                    {
                        self.expanded += 1;
                    }
                    cursor = *operand;
                }
            }
        };
        for value in self.path.drain(..) {
            self.memo.insert(value, BorrowRoot::Resolved(root));
        }
        root
    }
}

#[cfg(test)]
mod borrow_root_cache_tests;

/// Exclusion reason for a constant that carries a `Constant::Splat` anywhere
/// (v50): outside the lowering-target subset until a subset-contract bump
/// admits the uniform array with a backend lowering. Shared with the
/// conformance mirror (`trust_ir_conformance::subset`), which applies it to
/// global initializers as well. The walk visits each WRITTEN node once — a
/// splat's element is one child — so it costs the constant's text, not its
/// length.
pub fn constant_splat_excluded(constant: &Constant) -> Option<&'static str> {
    constant
        .try_visit_constants(|node| {
            if matches!(node, Constant::Splat { .. }) {
                core::ops::ControlFlow::Break(())
            } else {
                core::ops::ControlFlow::Continue(())
            }
        })
        .is_break()
        .then_some(
            "Constant::Splat: not yet admitted to the lowering-target subset (v50 landed the wire tag, Lean and interpreter semantics; admission is a subset-contract bump with the trust-cg lowering)",
        )
}

fn inst_result_tys(inst: &Inst, module: &Module) -> Vec<Ty> {
    match inst {
        Inst::MakeClosure { ty, .. } => vec![Ty::Closure(*ty)],
        // Trust (wave-DS): a drop RUNS a destructor and yields nothing; so
        // does its unwinding twin (amendment D).
        Inst::Drop { .. } | Inst::DropInvoke { .. } => Vec::new(),
        Inst::BinOp { ty, .. }
        | Inst::UnOp { ty, .. }
        | Inst::Load { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::MakeAggregate { ty, .. }
        | Inst::ArraySplat { ty, .. }
        | Inst::TensorContract { ty, .. }
        | Inst::TensorMap { ty, .. }
        | Inst::TensorReduce { ty, .. }
        | Inst::TensorView { ty, .. }
        | Inst::TensorGather { ty, .. }
        | Inst::TensorScatter { ty, .. }
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
        Inst::Call { callee, .. } | Inst::CallCannotUnwind { callee, .. }
        | Inst::Invoke { callee, .. } => module
            .function_by_id(*callee)
            .and_then(|callee| module.func_type(callee.ty))
            .map(|ty| ty.returns.clone())
            .unwrap_or_default(),
        // `InvokeIndirect` produces its callee's returns on the normal edge,
        // exactly like `CallIndirect` (amendment D, Part 2).
        Inst::CallIndirect { sig, .. }
        | Inst::CallIndirectCannotUnwind { sig, .. }
        | Inst::InvokeIndirect { sig, .. } => module
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
        | Inst::AssertInvoke { .. }
        | Inst::Unreachable
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::Dealloc { .. }
        | Inst::MemCopy { .. }
        | Inst::MemSet { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        // Resume produces no result.
        | Inst::Resume { .. } => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BinOp, FuncTy, ProofAnnotation};

    fn v(index: u32) -> ValueId {
        ValueId::new(index)
    }

    fn b(index: u32) -> BlockId {
        BlockId::new(index)
    }

    #[test]
    fn typed_values_include_params_results_and_producer_metadata() {
        let mut module = Module::new("bridge-metadata");
        let callee_ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::U64, Ty::Bool],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let caller_ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

        let mut callee = Function::new(FuncId::new(0), "callee", callee_ty, b(0));
        callee.blocks.push(crate::Block::new(b(0)));
        module
            .try_add_function(callee)
            .expect("Module::try_add_function: test fixture");

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
        module
            .try_add_function(caller)
            .expect("Module::try_add_function: test fixture");

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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![v4i32.clone(), v4i32.clone(), v4i32.clone()],
                returns: vec![v4i32.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        module
            .validate_vector_select_contracts()
            .expect("compare result is <4 x bool>");
    }

    #[test]
    fn vector_select_contract_rejects_physical_i32_mask_condition() {
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let mut module = Module::new("vector-select-invalid");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![v4i32.clone(), v4i32.clone(), v4i32.clone()],
                returns: vec![v4i32.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        let inc_ty = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let main_ty = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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
        module
            .try_add_function(inc)
            .expect("Module::try_add_function: test fixture");

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
        module
            .try_add_function(main)
            .expect("Module::try_add_function: test fixture");

        module
    }

    #[test]
    fn frontend_emission_handshake_worked_example() {
        let module = emit_two_function_module_with_spans();

        // Step 2: the module stays inside the pinned conformance subset.
        module
            .check_conformance_subset()
            .expect("worked-example module is in-subset");
        assert_eq!(ConformanceSubset::CURRENT.version, 5);

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
        let bytes =
            crate::binary::serialize_module(&module).expect("serialize_module: test fixture");
        let back = crate::binary::deserialize_module(&bytes).expect("binary round-trips");
        assert_eq!(back, module);
        // Idempotent re-encode is byte-identical (the wire-format guarantee a
        // downstream consumer pins against).
        assert_eq!(
            crate::binary::serialize_module(&back).expect("serialize_module: test fixture"),
            bytes
        );

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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        // A `Char` read out of memory: v4 admits the TYPE but condition 6
        // refuses this ORIGIN (an in-subset opcode at an in-subset type).
        blk.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::Char,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(3)),
        );
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        // Char load at instruction 1 (v4 condition 6, not a type exclusion).
        assert!(
            violations.iter().any(|x| x.instruction_index == Some(1)
                && x.reason.contains("may not be READ FROM MEMORY"))
        );
        // F16 Load at instruction 2 (inline-type exclusion on an in-subset op).
        assert!(
            violations
                .iter()
                .any(|x| x.instruction_index == Some(2) && x.reason.contains("F16"))
        );

        // Violations are precisely located + Display-able. The sited
        // variants print the BARE ids: `function` / `block` became `Option`s
        // in v3 (for `ModuleTarget`), and the diagnostic must not leak the
        // wrapper (`Some(FuncId(0))`) for a construct that does have a site.
        let any = &violations[0];
        assert_eq!(any.function, Some(FuncId::new(0)));
        let rendered = any.to_string();
        assert!(
            rendered.contains("in function FuncId(0), block BlockId(0)"),
            "{rendered}"
        );
        assert!(!rendered.contains("Some("), "{rendered}");
    }

    /// Subset v4 POSITIVE: the three v25 B1 scalars are in the type subset,
    /// alone and nested, and a `usize` body is subset-clean.
    #[test]
    fn subset_v4_admits_the_b1_scalars() {
        assert!(ConformanceSubset::ty_excluded(&Ty::Isize).is_none());
        assert!(ConformanceSubset::ty_excluded(&Ty::Usize).is_none());
        assert!(ConformanceSubset::ty_excluded(&Ty::Char).is_none());
        assert!(ConformanceSubset::ty_excluded(&Ty::Tuple(vec![Ty::Usize, Ty::Char])).is_none());
        assert!(ConformanceSubset::ty_excluded(&Ty::RefMut(Box::new(Ty::Isize))).is_none());

        // `fn(usize) -> usize { x + 1 }`, the shape every Rust slice index
        // lowers to. No target_info => condition 5's default byte model.
        let mut module = Module::new("usize_add_one");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Usize],
                returns: vec![Ty::Usize],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "usize_add_one", ft, b(0));
        let mut blk = crate::Block::new(b(0)).with_param(v(0), Ty::Usize);
        blk.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Usize,
                value: Constant::Int(1),
            })
            .with_result(v(1)),
        );
        blk.body.push(
            InstrNode::new(Inst::BinOp {
                op: crate::inst::BinOp::Add,
                ty: Ty::Usize,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(blk);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        module
            .check_conformance_subset()
            .expect("a usize body is inside subset v4");
    }

    /// v5 admits the same usize body on canonical wasm32, while an unknown
    ///32-bit scalar ABI remains a whole-module refusal.
    #[test]
    fn subset_v5_usize_on_wasm32_is_admitted_but_i686_stays_refused() {
        let mut module = Module::new("usize_wasm32");
        module.target_info = Some(crate::TargetInfo {
            triple: "wasm32-unknown-unknown".into(),
            pointer_size: 4,
            endianness: crate::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Usize],
                returns: vec![Ty::Usize],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "usize_id", ft, b(0));
        let mut blk = crate::Block::new(b(0)).with_param(v(0), Ty::Usize);
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(blk);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        module
            .check_conformance_subset()
            .expect("v5 selects the proved32-bit model");
        module.target_info.as_mut().expect("target").triple = "i686-unknown-linux-gnu".into();
        let violations = module
            .check_conformance_subset()
            .expect_err("i686 has no admitted scalar ABI");
        assert!(
            violations
                .iter()
                .any(|x| x.site == SubsetSite::ModuleTarget
                    && x.reason.contains("pinned byte model")),
            "{violations:?}"
        );
        // Right reason: the TYPE is not what refused it.
        assert!(
            !violations.iter().any(|x| x.reason.contains("Usize")),
            "`Usize` must be in-subset in v4; only the target refuses this \
             module: {violations:?}"
        );
    }

    /// Subset v4 condition 6, positive + negative twins + the over-refusal
    /// control, on ONE mutation axis: the cast that makes the `Char`.
    #[test]
    fn subset_v4_char_origin_condition() {
        let zext_u8 = |dst: Ty| Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U8,
            dst_ty: dst,
            operand: v(0),
        };
        // POSITIVE: the one admitted computed origin.
        assert!(ConformanceSubset::inst_excluded(&zext_u8(Ty::Char)).is_none());

        // NEGATIVE TWINS, each one mutation from the positive.
        for (what, inst) in [
            (
                "bitcast u32 -> char",
                Inst::Cast {
                    op: CastOp::Bitcast,
                    src_ty: Ty::U32,
                    dst_ty: Ty::Char,
                    operand: v(0),
                },
            ),
            (
                "zext u16 -> char (wider source)",
                Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::U16,
                    dst_ty: Ty::Char,
                    operand: v(0),
                },
            ),
            (
                "trunc u32 -> char",
                Inst::Cast {
                    op: CastOp::Trunc,
                    src_ty: Ty::U32,
                    dst_ty: Ty::Char,
                    operand: v(0),
                },
            ),
        ] {
            let reason = ConformanceSubset::inst_excluded(&inst)
                .unwrap_or_else(|| panic!("{what} must be out of subset"));
            assert!(
                reason.contains("subset v4 condition 6"),
                "{what}: wrong reason `{reason}`"
            );
        }

        // NEGATIVE TWINS on the memory axis.
        for (what, inst) in [
            (
                "load char",
                Inst::Load {
                    ty: Ty::Char,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                },
            ),
            (
                "atomic load char",
                Inst::AtomicLoad {
                    ty: Ty::Char,
                    ptr: v(0),
                    ordering: crate::inst::Ordering::SeqCst,
                },
            ),
            (
                "load <4 x char>",
                Inst::Load {
                    ty: Ty::Vector(Box::new(Ty::Char), 4),
                    ptr: v(0),
                    volatile: false,
                    align: None,
                },
            ),
        ] {
            let reason = ConformanceSubset::inst_excluded(&inst)
                .unwrap_or_else(|| panic!("{what} must be out of subset"));
            assert!(
                reason.contains("may not be READ FROM MEMORY"),
                "{what}: wrong reason `{reason}`"
            );
        }

        // MUTATION CONTROL — condition 6 must not over-refuse. None of these
        // produces a `Char` value, so the rule has nothing to say about them.
        for (what, inst) in [
            (
                "zext char -> u32 (char is the SOURCE)",
                Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::Char,
                    dst_ty: Ty::U32,
                    operand: v(0),
                },
            ),
            (
                "load &char (a POINTER, not a char)",
                Inst::Load {
                    ty: Ty::Ref(Box::new(Ty::Char)),
                    ptr: v(0),
                    volatile: false,
                    align: None,
                },
            ),
            (
                "load u32 (the carrier, spelled honestly)",
                Inst::Load {
                    ty: Ty::U32,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                },
            ),
            (
                "store char (a store produces no value)",
                Inst::Store {
                    ty: Ty::Char,
                    ptr: v(0),
                    value: v(1),
                    volatile: false,
                    align: None,
                },
            ),
        ] {
            assert!(
                ConformanceSubset::inst_excluded(&inst).is_none(),
                "{what} must stay IN subset v4"
            );
        }
    }

    /// WS2.17 REVIEW — subset v4 condition 6 must resolve the module's
    /// MEMBER TABLES, not just the inline type surface.
    ///
    /// `load { char }` / `load [char; 2]` / `load E` reads a `Char` out of
    /// arbitrary memory bytes, and one `ExtractField` / `ExtractElement`
    /// later that `Char` is an ordinary SSA value — while every instruction
    /// on its own names only a `Ty::Struct` / `Ty::Array` / `Ty::Enum`, which
    /// the inline classifier says nothing about. Before this fix the module
    /// below was reported IN SUBSET, so condition 6's rule ("a `Char` may
    /// originate only from …") was one indirection away from vacuous.
    #[test]
    fn subset_v4_char_origin_resolves_named_aggregates() {
        use crate::value::{EnumId, RecordId, StructId};

        /// `fn f(p: ptr) { load <ty> }` — one load, so the only thing that
        /// can be out of subset is that load.
        fn module_loading(name: &str, prepare: impl FnOnce(&mut Module) -> Ty) -> Module {
            let mut module = Module::new(name);
            let ty = prepare(&mut module);
            let ft = module
                .add_func_type(FuncTy {
                    params: vec![Ty::Ptr],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
            let mut blk = crate::Block::new(b(0)).with_param(v(0), Ty::Ptr);
            blk.body.push(
                InstrNode::new(Inst::Load {
                    ty,
                    ptr: v(0),
                    volatile: false,
                    align: None,
                })
                .with_result(v(1)),
            );
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(blk);
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");
            module
        }

        let char_field = |name: &str| crate::FieldDef {
            name: name.into(),
            ty: Ty::Char,
            offset: None,
        };
        let i32_field = |name: &str| crate::FieldDef {
            name: name.into(),
            ty: Ty::I32,
            offset: None,
        };

        // NEGATIVE TWINS: a `Char` reached through each member table.
        let through_struct = module_loading("via_struct", |m| {
            let id = m.add_struct(crate::StructDef {
                id: StructId::new(0),
                name: "S".into(),
                fields: vec![i32_field("n"), char_field("c")],
                size: None,
                align: None,
                repr: Default::default(),
                origin: None,
            });
            Ty::Struct(id)
        });
        let through_array = module_loading("via_array", |m| {
            let elem = m
                .add_type(Ty::Char)
                .expect("Module::add_type: test fixture");
            Ty::Array(elem, 2)
        });
        let through_enum = module_loading("via_enum", |m| {
            let id = m.add_enum(
                crate::EnumDef::new(
                    EnumId::new(0),
                    "E",
                    vec![
                        crate::EnumVariant {
                            name: "N".into(),
                            fields: vec![Ty::I32],
                            field_names: Vec::new(),
                        },
                        crate::EnumVariant {
                            name: "C".into(),
                            fields: vec![Ty::Char],
                            field_names: Vec::new(),
                        },
                    ],
                )
                .with_discriminants(vec![Some(0), Some(1)]),
            );
            Ty::Enum(id)
        });
        let through_record = module_loading("via_record", |m| {
            let id = m.add_record(crate::RecordDef {
                id: RecordId::new(0),
                name: "R".into(),
                fields: vec![char_field("c")],
            });
            Ty::Record(id)
        });
        // Two indirections deep, and behind a Vector lane: the walk must
        // recurse, not peek one level.
        let two_deep = module_loading("via_array_of_struct", |m| {
            let sid = m.add_struct(crate::StructDef {
                id: StructId::new(0),
                name: "S".into(),
                fields: vec![char_field("c")],
                size: None,
                align: None,
                repr: Default::default(),
                origin: None,
            });
            let elem = m
                .add_type(Ty::Struct(sid))
                .expect("Module::add_type: test fixture");
            Ty::Array(elem, 3)
        });

        for (what, module) in [
            ("load { i32, char }", &through_struct),
            ("load [char; 2]", &through_array),
            ("load enum with a char payload", &through_enum),
            ("load record { c: char }", &through_record),
            ("load [{ char }; 3]", &two_deep),
        ] {
            let Err(violations) = module.check_conformance_subset() else {
                panic!("{what} must be OUT of subset v4 (condition 6)");
            };
            assert!(
                violations
                    .iter()
                    .any(|x| x.reason.contains("may not be READ FROM MEMORY")),
                "{what}: wrong reason {violations:?}"
            );
        }

        // OVER-REFUSAL CONTROLS, one mutation from the twins above.
        let no_char = module_loading("no_char", |m| {
            let id = m.add_struct(crate::StructDef {
                id: StructId::new(0),
                name: "S".into(),
                fields: vec![i32_field("n")],
                size: None,
                align: None,
                repr: Default::default(),
                origin: None,
            });
            Ty::Struct(id)
        });
        no_char
            .check_conformance_subset()
            .expect("a struct with no char member stays in subset v4");
        // A POINTER to a char-bearing struct is a pointer, not a char.
        let pointer_to_char_struct = module_loading("ptr_to_struct", |m| {
            let id = m.add_struct(crate::StructDef {
                id: StructId::new(0),
                name: "S".into(),
                fields: vec![char_field("c")],
                size: None,
                align: None,
                repr: Default::default(),
                origin: None,
            });
            Ty::Ref(Box::new(Ty::Struct(id)))
        });
        pointer_to_char_struct
            .check_conformance_subset()
            .expect("loading a &S is loading a POINTER, not a char");
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
        // A tensor is out whatever its element (PKG-U13a), and so is the
        // contraction, by name rather than through its inline type.
        assert!(ConformanceSubset::ty_excluded(&Ty::Tensor(Box::new(Ty::I32), 2)).is_some());
        assert!(
            ConformanceSubset::inst_excluded(&Inst::TensorContract {
                ty: Ty::Tensor(Box::new(Ty::I32), 2),
                lhs: v(0),
                rhs: v(1),
                batch: Vec::new(),
                contract: vec![(1, 0)],
            })
            .is_some_and(|reason| reason.starts_with("Inst::TensorContract"))
        );
        // PKG-U13c: the map, the reduction and the view, each by name.
        let tensor = || Ty::Tensor(Box::new(Ty::I32), 1);
        for (inst, name) in [
            (
                Inst::TensorMap {
                    ty: tensor(),
                    args: vec![v(0)],
                    body: vec![crate::TensorMapNode::UnOp {
                        op: crate::UnOp::Neg,
                        ty: Ty::I32,
                        operand: 0,
                    }],
                },
                "Inst::TensorMap",
            ),
            (
                Inst::TensorReduce {
                    ty: Ty::Tensor(Box::new(Ty::I32), 0),
                    src: v(0),
                    op: crate::TensorReduceOp::Add,
                    axes: vec![0],
                    order: crate::TensorReduceOrder::RowMajor,
                },
                "Inst::TensorReduce",
            ),
            (
                Inst::TensorView {
                    ty: tensor(),
                    src: v(0),
                    params: Vec::new(),
                    exprs: vec![
                        crate::TensorIndexExpr::SrcExtent(0),
                        crate::TensorIndexExpr::Coord(0),
                    ],
                    shape: vec![0],
                    index: vec![1],
                    fill: None,
                },
                "Inst::TensorView",
            ),
            // PKG-U13d: the gather and the scatter, each by name.
            (
                Inst::TensorGather {
                    ty: tensor(),
                    data: v(0),
                    coords: vec![v(1)],
                },
                "Inst::TensorGather",
            ),
            (
                Inst::TensorScatter {
                    ty: tensor(),
                    init: v(0),
                    src: v(1),
                    coords: vec![v(2)],
                },
                "Inst::TensorScatter",
            ),
        ] {
            assert!(
                ConformanceSubset::inst_excluded(&inst)
                    .is_some_and(|reason| reason.starts_with(name)),
                "{name}"
            );
        }
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
    fn legacy_fat_pointer_trio_retains_target_and_metadata_refusals() {
        let fat = Ty::FatPtr(crate::FatPtrKind::Str);
        let wrong_metadata = Inst::PtrMetadata {
            ptr_ty: fat.clone(),
            metadata_ty: Ty::U32,
            ptr: v(0),
        };
        assert!(
            ConformanceSubset::inst_excluded(&wrong_metadata)
                .is_some_and(|reason| reason.contains("canonical target-width")),
            "v2 must reject a non-canonical fat-pointer metadata lane"
        );
        let mut module = Module::new("fatptr-subset-v2");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![fat.clone(), Ty::Ptr, Ty::U64],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");

        module
            .check_conformance_subset()
            .expect("v2 admits first-class fat pointers on the default 64-bit target");

        // v3: the pinned-target requirement is a MODULE-level condition
        // (structural condition 5), reported once at `SubsetSite::ModuleTarget`
        // with no function/block site — the v2 per-construct fat-pointer
        // reason is gone because the module condition subsumes it.
        let is_module_target = |violation: &SubsetViolation| {
            violation.site == SubsetSite::ModuleTarget
                && violation.function.is_none()
                && violation.block.is_none()
                && violation.instruction_index.is_none()
                && violation.reason == MODULE_TARGET_VIOLATION
        };
        module.target_info = Some(crate::TargetInfo {
            triple: "i686-unknown-linux-gnu".into(),
            pointer_size: 4,
            endianness: crate::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        let violations = module
            .check_conformance_subset()
            .expect_err("v3 must fail closed on a non-64-bit module");
        assert_eq!(violations.len(), 3, "{violations:?}");
        assert_eq!(violations.iter().filter(|v| is_module_target(v)).count(), 1);
        assert_eq!(
            violations
                .iter()
                .filter(|v| v.site == SubsetSite::Instruction
                    && v.reason.contains("canonical target-width lane"))
                .count(),
            2,
            "the raw32-bit target also makes both U64 metadata declarations wrong: {violations:?}"
        );

        let target = module.target_info.as_mut().expect("target");
        target.pointer_size = 8;
        target.endianness = crate::Endianness::Big;
        let violations = module
            .check_conformance_subset()
            .expect_err("v3 must fail closed on a big-endian module");
        assert_eq!(violations.len(), 1, "{violations:?}");
        assert!(is_module_target(&violations[0]), "{violations:?}");

        // Mutation control: an explicit x86_64 little-endian pin is the
        // pinned byte model and stays IN, exactly like the target-free module.
        let target = module.target_info.as_mut().expect("target");
        target.triple = "x86_64-unknown-linux-gnu".into();
        target.endianness = crate::Endianness::Little;
        module
            .check_conformance_subset()
            .expect("an explicit 64-bit little-endian pin is the model's byte model");

        // Fail closed on a malformed pointer size: `Module::pointer_bits`
        // would fall back to the 64-bit default on overflow, so condition 5
        // must read the pinned size directly.
        module.target_info.as_mut().expect("target").pointer_size = u32::MAX;
        let violations = module
            .check_conformance_subset()
            .expect_err("a malformed pointer size is not the pinned byte model");
        assert!(is_module_target(&violations[0]), "{violations:?}");
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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![operand_ty.clone()],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "borrows", ft, b(0));
        let mut block = crate::Block::new(b(0)).with_param(v(0), operand_ty);
        block
            .body
            .push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![fat.clone()],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        // entry is bb0, but bb1 is LISTED first.
        let mut func = Function::new(FuncId::new(0), "late_operand", ft, b(0));
        let mut bb1 = crate::Block::new(b(1));
        bb1.body
            .push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
        func.blocks.push(bb1);
        func.blocks
            .push(crate::Block::new(b(0)).with_param(v(0), fat.clone()));
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![fat.clone()],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "reborrow", ft, b(0));
        let mut block = crate::Block::new(b(0)).with_param(v(0), fat.clone());
        block
            .body
            .push(InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(1)));
        block
            .body
            .push(InstrNode::new(Inst::BorrowMut { ptr: v(1) }).with_result(v(2)));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "cyclic", ft, b(0));
        let mut block = crate::Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Borrow { ptr: v(2) }).with_result(v(1)));
        block
            .body
            .push(InstrNode::new(Inst::Borrow { ptr: v(1) }).with_result(v(2)));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![fat.clone(), v4i32.clone(), v4i32.clone()],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let errors = module
            .validate_vector_select_contracts()
            .expect_err("a borrow is never a legal vector select condition");
        let reported = errors
            .iter()
            .find(|error| error.cond == v(3))
            .expect("the fat borrow condition is reported");
        assert_eq!(reported.actual_cond_ty, Some(fat));
    }

    /// The ratified v2/v3 verdicts on every construct where this classifier
    /// historically drifted from `lowering-target-subset.md`. The machine
    /// cross-check against `trust_ir_conformance::subset` lives in that
    /// crate's `bridge_subset_agreement` gate; these are the core-crate
    /// statements of the same verdicts.
    #[test]
    fn ratified_boundary_verdicts() {
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
        // v3 (F-042): `Dealloc` left the subset in v2 (G18-1) but this
        // classifier still admitted it through the inline-type fallthrough.
        assert!(
            ConformanceSubset::inst_excluded(&Inst::Dealloc { ptr: v(0) })
                .is_some_and(|reason| reason.contains("Inst::Dealloc") && reason.contains("G18-1"))
        );
        // v3 (F-036 review): `Transmute` is integer/pointer scalar only on
        // BOTH sides — a float or bool source OR destination is OUT, named
        // as the structural condition. The destination cases are the
        // mistranslation control (Lean bound an int at a float/bool type).
        for (src_ty, dst_ty) in [
            (Ty::F32, Ty::U32),
            (Ty::U32, Ty::F32),
            (Ty::F64, Ty::U64),
            (Ty::U8, Ty::Bool),
            (Ty::Bool, Ty::U8),
        ] {
            assert!(
                ConformanceSubset::inst_excluded(&Inst::Cast {
                    op: CastOp::Transmute,
                    src_ty: src_ty.clone(),
                    dst_ty: dst_ty.clone(),
                    operand: v(0),
                })
                .is_some_and(|reason| reason.contains("scalar-to-scalar")),
                "Transmute {src_ty} -> {dst_ty} must be out of subset v3"
            );
        }
        // Mutation control: the same reinterpretation spelled as `Bitcast`
        // stays IN — it is the sanctioned int<->float carrier.
        assert!(
            ConformanceSubset::inst_excluded(&Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::U32,
                dst_ty: Ty::F32,
                operand: v(0),
            })
            .is_none()
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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        let violations = module
            .check_conformance_subset()
            .expect_err("Custom proof tags are outside the pinned vocabulary");
        assert!(violations.iter().any(|violation| matches!(
            violation.site,
            SubsetSite::InstructionProof { proof_index: 0 }
        )));
    }
}
