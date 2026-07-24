// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compiler error types.

use crate::ffi_verify::FfiMismatch;
use clean_kernel::{FVarId, Name};
use thiserror::Error;

/// Errors that can occur during compilation.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CompilerError {
    /// Unknown constant referenced.
    #[error("unknown constant: {0}")]
    UnknownConstant(Name),

    /// Invalid expression for LCNF conversion.
    #[error("invalid expression for LCNF conversion: {0}")]
    InvalidExpr(String),

    /// Type mismatch during compilation.
    #[error("type mismatch: expected {expected}, found {found}")]
    TypeMismatch { expected: String, found: String },

    /// An extern declaration does not match the known C runtime ABI.
    #[error(transparent)]
    FfiMismatch(#[from] FfiMismatch),

    /// Unsupported expression form.
    #[error("unsupported expression: {0}")]
    Unsupported(String),

    /// Unsupported or non-normalized type reached IR lowering.
    #[error("unsupported IR type expression: {expr}")]
    UnsupportedIrType { expr: String },

    /// LCNF IR lowering referenced a variable that was never bound.
    #[error("unbound to_ir variable: {fvar:?}")]
    UnboundToIrVar { fvar: FVarId },

    /// LCNF IR lowering referenced a join point that was never bound.
    #[error("unbound to_ir join point: {fvar:?}")]
    UnboundToIrJoinPoint { fvar: FVarId },

    /// Literal lowering reached a runtime representation this IR cannot encode.
    #[error("unsupported literal lowering for {kind}")]
    UnsupportedLiteral { kind: &'static str },

    /// A pseudo-op had the wrong shape or an erased operand where a runtime
    /// value was required.
    #[error("malformed pseudo-op {op:?}: {detail}")]
    MalformedPseudoOp { op: Name, detail: &'static str },

    /// Local functions must be lambda-lifted before IR lowering.
    ///
    /// `to_ir` lowering assumes the lambda-lifting pass has already rewritten
    /// every `Code::Fun` into a top-level declaration (plus a closure binding
    /// where the function escapes). The IR model has no `IRBody` variant for an
    /// inline nested function, so this error fails closed rather than risk a
    /// miscompilation. It is unreachable through the public entry points and
    /// `PassManager::default_pipeline`, which all lambda-lift first; it can only
    /// arise from calling `to_ir::lower_code` on un-lifted code directly.
    #[error("unexpected local function in to_ir: {name:?}")]
    UnexpectedLocalFunction { name: Name },

    /// Pattern matching on an erased scrutinee cannot produce executable IR.
    #[error("case scrutinee lowered to erased: {fvar:?}")]
    InvalidErasedCaseScrutinee { fvar: FVarId },

    /// Closure application requires a runtime closure value.
    #[error("closure callee lowered to erased: {fvar:?}")]
    InvalidClosureCallee { fvar: FVarId },

    /// Reuse lowering requires a live reset slot.
    #[error("reuse slot lowered to erased: {slot:?}")]
    InvalidReuseSlot { slot: FVarId },

    /// A constructor allocation would store a boxed (object-typed) value into
    /// a scalar field slot (C4 containment). The value's runtime
    /// representation is a managed pointer — e.g. an un-scalarized
    /// `UInt32.ofBitVec` carrier chain — so a width-typed scalar store
    /// (`clean_ctor_set_uint*`) would reinterpret the pointer as the field
    /// value. No faithful lowering exists until the carrier chain itself is
    /// scalarized (C5 territory), so this fails closed at `to_ir`: the
    /// per-decl compile probe (clean-cli #14 boundary) then demotes the decl
    /// to an extern fallback instead of the mismatch surfacing as a
    /// whole-module trust-ir validation failure.
    #[error(
        "constructor {ctor} scalar field at byte offset {offset} receives an \
         object-typed value ({value_ty}); a scalar store would reinterpret \
         the pointer — no faithful lowering"
    )]
    BoxedValueInScalarField {
        ctor: Name,
        offset: u32,
        value_ty: String,
    },

    /// A constructor application whose argument spine cannot align with the
    /// constructor's declared layout: the kernel spelling passes the
    /// inductive's `num_params` parameters as leading args (value-level ones
    /// like `Fin.mk`'s `n : Nat` included), then exactly one arg per field.
    /// Any other length has no faithful field placement — zipping used to
    /// silently truncate (storing `Fin.mk`'s bound `n` in `val`'s slot), so
    /// this is a hard error in ALL profiles; the per-decl compile probe
    /// demotes the decl to an extern boundary.
    #[error(
        "constructor {ctor} applied to {args} arg(s), but its spine must be \
         exactly {num_params} inductive parameter(s) + {num_fields} field(s); \
         no faithful field placement"
    )]
    CtorSpineMisaligned {
        ctor: Name,
        args: usize,
        num_params: u32,
        num_fields: usize,
    },

    /// A scalar-carrier construction (C5b) whose carrier is a heap OBJECT.
    /// `IRType` cannot distinguish a tagged immediate from a heap ctor
    /// pointer, and no runtime unbox route decodes a heap ctor chain
    /// (`clean_unbox` is a raw tag shift; `clean_unbox_uint32` decodes only
    /// the tagged/boxed-SCALAR convention; `clean_unbox_uint64` dereferences
    /// a heap scalar box) — so an `Unbox` here would reinterpret a pointer
    /// (`BitVec.ofFin`'s ctor) as the scalar. Fail closed; the per-decl
    /// probe demotes the decl to an extern boundary.
    #[error(
        "scalar-carrier constructor {ctor}: carrier is an object-typed value \
         ({carrier_ty}) with no affirmative boxed-scalar evidence; no runtime \
         unbox route decodes a heap constructor, so the construction has no \
         faithful lowering"
    )]
    ScalarCarrierObjectCarrier { ctor: Name, carrier_ty: String },

    /// Projection lowering indexed past the known field layout.
    #[error("projection index {idx} out of bounds for {type_name:?} ({field_count} field(s))")]
    ProjectionIndexOutOfBounds {
        type_name: Name,
        idx: u32,
        field_count: usize,
    },

    /// `_setTag` could not resolve its target constructor tag.
    #[error("unsupported _setTag lowering for constructor {ctor:?}")]
    UnsupportedSetTagLowering { ctor: Name },
}
