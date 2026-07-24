// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! L5IR - clean Low-Level Intermediate Representation
//!
//! Low-level IR with explicit reference counting and memory layout.
//! Target for backend code generation (C, LLVM, Rust).
//!
//! # Design
//!
//! Based on Lean 4's IR (src/Lean/Compiler/IR/Basic.lean).
//! Key features:
//! - Explicit `inc`/`dec` operations for reference counting
//! - Low-level types (u8, u64, object, etc.)
//! - Mutable field updates for in-place modification
//!
//! # Reference Counting
//!
//! Implements "Counting Immutable Beans" (Ullrich & de Moura, 2020):
//! - Reference counts track shared ownership
//! - `inc x n` increments ref count by n
//! - `dec x` decrements and potentially frees
//! - Optimizations elide unnecessary inc/dec pairs
//!
//! Part of #963 - Compiler IR infrastructure.

use clean_kernel::Name;
use serde::{Deserialize, Serialize};

/// Low-level type in L5IR.
///
/// Unlike kernel `Expr` types, these map directly to runtime representations.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum IRType {
    // Scalar types
    /// Boolean (1 byte).
    Bool,
    /// Unsigned 8-bit integer.
    UInt8,
    /// Unsigned 16-bit integer.
    UInt16,
    /// Unsigned 32-bit integer.
    UInt32,
    /// Unsigned 64-bit integer.
    UInt64,
    /// Pointer-sized unsigned integer.
    USize,
    /// 32-bit floating point.
    Float32,
    /// 64-bit floating point.
    Float64,

    // Reference types
    /// Heap-allocated, reference-counted object.
    Object,
    /// Tagged pointer (small integers, etc.).
    ///
    /// Tagged objects encode small values in the pointer bits,
    /// avoiding heap allocation.
    TObject,

    // Composite types
    /// Struct with fields of given types.
    Struct(Vec<IRType>),
    /// Union (sum type) with variants.
    Union(Vec<IRType>),

    // Special types
    /// Erased type (proof/type eliminated at runtime).
    Erased,
    /// Void (no value, for unit-like returns).
    Void,
}

impl IRType {
    /// Is this a scalar type (stored by value)?
    ///
    /// Scalar types are immediate values that don't require heap allocation
    /// or reference counting.
    #[inline]
    pub fn is_scalar(&self) -> bool {
        matches!(
            self,
            IRType::Bool
                | IRType::UInt8
                | IRType::UInt16
                | IRType::UInt32
                | IRType::UInt64
                | IRType::USize
                | IRType::Float32
                | IRType::Float64
        )
    }

    /// Is this an object type (reference-counted)?
    ///
    /// Object types are heap-allocated and managed by reference counting.
    /// Includes `Struct` and `Union` which are represented as `clean_obj*`
    /// in both C and Rust emitters and require RC operations.
    #[inline]
    pub fn is_object(&self) -> bool {
        matches!(
            self,
            IRType::Object | IRType::TObject | IRType::Struct(_) | IRType::Union(_)
        )
    }

    /// Is this a runtime reference-counted field type?
    ///
    /// Constructor metadata uses this predicate when counting object slots.
    /// It is currently equivalent to `is_object()`, but keeping the name
    /// separate makes that intent explicit at the call site.
    #[inline]
    pub fn is_rc_type(&self) -> bool {
        self.is_object()
    }

    /// Is this the void type?
    #[inline]
    pub fn is_void(&self) -> bool {
        matches!(self, IRType::Void)
    }

    /// Byte size of a scalar type for constructor object layout.
    ///
    /// Returns the number of bytes this scalar occupies in the scalar storage
    /// area of a constructor object. Returns 0 for non-scalar types (objects
    /// are stored in the object pointer array, not scalar storage).
    ///
    /// Matches Lean 4 `IRType.scalar_size` semantics used by `lean_alloc_ctor`.
    /// Part of #1953.
    pub fn scalar_byte_size(&self) -> u32 {
        match self {
            IRType::Bool | IRType::UInt8 => 1,
            IRType::UInt16 => 2,
            IRType::UInt32 | IRType::Float32 => 4,
            IRType::UInt64 | IRType::USize | IRType::Float64 => 8,
            _ => 0,
        }
    }

    /// Get the boxed equivalent of this type.
    ///
    /// Scalars become Object (heap-allocated lean_object*).
    /// Non-scalars remain unchanged.
    pub fn boxed(&self) -> IRType {
        if self.is_scalar() {
            IRType::Object
        } else {
            self.clone()
        }
    }

    /// Does this type lower to a managed pointer (`clean_obj*` in C,
    /// `Ty::Ptr` in trust-ir) in every backend? Unlike [`IRType::is_object`],
    /// this INCLUDES `Erased`, which all emitters represent as a managed
    /// pointer slot (mirrors `emit_trust_ir::lower_ty`).
    #[inline]
    pub(crate) fn lowers_to_ptr(&self) -> bool {
        matches!(
            self,
            IRType::Object
                | IRType::TObject
                | IRType::Struct(_)
                | IRType::Union(_)
                | IRType::Erased
        )
    }

    /// Are two SCALAR types the same after backend lowering — i.e. is a
    /// value of one faithfully usable as the other with NO conversion?
    ///
    /// Mirrors `emit_trust_ir::lower_ty` equality on the scalar fragment:
    /// `UInt64` and `USize` collapse (both `U64`/`uint64_t`-class), while
    /// `Bool` stays distinct from `UInt8` and floats stay distinct from
    /// same-width integers. Returns `false` if either side is non-scalar.
    /// Used by the C2 carrier-projection rules shared between the
    /// `ir_checker` and the C emitter.
    #[inline]
    pub(crate) fn same_lowered_scalar(&self, other: &IRType) -> bool {
        match (self, other) {
            (IRType::UInt64 | IRType::USize, IRType::UInt64 | IRType::USize) => true,
            (a, b) => a.is_scalar() && a == b,
        }
    }
}

/// Check if two IR types are equivalent for boxing purposes.
///
/// Two types are equivalent if:
/// - Both are scalar and the same type, OR
/// - Both are object types (all objects are interchangeable at runtime)
///
/// `Void` and `Erased` are NOT equivalent to object types — `Void` means
/// "no value" and `Erased` is a proof/type erasure marker, neither of which
/// can be passed where `clean_obj*` is expected.
pub fn eqv_types(t1: &IRType, t2: &IRType) -> bool {
    if t1.is_scalar() && t2.is_scalar() {
        t1 == t2
    } else if t1.is_object() && t2.is_object() {
        true
    } else {
        t1 == t2
    }
}

/// Variable identifier in L5IR.
///
/// Variables are numbered locally within each function.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VarId(pub u32);

/// Join point identifier.
///
/// Join points are local jump targets within a function.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct JoinPointId(pub u32);

/// Function identifier.
///
/// References a global function by name.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FnId(pub Name);

/// IR argument (variable or erased).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum IRArg {
    /// Variable reference.
    Var(VarId),
    /// Erased argument (proof term, eliminated).
    Erased,
}

/// Constructor info for L5IR.
///
/// Describes a constructor's runtime representation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CtorInfo {
    /// Constructor name.
    pub name: Name,
    /// Tag value (for multi-constructor inductives).
    pub tag: u32,
    /// Number of scalar fields.
    pub num_scalars: u32,
    /// Number of object fields.
    pub num_objects: u32,
    /// Field types.
    pub field_types: Vec<IRType>,
}

impl CtorInfo {
    /// Total scalar storage size in bytes for this constructor.
    ///
    /// Sum of `scalar_byte_size()` across all scalar fields. Passed to
    /// `clean_alloc_ctor(tag, num_objs, scalar_sz)` so the runtime allocates
    /// enough space for inline scalar data after the object pointer array.
    /// Part of #1953.
    pub fn scalar_size(&self) -> u32 {
        self.field_types.iter().map(|t| t.scalar_byte_size()).sum()
    }
}

/// IR literal value.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum IRLiteral {
    /// Boolean.
    Bool(bool),
    /// Unsigned 8-bit.
    UInt8(u8),
    /// Unsigned 16-bit.
    UInt16(u16),
    /// Unsigned 32-bit.
    UInt32(u32),
    /// Unsigned 64-bit.
    UInt64(u64),
    /// Pointer-sized.
    USize(usize),
    /// A `Nat` literal `>= 2^64` (up to `2^128 - 1`), carried as its exact u128
    /// value. Unlike the scalar arms this is inherently OBJECT-typed: no machine
    /// scalar can hold it, so it lowers directly to a heap Nat cell via
    /// `clean_nat_big` (RUNG B). The emitter fails closed above two limbs, so the
    /// value is always `< 2^128`. Backs `UInt64.size = 2^64` and friends.
    NatBig(u128),
    /// 32-bit float.
    Float32(f32),
    /// 64-bit float.
    Float64(f64),
}

/// IR expression (pure computation).
///
/// Expressions produce values without side effects (except allocation).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum IRExpr {
    /// Construct a value: `ctor info args`.
    Ctor { info: CtorInfo, args: Vec<IRArg> },

    /// Project field: `proj idx arg`.
    ///
    /// `ty` is the type of the projected field, needed by emitters to dispatch
    /// between `clean_ctor_get()` (object fields) and typed scalar accessors
    /// like `clean_ctor_get_uint64()`.  Same pattern as `Unbox` (#1925).
    Proj { idx: u32, ty: IRType, arg: IRArg },

    /// Get tag from tagged object.
    Tag(IRArg),

    /// Box scalar to heap object.
    Box { ty: IRType, arg: IRArg },

    /// Unbox heap object to scalar.
    ///
    /// `ty` is the expected scalar type of the unboxed value, needed by
    /// emitters to dispatch between `clean_unbox()` (integers/usize),
    /// `clean_unbox_float()` (Float64), etc.
    Unbox { ty: IRType, arg: IRArg },

    /// Literal value.
    Lit(IRLiteral),

    /// Full function application.
    Apply { fn_id: FnId, args: Vec<IRArg> },

    /// Partial application (creates closure).
    ///
    /// `arity` is the total number of parameters the underlying function accepts,
    /// NOT the number of already-captured arguments (`args.len()`). The runtime
    /// uses `arity - args.len()` to determine how many more arguments are needed.
    PartialApply {
        fn_id: FnId,
        arity: u16,
        args: Vec<IRArg>,
    },

    /// Dynamic closure application (Lean 4 `ap`).
    ///
    /// Applies `args` to a closure/pap object. The runtime checks arity:
    /// - If `num_fixed + args.len() == arity`: invoke the function directly.
    /// - If `num_fixed + args.len() < arity`: create a new closure with more captured args.
    /// - If `num_fixed + args.len() > arity`: invoke, then apply remaining args to the result.
    ClosureApply { closure: IRArg, args: Vec<IRArg> },

    /// Extract USize value at position `sizeof(void*)*idx` from object.
    ///
    /// Lean 4: `uproj (i : Nat) (x : VarId)`.
    /// C emission: `clean_ctor_get_usize(var, idx)`.
    UProj { idx: u32, var: VarId },

    /// Extract scalar value at position `sizeof(void*)*n + offset` from object.
    ///
    /// Lean 4: `sproj (n : Nat) (offset : Nat) (x : VarId)`.
    /// `ty` is the expected scalar type, needed by emitters to select the
    /// correct getter (e.g., `clean_ctor_get_uint8`, `clean_ctor_get_float`).
    SProj {
        n: u32,
        offset: u32,
        var: VarId,
        ty: IRType,
    },

    /// Check if object's reference count > 1.
    ///
    /// Lean 4: `isShared (x : VarId)`.
    /// Returns UInt8: 1 if shared (RC > 1), 0 if exclusive (RC == 1).
    /// C emission: `!clean_is_exclusive(var)`.
    IsShared(VarId),

    /// String literal.
    String(String),

    /// Reset object for reuse (ref count == 1 optimization).
    ///
    /// If the object's ref count is 1, reset it for in-place reuse.
    Reset(VarId),

    /// Reuse reset object.
    ///
    /// Allocates in the slot from a prior Reset if available.
    Reuse {
        var: VarId,
        ctor: CtorInfo,
        args: Vec<IRArg>,
    },
}

/// IR function body (control flow with side effects).
///
/// Bodies are sequences of variable declarations, ref count operations,
/// and control flow, ending in a terminal (return, jump, case).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum IRBody {
    /// Variable declaration: `let x : T := e; rest`.
    VDecl {
        var: VarId,
        ty: IRType,
        value: IRExpr,
        rest: Box<IRBody>,
    },

    /// Join point declaration.
    JDecl {
        jp: JoinPointId,
        params: Vec<(VarId, IRType)>,
        body: Box<IRBody>,
        rest: Box<IRBody>,
    },

    /// Increment reference count: `inc x n; rest`.
    ///
    /// Increments the ref count of `x` by `n`.
    Inc {
        var: VarId,
        n: u32,
        rest: Box<IRBody>,
    },

    /// Decrement reference count: `dec x; rest`.
    ///
    /// Decrements ref count and frees if zero.
    Dec { var: VarId, rest: Box<IRBody> },

    /// Mutable object field set: `x[idx] := y; rest`.
    ///
    /// In-place update of object (pointer) field `idx` in object `var`.
    /// Lean 4: `set (x : VarId) (i : Nat) (y : VarId)`.
    /// Requires `RC(var) == 1`.
    Set {
        var: VarId,
        idx: u32,
        value: VarId,
        rest: Box<IRBody>,
    },

    /// Set constructor tag: `setTag x cidx; rest`.
    ///
    /// Lean 4: `setTag (x : VarId) (cidx : Nat)`.
    /// Mutates the tag of a constructor object in place.
    /// Requires `RC(var) == 1`.
    SetTag {
        var: VarId,
        tag: u32,
        rest: Box<IRBody>,
    },

    /// Store USize value at position `sizeof(void*)*idx` in object.
    ///
    /// Lean 4: `uset (x : VarId) (i : Nat) (y : VarId)`.
    /// `value` must be of type USize.
    /// Requires `RC(var) == 1`.
    USet {
        var: VarId,
        idx: u32,
        value: VarId,
        rest: Box<IRBody>,
    },

    /// Store scalar value at position `sizeof(void*)*n + offset` in object.
    ///
    /// Lean 4: `sset (x : VarId) (i : Nat) (offset : Nat) (y : VarId) (ty : IRType)`.
    /// `ty` must be a non-pointer scalar type (not Object, TObject, Erased, or USize).
    /// Requires `RC(var) == 1`.
    SSet {
        var: VarId,
        n: u32,
        offset: u32,
        value: VarId,
        ty: IRType,
        rest: Box<IRBody>,
    },

    /// Case analysis by tag.
    Case {
        scrutinee: VarId,
        alts: Vec<IRAlt>,
        default: Option<Box<IRBody>>,
    },

    /// Jump to join point.
    Jmp { jp: JoinPointId, args: Vec<IRArg> },

    /// Return value.
    Ret(IRArg),

    /// Unreachable (after absurd or exhaustive case).
    Unreachable,
}

/// IR case alternative.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct IRAlt {
    /// Constructor for this alternative.
    pub ctor: CtorInfo,
    /// Body to execute if tag matches.
    pub body: Box<IRBody>,
}

/// Top-level IR function declaration.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct IRDecl {
    /// Function name.
    pub name: Name,
    /// Parameters (var id, type).
    pub params: Vec<(VarId, IRType)>,
    /// Return type.
    pub return_type: IRType,
    /// Function body.
    pub body: IRBody,
}

#[cfg(test)]
#[path = "ir_tests.rs"]
mod tests;
