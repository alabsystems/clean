// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The data model of Lean 4's compiled IR (λRC), constructor for constructor.
//!
//! Every type here mirrors one in `Lean/Compiler/IR/Basic.lean` (v4.30.0-rc2)
//! and keeps every field Lean keeps — borrow annotations, the `c`/`persistent`
//! flags of `inc`/`dec`, `case`'s type id and scrutinee type, `reuse`'s header
//! flag, the `Option Name` of a `struct` type, a `Nat` literal of any size.
//! Nothing is normalized away, because the next consumer is an interpreter that
//! must run exactly the program Lean compiled.
//!
//! One representation choice differs from Lean's and is lossless: a
//! [`FnBody`] is stored FLATTENED, as Lean's own `FnBody.flatten` presents it —
//! the run of non-terminal instructions as a vector, then the terminal. Lean's
//! `FnBody` is a right-nested chain (`vdecl x ty e b`), so a body with ten
//! thousand statements is ten thousand nested objects; decoding or dropping
//! that as a `Box` chain recurses once per statement. `FnBody.reshape` inverts
//! `flatten`, so no information is lost. Nesting that remains (a join point's
//! body, a `case` alternative) is structural and bounded by the decoder.

use crate::expr::BigNat;
use clean_kernel::Name;

/// A local variable (`Lean.IR.VarId`, printed `x_<idx>`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct VarId(pub(crate) u64);

/// A join point (`Lean.IR.JoinPointId`, printed `block_<idx>`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct JoinPointId(pub(crate) u64);

/// `Lean.IR.IRType`, in constructor order (the order is the runtime tag).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum IrType {
    /// `float` (tag 0).
    Float,
    /// `uint8` (tag 1).
    UInt8,
    /// `uint16` (tag 2).
    UInt16,
    /// `uint32` (tag 3).
    UInt32,
    /// `uint64` (tag 4).
    UInt64,
    /// `usize` (tag 5).
    USize,
    /// `erased` (tag 6): types, propositions and proofs.
    Erased,
    /// `object` (tag 7): a pointer to a heap value.
    Object,
    /// `tobject` (tag 8): an `object` or a tagged scalar.
    TObject,
    /// `float32` (tag 9).
    Float32,
    /// `struct (leanTypeName : Option Name) (types : Array IRType)` (tag 10).
    Struct {
        /// The Lean type the struct represents, when known.
        lean_type_name: Option<Name>,
        /// Field types.
        types: Vec<IrType>,
    },
    /// `union (leanTypeName : Name) (types : Array IRType)` (tag 11).
    Union {
        /// The Lean type the union represents.
        lean_type_name: Name,
        /// Alternative types.
        types: Vec<IrType>,
    },
    /// `tagged` (tag 12): a tagged pointer holding a scalar.
    Tagged,
    /// `void` (tag 13).
    Void,
}

/// `Lean.IR.Arg`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Arg {
    /// `var (id : VarId)`.
    Var(VarId),
    /// `erased` — an erased type/proof argument (printed `◾`).
    Erased,
}

/// `Lean.IR.LitVal`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum LitVal {
    /// `num (v : Nat)` — any size.
    Num(BigNat),
    /// `str (v : String)`.
    Str(String),
}

/// `Lean.IR.CtorInfo`: the runtime layout of a constructor application.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CtorInfo {
    /// The Lean constructor's name (anonymous for `struct`/`union` values).
    pub(crate) name: Name,
    /// Constructor index (the object tag).
    pub(crate) cidx: u64,
    /// Number of `object`/`tobject` fields.
    pub(crate) size: u64,
    /// Number of `usize` fields.
    pub(crate) usize: u64,
    /// Bytes of other scalar fields.
    pub(crate) ssize: u64,
}

/// `Lean.IR.Expr`, the right-hand side of a `vdecl`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Expr {
    /// `ctor (i : CtorInfo) (ys : Array Arg)`.
    Ctor {
        /// Constructor layout.
        info: CtorInfo,
        /// Field arguments.
        args: Vec<Arg>,
    },
    /// `reset (n : Nat) (x : VarId)`.
    Reset {
        /// Number of fields to release.
        n: u64,
        /// The object being reset.
        x: VarId,
    },
    /// `reuse (x : VarId) (i : CtorInfo) (updtHeader : Bool) (ys : Array Arg)`.
    Reuse {
        /// The reset cell.
        x: VarId,
        /// Constructor layout.
        info: CtorInfo,
        /// Whether the object header (tag) must be rewritten.
        update_header: bool,
        /// Field arguments.
        args: Vec<Arg>,
    },
    /// `proj (i : Nat) (x : VarId)`.
    Proj {
        /// Field index.
        i: u64,
        /// The object.
        x: VarId,
    },
    /// `uproj (i : Nat) (x : VarId)`.
    UProj {
        /// Field index.
        i: u64,
        /// The object.
        x: VarId,
    },
    /// `sproj (n : Nat) (offset : Nat) (x : VarId)`.
    SProj {
        /// Number of pointer-sized slots before the scalar area.
        n: u64,
        /// Byte offset into the scalar area.
        offset: u64,
        /// The object.
        x: VarId,
    },
    /// `fap (c : FunId) (ys : Array Arg)` — full application.
    Fap {
        /// Callee.
        f: Name,
        /// Arguments.
        args: Vec<Arg>,
    },
    /// `pap (c : FunId) (ys : Array Arg)` — partial application.
    Pap {
        /// Callee.
        f: Name,
        /// Captured arguments.
        args: Vec<Arg>,
    },
    /// `ap (x : VarId) (ys : Array Arg)` — closure application.
    Ap {
        /// The closure.
        x: VarId,
        /// Arguments.
        args: Vec<Arg>,
    },
    /// `box (ty : IRType) (x : VarId)`.
    Box {
        /// The scalar type being boxed.
        ty: IrType,
        /// The scalar.
        x: VarId,
    },
    /// `unbox (x : VarId)`.
    Unbox {
        /// The boxed value.
        x: VarId,
    },
    /// `lit (v : LitVal)`.
    Lit(LitVal),
    /// `isShared (x : VarId)`.
    IsShared {
        /// The object.
        x: VarId,
    },
}

/// `Lean.IR.Param`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Param {
    /// The parameter variable.
    pub(crate) x: VarId,
    /// Borrowed (`@&`) parameter.
    pub(crate) borrow: bool,
    /// Parameter type.
    pub(crate) ty: IrType,
}

/// A non-terminal `Lean.IR.FnBody` constructor with its continuation removed
/// (the continuation is the next element of [`FnBody::instrs`]).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Instr {
    /// `vdecl (x : VarId) (ty : IRType) (e : Expr)`.
    VDecl {
        /// The bound variable.
        x: VarId,
        /// Its type.
        ty: IrType,
        /// Its value.
        e: Expr,
    },
    /// `jdecl (j : JoinPointId) (xs : Array Param) (v : FnBody)`.
    JDecl {
        /// The join point.
        j: JoinPointId,
        /// Its parameters.
        params: Vec<Param>,
        /// Its body.
        body: FnBody,
    },
    /// `set (x : VarId) (i : Nat) (y : Arg)`.
    Set {
        /// The object.
        x: VarId,
        /// Field index.
        i: u64,
        /// The stored value.
        y: Arg,
    },
    /// `setTag (x : VarId) (cidx : Nat)`.
    SetTag {
        /// The object.
        x: VarId,
        /// New constructor index.
        cidx: u64,
    },
    /// `uset (x : VarId) (i : Nat) (y : VarId)`.
    USet {
        /// The object.
        x: VarId,
        /// Slot index.
        i: u64,
        /// The stored `usize`.
        y: VarId,
    },
    /// `sset (x : VarId) (i : Nat) (offset : Nat) (y : VarId) (ty : IRType)`.
    SSet {
        /// The object.
        x: VarId,
        /// Number of pointer-sized slots before the scalar area.
        i: u64,
        /// Byte offset into the scalar area.
        offset: u64,
        /// The stored scalar.
        y: VarId,
        /// Its type.
        ty: IrType,
    },
    /// `inc (x : VarId) (n : Nat) (c : Bool) (persistent : Bool)`.
    Inc {
        /// The object.
        x: VarId,
        /// Increment.
        n: u64,
        /// `c`: must check whether `x` is a tagged scalar.
        check_ref: bool,
        /// `x` is statically known to be persistent.
        persistent: bool,
    },
    /// `dec (x : VarId) (n : Nat) (c : Bool) (persistent : Bool)`.
    Dec {
        /// The object.
        x: VarId,
        /// Decrement.
        n: u64,
        /// `c`: must check whether `x` is a tagged scalar.
        check_ref: bool,
        /// `x` is statically known to be persistent.
        persistent: bool,
    },
    /// `del (x : VarId)`.
    Del {
        /// The object.
        x: VarId,
    },
}

/// A terminal `Lean.IR.FnBody` constructor.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Terminal {
    /// `case (tid : Name) (x : VarId) (xType : IRType) (cs : Array Alt)`.
    Case {
        /// `cases.typeName` of the impure-phase LCNF `cases` it was lowered
        /// from (`Lean/Compiler/IR/ToIR.lean`): an impure-phase type name,
        /// not necessarily the source inductive.
        tid: Name,
        /// The scrutinee.
        x: VarId,
        /// The scrutinee's type.
        x_type: IrType,
        /// Alternatives, in Lean's order.
        alts: Vec<Alt>,
    },
    /// `ret (x : Arg)`.
    Ret(Arg),
    /// `jmp (j : JoinPointId) (ys : Array Arg)`.
    Jmp {
        /// Target join point.
        j: JoinPointId,
        /// Arguments.
        args: Vec<Arg>,
    },
    /// `unreachable` (printed `⊥`).
    Unreachable,
}

/// `Lean.IR.FnBody` in its flattened form (see the module documentation).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct FnBody {
    /// The non-terminal instructions, in execution order.
    pub(crate) instrs: Vec<Instr>,
    /// The terminal instruction.
    pub(crate) terminal: Terminal,
}

/// `Lean.IR.Alt`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Alt {
    /// `ctor (info : CtorInfo) (b : FnBody)`.
    Ctor {
        /// The constructor this alternative matches.
        info: CtorInfo,
        /// Its body.
        body: FnBody,
    },
    /// `default (b : FnBody)`.
    Default {
        /// Its body.
        body: FnBody,
    },
}

/// `Lean.IR.DeclInfo`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub(crate) struct DeclInfo {
    /// `sorryDep?`: the declaration this one depends on that uses `sorry`.
    pub(crate) sorry_dep: Option<Name>,
}

/// `Lean.ExternEntry` (`Lean/Compiler/ExternAttr.lean`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ExternEntry {
    /// `adhoc (backend : Name)`.
    Adhoc {
        /// Backend name (`all`, `cpp`, …).
        backend: Name,
    },
    /// `inline (backend : Name) (pattern : String)`.
    Inline {
        /// Backend name.
        backend: Name,
        /// Inline C pattern (`#1 + #2`).
        pattern: String,
    },
    /// `standard (backend : Name) (fn : String)`.
    Standard {
        /// Backend name.
        backend: Name,
        /// Native symbol.
        symbol: String,
    },
    /// `opaque` — a call to a Lean function whose IR is not exported.
    Opaque,
}

/// `Lean.ExternAttrData`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub(crate) struct ExternAttrData {
    /// The entries, in Lean's order.
    pub(crate) entries: Vec<ExternEntry>,
}

/// `Lean.IR.Decl`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Decl {
    /// `fdecl (f : FunId) (xs : Array Param) (type : IRType) (body : FnBody) (info : DeclInfo)`.
    FDecl {
        /// Function name.
        f: Name,
        /// Parameters.
        params: Vec<Param>,
        /// Result type.
        ty: IrType,
        /// Body.
        body: FnBody,
        /// Extra information.
        info: DeclInfo,
    },
    /// `extern (f : FunId) (xs : Array Param) (type : IRType) (ext : ExternAttrData)`.
    Extern {
        /// Function name.
        f: Name,
        /// Parameters.
        params: Vec<Param>,
        /// Result type.
        ty: IrType,
        /// How the function is implemented natively.
        ext: ExternAttrData,
    },
}

impl Decl {
    /// The declaration's name (`Decl.name`).
    #[must_use]
    pub(crate) fn name(&self) -> &Name {
        match self {
            Decl::FDecl { f, .. } | Decl::Extern { f, .. } => f,
        }
    }

    /// `true` for `Decl.extern`.
    #[cfg(any(test, feature = "cli"))]
    #[must_use]
    pub(crate) fn is_extern(&self) -> bool {
        matches!(self, Decl::Extern { .. })
    }
}
