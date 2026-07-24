// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! L5CNF - clean Compiler Normal Form
//!
//! A high-level intermediate representation in A-normal form.
//! Based on Lean 4's LCNF (src/Lean/Compiler/LCNF/Basic.lean).
//!
//! # Key properties
//! - A-normal form: all intermediate results are let-bound
//! - Explicit join points for control flow
//! - Preserves type information for optimization
//! - Borrow annotations for ownership analysis
//!
//! # Example
//!
//! The Lean expression:
//! ```text
//! def add (x y : Nat) : Nat := x + y
//! ```
//!
//! Becomes LCNF:
//! ```text
//! def add (x : Nat) (y : Nat) : Nat :=
//!   let _1 := Nat.add x y
//!   return _1
//! ```

use clean_kernel::{BigNat, Expr, FVarId, Level, Literal, Name};
use serde::{Deserialize, Serialize};

/// Function parameter in LCNF.
///
/// Corresponds to `Param` in Lean 4's LCNF.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Param {
    /// Unique identifier for this parameter.
    pub fvar_id: FVarId,
    /// User-visible name.
    pub name: Name,
    /// Parameter type (kernel expression).
    pub ty: Expr,
    /// Whether this parameter is borrowed (vs owned).
    /// Borrowed parameters don't need ref count operations.
    pub borrow: bool,
}

impl Param {
    /// Create a new owned parameter.
    pub fn new(fvar_id: FVarId, name: Name, ty: Expr) -> Self {
        Self {
            fvar_id,
            name,
            ty,
            borrow: false,
        }
    }

    /// Create a new borrowed parameter.
    pub fn new_borrowed(fvar_id: FVarId, name: Name, ty: Expr) -> Self {
        Self {
            fvar_id,
            name,
            ty,
            borrow: true,
        }
    }
}

/// Argument to a function or constructor application.
///
/// Corresponds to `Arg` in Lean 4's LCNF.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Arg {
    /// Erased argument (proof or type that's computationally irrelevant).
    Erased,
    /// Free variable reference.
    FVar(FVarId),
    /// Type argument (for polymorphic instantiation).
    Type(Expr),
    /// Field index literal (used in _set operations). Part of #1105.
    Index(u32),
}

impl Arg {
    /// Check if this argument is erased.
    pub fn is_erased(&self) -> bool {
        matches!(self, Arg::Erased)
    }

    /// Get the FVarId if this is an FVar argument.
    pub fn as_fvar(&self) -> Option<FVarId> {
        match self {
            Arg::FVar(id) => Some(*id),
            _ => None,
        }
    }
}

/// Value in a let-binding.
///
/// Corresponds to `LetValue` in Lean 4's LCNF.
/// All computations are one of these forms.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LetValue {
    /// Literal constant (Nat, String).
    Lit(Literal),

    /// Erased term (proof or type).
    Erased,

    /// Structure projection: `proj type_name idx struct_fvar`.
    ///
    /// Extracts field `idx` from a structure of type `type_name`.
    Proj {
        /// Inductive type name of the structure.
        type_name: Name,
        /// Field index (0-based).
        idx: u32,
        /// FVar holding the structure value.
        structure: FVarId,
    },

    /// Constant application: `const name levels args`.
    ///
    /// Full application of a top-level constant.
    Const {
        /// Name of the constant.
        name: Name,
        /// Universe level instantiation.
        levels: Vec<Level>,
        /// Arguments (may include erased).
        args: Vec<Arg>,
    },

    /// Local function application: `fvar args`.
    ///
    /// Application of a local function variable.
    FVar {
        /// FVar holding the function.
        fvar: FVarId,
        /// Arguments.
        args: Vec<Arg>,
    },

    /// Constructor application: `ctor name levels args`.
    ///
    /// Build an inductive value.
    Ctor {
        /// Constructor name (e.g., `Nat.succ`).
        name: Name,
        /// Universe levels.
        levels: Vec<Level>,
        /// Constructor arguments.
        args: Vec<Arg>,
    },

    /// Reuse operation: `reuse slot ctor_name levels args`.
    ///
    /// Memory reuse for constructor allocation. The slot FVar holds
    /// a reset slot that may be reused for allocation. If the slot
    /// is uniquely owned, the memory is mutated in place; otherwise
    /// a fresh allocation is made.
    ///
    /// Introduced by reset_reuse pass, consumed by expand_reset_reuse.
    /// Part of #1104.
    Reuse {
        /// FVar holding the reset slot (from `_reset` operation).
        slot: FVarId,
        /// Constructor name to build.
        ctor_name: Name,
        /// Universe levels.
        levels: Vec<Level>,
        /// Constructor arguments (excluding the slot).
        args: Vec<Arg>,
    },
}

impl LetValue {
    /// Create a Nat literal value.
    pub fn nat(n: u64) -> Self {
        LetValue::Lit(Literal::Nat(BigNat::from_u64(n)))
    }

    /// Create a constant application with no arguments.
    pub fn const_simple(name: Name) -> Self {
        LetValue::Const {
            name,
            levels: Vec::new(),
            args: Vec::new(),
        }
    }
}

/// Let declaration in LCNF.
///
/// Corresponds to `LetDecl` in Lean 4's LCNF.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LetDecl {
    /// Unique identifier for this binding.
    pub fvar_id: FVarId,
    /// User-visible name.
    pub name: Name,
    /// Type of the bound value.
    pub ty: Expr,
    /// The computed value.
    pub value: LetValue,
}

impl LetDecl {
    /// Create a new let declaration.
    pub fn new(fvar_id: FVarId, name: Name, ty: Expr, value: LetValue) -> Self {
        Self {
            fvar_id,
            name,
            ty,
            value,
        }
    }
}

/// Function declaration (local function or join point).
///
/// Corresponds to `FunDecl` in Lean 4's LCNF.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunDecl {
    /// Unique identifier for this function.
    pub fvar_id: FVarId,
    /// User-visible name.
    pub name: Name,
    /// Function parameters.
    pub params: Vec<Param>,
    /// Return type.
    pub ty: Expr,
    /// Function body.
    pub body: Box<Code>,
}

impl FunDecl {
    /// Create a new function declaration.
    pub fn new(fvar_id: FVarId, name: Name, params: Vec<Param>, ty: Expr, body: Code) -> Self {
        Self {
            fvar_id,
            name,
            params,
            ty,
            body: Box::new(body),
        }
    }
}

/// Case alternative.
///
/// Corresponds to `AltCore` in Lean 4's LCNF.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Alt {
    /// Constructor pattern: `| ctor params => body`.
    Ctor {
        /// Constructor name.
        ctor_name: Name,
        /// Pattern variables bound by this constructor.
        params: Vec<Param>,
        /// Body to execute if pattern matches.
        body: Box<Code>,
    },
    /// Default pattern: `| _ => body`.
    Default(Box<Code>),
}

impl Alt {
    /// Create a constructor alternative.
    pub fn ctor(ctor_name: Name, params: Vec<Param>, body: Code) -> Self {
        Alt::Ctor {
            ctor_name,
            params,
            body: Box::new(body),
        }
    }

    /// Create a default alternative.
    pub fn default(body: Code) -> Self {
        Alt::Default(Box::new(body))
    }

    /// Get the body of this alternative.
    pub fn body(&self) -> &Code {
        match self {
            Alt::Ctor { body, .. } => body,
            Alt::Default(body) => body,
        }
    }
}

/// Case expression.
///
/// Pattern matching on an inductive value.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Cases {
    /// Name of the inductive type being matched.
    ///
    /// Used by ToMono to dispatch to type-specific transformations
    /// (e.g., Decidable → Bool, Nat cases → Int ops).
    /// Corresponds to `Cases.typeName` in Lean 4's LCNF.
    pub type_name: Name,
    /// Result type of the entire match.
    pub result_type: Expr,
    /// FVar being matched on.
    pub scrutinee: FVarId,
    /// Case alternatives.
    pub alts: Vec<Alt>,
}

impl Cases {
    /// Create a new case expression.
    pub fn new(type_name: Name, result_type: Expr, scrutinee: FVarId, alts: Vec<Alt>) -> Self {
        Self {
            type_name,
            result_type,
            scrutinee,
            alts,
        }
    }

    /// Check if this case has a default alternative.
    pub fn has_default(&self) -> bool {
        self.alts.iter().any(|a| matches!(a, Alt::Default(_)))
    }
}

/// Code block (function body).
///
/// Corresponds to `Code` in Lean 4's LCNF.
/// This is the core computation type in LCNF.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Code {
    /// Let binding: `let x : T := v; body`.
    Let(LetDecl, Box<Code>),

    /// Local function: `fun f (params) : T := fbody; body`.
    Fun(FunDecl, Box<Code>),

    /// Join point: `jp f (params) : T := fbody; body`.
    ///
    /// Join points are local functions that are always tail-called.
    /// They enable efficient compilation of control flow.
    JoinPoint(FunDecl, Box<Code>),

    /// Case analysis on an inductive value.
    Cases(Cases),

    /// Jump to join point: `jmp f args`.
    Jmp {
        /// Join point FVar to jump to.
        jp: FVarId,
        /// Arguments to pass.
        args: Vec<Arg>,
    },

    /// Return a value: `return fvar`.
    Return(FVarId),

    /// Unreachable code (for exhaustiveness).
    Unreachable(Expr),
}

impl Code {
    /// Create a let binding.
    pub fn let_bind(decl: LetDecl, body: Code) -> Self {
        Code::Let(decl, Box::new(body))
    }

    /// Create a local function.
    pub fn fun(decl: FunDecl, body: Code) -> Self {
        Code::Fun(decl, Box::new(body))
    }

    /// Create a join point.
    pub fn join_point(decl: FunDecl, body: Code) -> Self {
        Code::JoinPoint(decl, Box::new(body))
    }

    /// Create a case expression.
    pub fn cases(type_name: Name, result_type: Expr, scrutinee: FVarId, alts: Vec<Alt>) -> Self {
        Code::Cases(Cases::new(type_name, result_type, scrutinee, alts))
    }

    /// Create a jump to a join point.
    pub fn jmp(jp: FVarId, args: Vec<Arg>) -> Self {
        Code::Jmp { jp, args }
    }

    /// Create a return.
    pub fn ret(fvar: FVarId) -> Self {
        Code::Return(fvar)
    }

    /// Check if this code is a terminal (Return, Jmp, or Unreachable).
    pub fn is_terminal(&self) -> bool {
        matches!(
            self,
            Code::Return(_) | Code::Jmp { .. } | Code::Unreachable(_)
        )
    }
}

/// External function attribute.
///
/// Marks a function as externally implemented.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternAttr {
    /// External entry name (e.g., C function name).
    pub entries: Vec<ExternEntry>,
}

/// Single external entry (platform-specific).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExternEntry {
    /// Backend identifier (e.g., "c", "llvm").
    pub backend: String,
    /// External name in that backend.
    pub name: String,
}

/// Declaration value (code or external).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DeclValue {
    /// LCNF code body.
    Code(Box<Code>),
    /// External implementation.
    Extern(ExternAttr),
}

/// Top-level declaration in LCNF.
///
/// Corresponds to `Decl` in Lean 4's LCNF.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Decl {
    /// Declaration name.
    pub name: Name,
    /// Universe level parameters.
    pub level_params: Vec<Name>,
    /// Declaration type.
    pub ty: Expr,
    /// Function parameters.
    pub params: Vec<Param>,
    /// Declaration body.
    pub body: DeclValue,
    /// Whether this is a recursive definition.
    pub recursive: bool,
}

impl Decl {
    /// Create a new code declaration.
    pub fn new(
        name: Name,
        level_params: Vec<Name>,
        ty: Expr,
        params: Vec<Param>,
        body: Code,
        recursive: bool,
    ) -> Self {
        Self {
            name,
            level_params,
            ty,
            params,
            body: DeclValue::Code(Box::new(body)),
            recursive,
        }
    }

    /// Create an extern declaration.
    pub fn extern_decl(
        name: Name,
        level_params: Vec<Name>,
        ty: Expr,
        params: Vec<Param>,
        entries: Vec<ExternEntry>,
    ) -> Self {
        Self {
            name,
            level_params,
            ty,
            params,
            body: DeclValue::Extern(ExternAttr { entries }),
            recursive: false,
        }
    }

    /// Check if this declaration is external.
    pub fn is_extern(&self) -> bool {
        matches!(self.body, DeclValue::Extern(_))
    }
}

mod display;

#[cfg(test)]
mod tests;
