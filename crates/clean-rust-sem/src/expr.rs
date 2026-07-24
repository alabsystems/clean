// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust Expression Semantics
//!
//! This module defines the semantics of Rust expressions,
//! including evaluation rules and type checking.
//!
//! ## Expression Categories
//!
//! - **Literals**: Numbers, booleans, strings, characters
//! - **Place Expressions**: Variables, field access, indexing
//! - **Operators**: Arithmetic, logical, comparison
//! - **Control Flow**: if/else, match, loops
//! - **Calls**: Function and method calls
//! - **Blocks**: Sequences of statements with final expression

use crate::types::{ConstGenericArg, Mutability, RustType};
use crate::values::{BinOp, UnOp, Value};
use serde::{Deserialize, Serialize};

/// Inline assembly expression or item payload.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InlineAsm {
    /// Concatenated assembly template.
    pub template: String,
    /// Operand descriptors in source order.
    pub operands: Vec<AsmOperand>,
    /// Parsed asm options.
    #[serde(default)]
    pub options: AsmOptions,
    /// Conservatively captured clobber declarations (currently ABI names).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub clobbers: Vec<String>,
}

/// Operand to an inline assembly invocation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AsmOperand {
    /// Input operand, e.g. `in(reg) value`.
    In { constraint: String, expr: Expr },
    /// Output operand, e.g. `out(reg) dst` or `lateout(reg) _`.
    Out {
        constraint: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        expr: Option<Expr>,
    },
    /// Read-write operand, e.g. `inout(reg) value` or `inout(reg) src => dst`.
    InOut {
        constraint: String,
        in_expr: Expr,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        out_expr: Option<Expr>,
    },
    /// Compile-time constant operand.
    Const(Expr),
    /// Symbol operand, e.g. `sym foo`.
    Sym(String),
}

/// Parsed `asm!` / `global_asm!` options.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct AsmOptions {
    pub pure: bool,
    pub nomem: bool,
    pub readonly: bool,
    pub preserves_flags: bool,
    pub nostack: bool,
    pub noreturn: bool,
    pub att_syntax: bool,
    pub raw: bool,
    pub may_unwind: bool,
}

/// A Rust expression
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Expr {
    /// Literal value
    Literal(Value),

    /// Variable reference (place expression)
    Var { name: String, local_idx: u32 },

    /// Field access: expr.field
    Field { base: Box<Expr>, field: String },

    /// Array/slice indexing: `expr[index]`
    Index { base: Box<Expr>, index: Box<Expr> },

    /// Dereference: *expr
    Deref(Box<Expr>),

    /// Address-of: &expr or &mut expr
    AddrOf {
        mutability: Mutability,
        expr: Box<Expr>,
    },

    /// Binary operation
    BinOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },

    /// Unary operation
    UnOp { op: UnOp, expr: Box<Expr> },

    /// Type cast: expr as Type
    Cast { expr: Box<Expr>, target: RustType },

    /// Function call (type_args carries explicit turbofish type arguments)
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        type_args: Vec<RustType>,
    },

    /// Method call: expr.method(args)
    MethodCall {
        receiver: Box<Expr>,
        method: String,
        args: Vec<Expr>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        type_args: Vec<RustType>,
    },

    /// If expression
    If {
        condition: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Option<Box<Expr>>,
    },

    /// Match expression
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
    },

    /// Block expression
    Block {
        stmts: Vec<Stmt>,
        expr: Option<Box<Expr>>,
    },

    /// Tuple construction
    Tuple(Vec<Expr>),

    /// Array construction
    Array(Vec<Expr>),

    /// Array repeat: [expr; count]
    ArrayRepeat { value: Box<Expr>, count: usize },

    /// Struct construction
    Struct {
        name: String,
        fields: Vec<(String, Expr)>,
        /// Explicit type arguments for generic structs (e.g. `Foo::<u32> { .. }`)
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        type_args: Vec<RustType>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        const_args: Vec<ConstGenericArg>,
    },

    /// Union initialization
    ///
    /// Unlike structs, a union can only be initialized with one field.
    /// The initialized field determines the active variant.
    /// Creating a union is safe; reading from it requires unsafe.
    UnionInit {
        name: String,
        /// The single field to initialize (field_name, value)
        field: (String, Box<Expr>),
    },

    /// Union field access (requires unsafe context)
    ///
    /// Reads the union's memory as the specified field type.
    /// This is unsafe because the compiler cannot verify the
    /// field being read matches the field that was last written.
    UnionFieldAccess {
        union_expr: Box<Expr>,
        field: String,
    },

    /// Enum variant construction
    EnumVariant {
        enum_name: String,
        variant: String,
        payload: EnumVariantPayload,
        /// Explicit type arguments for generic enums (e.g. `Option::<i32>::Some(42)`)
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        type_args: Vec<RustType>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        const_args: Vec<ConstGenericArg>,
    },

    /// Closure
    Closure {
        params: Vec<(String, RustType)>,
        body: Box<Expr>,
        captures: Vec<(String, Mutability)>,
        /// Whether this is a `move` closure (captures by value instead of by reference)
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        capture_by_value: bool,
    },

    /// Range: start..end or start..=end
    Range {
        start: Option<Box<Expr>>,
        end: Option<Box<Expr>>,
        inclusive: bool,
    },

    /// Return expression
    Return(Option<Box<Expr>>),

    /// Break expression (with optional value and label)
    Break {
        label: Option<String>,
        value: Option<Box<Expr>>,
    },

    /// Continue expression
    Continue { label: Option<String> },

    /// Loop (infinite)
    Loop {
        label: Option<String>,
        body: Box<Expr>,
    },

    /// While loop
    While {
        label: Option<String>,
        condition: Box<Expr>,
        body: Box<Expr>,
    },

    /// For loop
    For {
        label: Option<String>,
        pattern: Box<Pattern>,
        iter: Box<Expr>,
        body: Box<Expr>,
    },

    /// Unsafe block: unsafe { ... }
    ///
    /// Unsafe blocks allow operations that the compiler cannot verify as safe:
    /// - Raw pointer dereferencing
    /// - Calling unsafe functions
    /// - Accessing mutable statics
    /// - Accessing union fields
    /// - Calling FFI functions
    Unsafe {
        /// The block expression executed in unsafe context
        block: Box<Expr>,
    },

    /// Raw pointer dereference: *ptr where ptr is *const T or *mut T
    ///
    /// Separate from Deref because raw pointer deref requires unsafe context
    RawDeref(Box<Expr>),

    /// Assignment: target = value
    ///
    /// Assigns `value` to the place expression `target`. Returns `()`.
    /// The target must be a mutable variable, field, or index expression.
    Assign { target: Box<Expr>, value: Box<Expr> },

    /// Compound assignment: target <op>= value
    ///
    /// Kept distinct from `Assign` so lowering can preserve single-evaluation
    /// place semantics for compound-assignment targets.
    AssignOp {
        op: BinOp,
        target: Box<Expr>,
        value: Box<Expr>,
    },

    /// Panic expression: panic!("message")
    ///
    /// Models Rust's panic mechanism. Currently implements abort semantics
    /// (immediate termination) rather than unwinding semantics.
    /// Covers panic!, unreachable!, todo!, unimplemented! macros.
    Panic { message: Box<Expr> },

    /// Await expression: expr.await
    ///
    /// Evaluates the base expression to a future value, then drives it
    /// to completion. In the verification model, futures are evaluated
    /// synchronously (no actual task scheduling).
    Await { base: Box<Expr> },

    /// Async block: async { ... } or async move { ... }
    ///
    /// Creates a future value that lazily wraps the block body.
    /// The future is evaluated when `.await`ed.
    Async {
        /// Whether this is `async move { ... }` (captures by value)
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        capture_by_value: bool,
        /// The block body
        body: Box<Expr>,
    },

    /// Inline assembly expression: `asm!(...)`
    ///
    /// Evaluation reads input operands, havocs output operands, and may
    /// conservatively havoc modeled memory when `nomem` is not present.
    InlineAsm(InlineAsm),
}

/// Enum variant payload for construction
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EnumVariantPayload {
    Unit,
    Tuple(Vec<Expr>),
    Struct(Vec<(String, Expr)>),
}

/// Match arm
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
}

/// Pattern for matching
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Pattern {
    Wildcard,
    Binding {
        name: String,
        mutable: bool,
        subpattern: Option<Box<Pattern>>,
    },
    Literal(Value),
    Ref {
        mutability: Mutability,
        pattern: Box<Pattern>,
    },
    Tuple(Vec<Pattern>),
    Struct {
        name: String,
        fields: Vec<(String, Pattern)>,
        rest: bool,
    },
    EnumVariant {
        enum_name: String,
        variant: String,
        payload: EnumPatternPayload,
    },
    Or(Vec<Pattern>),
    Range {
        start: Value,
        end: Value,
        inclusive: bool,
    },
    /// Slice pattern: [a, b, .., z]
    Slice(Vec<Pattern>),
    /// Rest pattern: .. (used inside slice patterns)
    Rest,
}

/// Enum variant pattern payload
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EnumPatternPayload {
    Unit,
    Tuple(Vec<Pattern>),
    Struct(Vec<(String, Pattern)>),
}

/// Statement (used in blocks)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Stmt {
    /// Let binding: `let pattern = expr` or `let pattern = expr else { diverge }`
    ///
    /// When `else_block` is `Some`, the pattern must be refutable and the else
    /// block must diverge (return, break, continue, or panic). This models
    /// Rust's let-else syntax (RFC 3137, stabilized in Rust 1.65).
    Let {
        pattern: Pattern,
        ty: Option<RustType>,
        init: Option<Box<Expr>>,
        /// Diverging block executed when a refutable pattern fails to match.
        else_block: Option<Box<Expr>>,
    },

    /// Expression statement (value discarded)
    Expr(Expr),

    /// Item declaration (function, struct, etc.)
    Item(Item),
}

pub use crate::item::Item;

/// Expression evaluation result
#[must_use]
#[derive(Debug, Clone)]
pub enum EvalResult {
    /// Normal value
    Value(Value),
    /// Return from function
    Return(Value),
    /// Break from loop (with optional label and value)
    Break {
        label: Option<String>,
        value: Option<Value>,
    },
    /// Continue loop (with optional label)
    Continue { label: Option<String> },
    /// Panic occurred (abort semantics - immediate termination)
    ///
    /// Unlike Error which indicates evaluation failure, Panic represents
    /// explicit runtime panic (panic!, unwrap on None, etc.)
    Panic(String),
    /// Error during evaluation
    Error(String),
}

impl EvalResult {
    /// Check if result is a normal value
    #[must_use]
    pub fn is_value(&self) -> bool {
        matches!(self, EvalResult::Value(_))
    }

    /// Get value if normal
    #[must_use]
    pub fn value(self) -> Option<Value> {
        match self {
            EvalResult::Value(v) => Some(v),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literal_expr() {
        let expr = Expr::Literal(Value::u32(42));
        assert!(matches!(expr, Expr::Literal(_)));
    }

    #[test]
    fn test_binop_expr() {
        let expr = Expr::BinOp {
            op: BinOp::Add,
            left: Box::new(Expr::Literal(Value::u32(1))),
            right: Box::new(Expr::Literal(Value::u32(2))),
        };
        assert!(matches!(expr, Expr::BinOp { .. }));
    }

    #[test]
    fn test_if_expr() {
        let expr = Expr::If {
            condition: Box::new(Expr::Literal(Value::Bool(true))),
            then_branch: Box::new(Expr::Literal(Value::u32(1))),
            else_branch: Some(Box::new(Expr::Literal(Value::u32(2)))),
        };
        assert!(matches!(expr, Expr::If { .. }));
    }

    #[test]
    fn test_pattern_matching() {
        let pattern = Pattern::Tuple(vec![
            Pattern::Binding {
                name: "x".to_string(),
                mutable: false,
                subpattern: None,
            },
            Pattern::Wildcard,
        ]);
        assert!(matches!(pattern, Pattern::Tuple(_)));
    }

    #[test]
    fn test_closure_expr() {
        let closure = Expr::Closure {
            params: vec![("x".to_string(), RustType::Uint(crate::types::UintType::U32))],
            body: Box::new(Expr::Var {
                name: "x".to_string(),
                local_idx: 0,
            }),
            captures: vec![],
            capture_by_value: false,
        };
        assert!(matches!(closure, Expr::Closure { .. }));
    }

    #[test]
    fn test_match_expr() {
        let match_expr = Expr::Match {
            scrutinee: Box::new(Expr::Var {
                name: "opt".to_string(),
                local_idx: 0,
            }),
            arms: vec![
                MatchArm {
                    pattern: Pattern::EnumVariant {
                        enum_name: "Option".to_string(),
                        variant: "Some".to_string(),
                        payload: EnumPatternPayload::Tuple(vec![Pattern::Binding {
                            name: "x".to_string(),
                            mutable: false,
                            subpattern: None,
                        }]),
                    },
                    guard: None,
                    body: Expr::Var {
                        name: "x".to_string(),
                        local_idx: 1,
                    },
                },
                MatchArm {
                    pattern: Pattern::EnumVariant {
                        enum_name: "Option".to_string(),
                        variant: "None".to_string(),
                        payload: EnumPatternPayload::Unit,
                    },
                    guard: None,
                    body: Expr::Literal(Value::u32(0)),
                },
            ],
        };
        assert!(matches!(match_expr, Expr::Match { .. }));
    }
}
