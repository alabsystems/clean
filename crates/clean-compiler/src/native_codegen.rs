// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native code generation types and lowering from kernel `Expr` to native IR.
//!
//! This module provides the instruction-level representation for native code
//! generation: `NativeType` (runtime type tags), `NativeOp` (primitive
//! operations), and `NativeInstr` (SSA-style instructions). The `lower_expr`
//! function converts kernel expressions into a linear instruction sequence,
//! while `erase_proofs` replaces proof/type subterms with the `lcErased`
//! sentinel before lowering.
//!
//! Part of #3084 - Native code generation infrastructure.

use clean_kernel::expr::{Expr, ExprKind, Literal};
use clean_kernel::{Environment, Name};
use thiserror::Error;

// ---------------------------------------------------------------------------
// CodegenError
// ---------------------------------------------------------------------------

/// Errors that can occur during native code generation.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum CodegenError {
    /// Expression form not supported by the native codegen backend.
    #[error("unsupported expression for native codegen: {0}")]
    UnsupportedExpr(String),

    /// Reference to an unknown constant.
    #[error("unknown constant in native codegen: {0}")]
    UnknownConstant(String),

    /// Type that cannot be represented in the native IR.
    #[error("unsupported type for native codegen: {0}")]
    UnsupportedType(String),

    /// Proof or type term reached codegen without being erased.
    #[error("unerased proof term in native codegen: {0}")]
    UnerasedProof(String),
}

// ---------------------------------------------------------------------------
// NativeType
// ---------------------------------------------------------------------------

/// Native runtime type representation.
///
/// Maps kernel types to machine-level storage categories for code generation.
/// `Object` is the fallback for any heap-allocated, reference-counted value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum NativeType {
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    USize,
    Float,
    Double,
    /// Boxed Lean object (heap-allocated, reference-counted).
    Object,
    /// Erased proof/proposition (computationally irrelevant).
    IrrelevantType,
    /// Function closure.
    Closure,
    /// Homogeneous array of elements.
    Array(Box<NativeType>),
    /// Struct with named fields.
    Struct(Vec<(String, NativeType)>),
}

impl NativeType {
    /// Returns `true` if this type is a scalar stored inline (not heap-allocated).
    #[must_use]
    pub(crate) fn is_scalar(&self) -> bool {
        matches!(
            self,
            Self::Uint8
                | Self::Uint16
                | Self::Uint32
                | Self::Uint64
                | Self::USize
                | Self::Float
                | Self::Double
        )
    }

    /// Returns `true` if this type requires reference counting at runtime.
    #[must_use]
    pub(crate) fn is_rc(&self) -> bool {
        matches!(
            self,
            Self::Object | Self::Closure | Self::Array(_) | Self::Struct(_)
        )
    }

    /// Returns `true` if this type is computationally irrelevant.
    #[must_use]
    pub(crate) fn is_irrelevant(&self) -> bool {
        matches!(self, Self::IrrelevantType)
    }
}

// ---------------------------------------------------------------------------
// NativeArg
// ---------------------------------------------------------------------------

/// An argument to a native instruction.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub(crate) enum NativeArg {
    /// Variable reference by name.
    Var(String),
    /// Integer literal.
    LitInt(u64),
    /// String literal.
    LitStr(String),
    /// Erased/irrelevant argument.
    Erased,
}

// ---------------------------------------------------------------------------
// NativeOp
// ---------------------------------------------------------------------------

/// Native operations on machine-level values.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum NativeOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // Comparison
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    // Bitwise / logical
    // Instruction classes nothing builds yet — neither the `expr_to_instrs`
    // lowering nor the codegen tests reach the bitwise, shift, or boxing
    // groups. Kept because this enum is the target instruction set the backend
    // is being built against, not a log of what is reachable today
    // — 2026-07-31.
    #[allow(dead_code)]
    And,
    #[allow(dead_code)]
    Or,
    #[allow(dead_code)]
    Not,
    #[allow(dead_code)]
    Xor,

    // Shifts
    #[allow(dead_code)]
    Shl,
    #[allow(dead_code)]
    Shr,

    // Boxing
    /// Box a scalar into a heap object.
    #[allow(dead_code)]
    Box_,
    /// Unbox a heap object to a scalar.
    #[allow(dead_code)]
    Unbox,

    // Memory
    /// Allocate a new object.
    Alloc,
    /// Deallocate an object.
    Dealloc,

    // Control
    /// Function call by name.
    Call(String),
    /// Projection (field access by index).
    Proj(usize),
    /// Constructor application (name, tag).
    Ctor(String, u16),
    /// Case split on constructor tag: vec of (tag, branch instructions).
    // Staged alongside the bitwise/shift/boxing classes above: the lowering
    // still flattens cases into the caller's instruction stream instead of
    // nesting them here — 2026-07-31.
    #[allow(dead_code)]
    Case(Vec<(u16, Vec<NativeInstr>)>),
}

// ---------------------------------------------------------------------------
// NativeInstr
// ---------------------------------------------------------------------------

/// A single native instruction in SSA-like form.
///
/// Each instruction optionally binds its result to a named variable (`target`)
/// and applies an operation to zero or more arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct NativeInstr {
    /// Variable name for the result, or `None` for void operations.
    pub(crate) target: Option<String>,
    /// The operation to perform.
    pub(crate) op: NativeOp,
    /// Arguments to the operation.
    pub(crate) args: Vec<NativeArg>,
}

impl NativeInstr {
    /// Create a new instruction.
    #[must_use]
    pub(crate) fn new(target: Option<String>, op: NativeOp, args: Vec<NativeArg>) -> Self {
        Self { target, op, args }
    }
}

// ---------------------------------------------------------------------------
// Proof erasure
// ---------------------------------------------------------------------------

/// The sentinel name used for erased proof/type subterms.
const LC_ERASED: &str = "lcErased";

/// Erase proof and type subterms from a kernel expression.
///
/// Replaces any subexpression whose type lives in `Prop` (Sort 0) with the
/// `lcErased` constant. This is a conservative, syntax-directed pass:
///
/// - `Sort _` -> `lcErased` (types are irrelevant)
/// - `Pi` (forall) where result is `Prop` -> `lcErased`
/// - `Lam` body and `Let` value/body are recursively erased
/// - `App` erases both function and argument
/// - Other forms pass through unchanged
///
/// This runs *before* lowering so that `lower_expr` never sees proof terms.
pub(crate) fn erase_proofs(expr: &Expr) -> Expr {
    match expr.kind() {
        // Types and sorts are computationally irrelevant
        ExprKind::Sort(_) => Expr::const_str(LC_ERASED),

        // Recurse into applications
        ExprKind::App(func, arg) => {
            let f = erase_proofs(func);
            let a = erase_proofs(arg);
            Expr::app(f, a)
        }

        // Recurse into lambda bodies
        ExprKind::Lam(bd, ty, body) => {
            let ty_erased = erase_proofs(ty);
            let body_erased = erase_proofs(body);
            Expr::lam(*bd, ty_erased, body_erased)
        }

        // Recurse into pi/forall — erase if the body is Prop
        ExprKind::Pi(bd, dom, codom) => {
            if codom.is_prop() {
                return Expr::const_str(LC_ERASED);
            }
            let dom_erased = erase_proofs(dom);
            let codom_erased = erase_proofs(codom);
            Expr::pi(*bd, dom_erased, codom_erased)
        }

        // Recurse into let bindings
        ExprKind::Let(name, ty, val, body, non_dep) => {
            let ty_erased = erase_proofs(ty);
            let val_erased = erase_proofs(val);
            let body_erased = erase_proofs(body);
            Expr::let_named(name.clone(), ty_erased, val_erased, body_erased, *non_dep)
        }

        // Metadata wrapper — recurse into inner
        ExprKind::MData(md, inner) => {
            let inner_erased = erase_proofs(inner);
            Expr::mdata(md.clone(), inner_erased)
        }

        // Projection — recurse into the struct expression
        ExprKind::Proj(name, idx, struct_expr) => {
            let struct_erased = erase_proofs(struct_expr);
            Expr::proj(name.clone(), *idx, struct_erased)
        }

        // Atoms pass through unchanged: BVar, FVar, Const, Lit
        _ => expr.clone(),
    }
}

// ---------------------------------------------------------------------------
// Variable name generation
// ---------------------------------------------------------------------------

/// Counter for generating unique variable names during lowering.
struct VarGen {
    next: u32,
}

impl VarGen {
    fn new() -> Self {
        Self { next: 0 }
    }

    fn fresh(&mut self) -> String {
        let name = format!("_x{}", self.next);
        self.next += 1;
        name
    }
}

// ---------------------------------------------------------------------------
// Lowering: Expr -> Vec<NativeInstr>
// ---------------------------------------------------------------------------

/// Classify a constant name to a native type.
///
/// Recognizes Lean 4 built-in type names.
fn classify_type_name(name: &str) -> Option<NativeType> {
    match name {
        "UInt8" => Some(NativeType::Uint8),
        "UInt16" => Some(NativeType::Uint16),
        "UInt32" => Some(NativeType::Uint32),
        "UInt64" => Some(NativeType::Uint64),
        "USize" => Some(NativeType::USize),
        "Float" => Some(NativeType::Float),
        "Float32" => Some(NativeType::Float),
        "Float64" | "Double" => Some(NativeType::Double),
        "String" | "ByteArray" | "Array" => Some(NativeType::Object),
        LC_ERASED => Some(NativeType::IrrelevantType),
        _ => None,
    }
}

/// Lower a single expression into native instructions, appending to `instrs`.
///
/// Returns the `NativeArg` referencing the result of the expression.
fn lower_expr_inner(
    expr: &Expr,
    env: &Environment,
    instrs: &mut Vec<NativeInstr>,
    vgen: &mut VarGen,
) -> Result<NativeArg, CodegenError> {
    match expr.kind() {
        // Literal Nat -> integer constant
        ExprKind::Lit(Literal::Nat(n)) => {
            let val = n.to_u64().unwrap_or(0);
            Ok(NativeArg::LitInt(val))
        }

        // Literal String -> string constant
        ExprKind::Lit(Literal::String(s)) => Ok(NativeArg::LitStr(s.to_string())),

        // Constant reference
        ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            if name_str == LC_ERASED {
                return Ok(NativeArg::Erased);
            }
            // Check if it's a known constant in the environment
            let n = Name::from_string(&name_str);
            if env.get_const(&n).is_none() && classify_type_name(&name_str).is_none() {
                return Err(CodegenError::UnknownConstant(name_str));
            }
            Ok(NativeArg::Var(name_str))
        }

        // Free variable
        ExprKind::FVar(id) => Ok(NativeArg::Var(format!("_fv{}", id.as_u64()))),

        // Bound variable (should have been substituted, but handle gracefully)
        ExprKind::BVar(idx) => Ok(NativeArg::Var(format!("_bv{idx}"))),

        // Application: lower function and args, emit Call
        ExprKind::App(..) => {
            let head = expr.get_app_fn();
            let args = expr.get_app_args();

            // Try to resolve the head as a constant name for the call
            let func_name = match head.kind() {
                ExprKind::Const(name, _) => name.to_string(),
                _ => {
                    // Non-constant head: lower head as closure, emit indirect call
                    let head_arg = lower_expr_inner(head, env, instrs, vgen)?;
                    let target = vgen.fresh();
                    let mut call_args = vec![head_arg];
                    for a in &args {
                        call_args.push(lower_expr_inner(a, env, instrs, vgen)?);
                    }
                    instrs.push(NativeInstr::new(
                        Some(target.clone()),
                        NativeOp::Call("__apply".to_owned()),
                        call_args,
                    ));
                    return Ok(NativeArg::Var(target));
                }
            };

            // Lower all arguments
            let mut lowered_args = Vec::with_capacity(args.len());
            for a in &args {
                lowered_args.push(lower_expr_inner(a, env, instrs, vgen)?);
            }

            let target = vgen.fresh();
            instrs.push(NativeInstr::new(
                Some(target.clone()),
                NativeOp::Call(func_name),
                lowered_args,
            ));
            Ok(NativeArg::Var(target))
        }

        // Projection
        ExprKind::Proj(_name, idx, struct_expr) => {
            let struct_arg = lower_expr_inner(struct_expr, env, instrs, vgen)?;
            let target = vgen.fresh();
            instrs.push(NativeInstr::new(
                Some(target.clone()),
                NativeOp::Proj(*idx as usize),
                vec![struct_arg],
            ));
            Ok(NativeArg::Var(target))
        }

        // Let binding: lower value, bind name, lower body
        ExprKind::Let(name, _ty, val, body, _non_dep) => {
            let val_arg = lower_expr_inner(val, env, instrs, vgen)?;
            // Bind the let variable (use name if available, otherwise generate)
            let var_name = if name.is_anon() {
                vgen.fresh()
            } else {
                format!("_let_{}", name)
            };
            // Emit an identity assignment
            instrs.push(NativeInstr::new(
                Some(var_name.clone()),
                NativeOp::Call("__id".to_owned()),
                vec![val_arg],
            ));
            // Lower body (the body references the let-bound var via BVar)
            lower_expr_inner(body, env, instrs, vgen)
        }

        // Lambda — emit as closure allocation
        ExprKind::Lam(..) => {
            let target = vgen.fresh();
            instrs.push(NativeInstr::new(
                Some(target.clone()),
                NativeOp::Alloc,
                vec![], // closure capture handled by later pass
            ));
            Ok(NativeArg::Var(target))
        }

        // Sort — should have been erased
        ExprKind::Sort(_) => Ok(NativeArg::Erased),

        // Pi — type-level, should have been erased
        ExprKind::Pi(..) => Ok(NativeArg::Erased),

        // MData — transparent wrapper, lower inner
        ExprKind::MData(_, inner) => lower_expr_inner(inner, env, instrs, vgen),

        // Fallback for any remaining expression forms
        _ => Err(CodegenError::UnsupportedExpr(format!("{:?}", expr.kind()))),
    }
}

/// Lower a kernel `Expr` into a sequence of native instructions.
///
/// The expression should have proofs erased (via `erase_proofs`) before
/// calling this function. The resulting instruction sequence is in
/// SSA-like form where each instruction optionally binds a named variable.
///
/// # Errors
///
/// Returns `CodegenError` if the expression contains forms that cannot be
/// lowered (e.g., unerased proofs, unknown constants).
pub(crate) fn lower_expr(expr: &Expr, env: &Environment) -> Result<Vec<NativeInstr>, CodegenError> {
    let mut instrs = Vec::new();
    let mut vgen = VarGen::new();
    let _result = lower_expr_inner(expr, env, &mut instrs, &mut vgen)?;
    Ok(instrs)
}

#[cfg(test)]
#[path = "native_codegen_tests.rs"]
mod tests;
