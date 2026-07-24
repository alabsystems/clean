// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constant Folding for L5CNF
//!
//! Evaluates constant expressions at compile time when all operands
//! are known literals.
//!
//! # Supported Operations
//!
//! - **Nat:** add, sub, mul, div, mod, beq, ble, blt
//! - **String:** append, length
//!
//! Future: Int operations, Bool operations (requires constructor tracking)
//!
//! # Example
//!
//! Before:
//! ```text
//! let _1 := 2
//! let _2 := 3
//! let _3 := Nat.add _1 _2
//! return _3
//! ```
//!
//! After (when _1, _2 are propagated):
//! ```text
//! let _1 := 2
//! let _2 := 3
//! let _3 := 5
//! return _3
//! ```
//!
//! Note: Full constant propagation requires DCE to remove _1, _2.
//!
//! Part of #963 - Compiler IR infrastructure.

use crate::lcnf::{Arg, Cases, Code, Decl, DeclValue, FunDecl, LetDecl, LetValue};
use crate::CodeFolder;
use clean_kernel::{BigNat, FVarId, Literal};
use std::collections::HashMap;

/// Context for constant folding.
struct ConstFoldCtx {
    /// Known constant values for FVarIds.
    constants: HashMap<FVarId, Literal>,
}

impl ConstFoldCtx {
    fn new() -> Self {
        Self {
            constants: HashMap::new(),
        }
    }

    /// Record a known constant value.
    fn record(&mut self, fvar: FVarId, lit: Literal) {
        self.constants.insert(fvar, lit);
    }

    /// Look up a constant value for an FVarId.
    fn get(&self, fvar: &FVarId) -> Option<&Literal> {
        self.constants.get(fvar)
    }

    /// Try to get a literal value from an argument.
    fn arg_to_literal(&self, arg: &Arg) -> Option<&Literal> {
        match arg {
            Arg::FVar(fvar) => self.get(fvar),
            _ => None,
        }
    }
}

/// Try to fold a constant application.
fn try_fold_const(name: &str, args: &[Arg], ctx: &ConstFoldCtx) -> Option<LetValue> {
    match name {
        // Nat operations
        "Nat.add" => fold_nat_binop_checked(args, ctx, |a, b| a.checked_add(b)),
        "Nat.sub" => fold_nat_binop(args, ctx, |a, b| a.saturating_sub(b)),
        "Nat.mul" => fold_nat_binop_checked(args, ctx, |a, b| a.checked_mul(b)),
        "Nat.div" => fold_nat_binop_checked(args, ctx, |a, b| a.checked_div(b)),
        "Nat.mod" => fold_nat_binop_checked(args, ctx, |a, b| a.checked_rem(b)),
        "Nat.beq" => fold_nat_cmp(args, ctx, |a, b| a == b),
        "Nat.ble" => fold_nat_cmp(args, ctx, |a, b| a <= b),
        "Nat.blt" => fold_nat_cmp(args, ctx, |a, b| a < b),

        // String operations
        "String.append" => fold_string_append(args, ctx),
        "String.length" => fold_string_length(args, ctx),

        // Bool operations (represented as constructors, but can appear as const calls)
        "Bool.not" => fold_bool_not(args, ctx),

        _ => None,
    }
}

/// Fold a binary Nat operation.
fn fold_nat_binop<F>(args: &[Arg], ctx: &ConstFoldCtx, op: F) -> Option<LetValue>
where
    F: Fn(u64, u64) -> u64,
{
    if args.len() != 2 {
        return None;
    }

    let a = match ctx.arg_to_literal(&args[0])? {
        Literal::Nat(n) => n.to_u64()?,
        _ => return None,
    };

    let b = match ctx.arg_to_literal(&args[1])? {
        Literal::Nat(n) => n.to_u64()?,
        _ => return None,
    };

    Some(LetValue::Lit(Literal::Nat(BigNat::Small(op(a, b)))))
}

/// Fold a binary Nat operation that can fail (div, mod by zero).
fn fold_nat_binop_checked<F>(args: &[Arg], ctx: &ConstFoldCtx, op: F) -> Option<LetValue>
where
    F: Fn(u64, u64) -> Option<u64>,
{
    if args.len() != 2 {
        return None;
    }

    let a = match ctx.arg_to_literal(&args[0])? {
        Literal::Nat(n) => n.to_u64()?,
        _ => return None,
    };

    let b = match ctx.arg_to_literal(&args[1])? {
        Literal::Nat(n) => n.to_u64()?,
        _ => return None,
    };

    let result = op(a, b)?;
    Some(LetValue::Lit(Literal::Nat(BigNat::Small(result))))
}

/// Fold a Nat comparison to Bool constructor.
fn fold_nat_cmp<F>(args: &[Arg], ctx: &ConstFoldCtx, op: F) -> Option<LetValue>
where
    F: Fn(u64, u64) -> bool,
{
    if args.len() != 2 {
        return None;
    }

    let a = match ctx.arg_to_literal(&args[0])? {
        Literal::Nat(n) => n.to_u64()?,
        _ => return None,
    };

    let b = match ctx.arg_to_literal(&args[1])? {
        Literal::Nat(n) => n.to_u64()?,
        _ => return None,
    };

    let result = op(a, b);
    let ctor_name = if result { "Bool.true" } else { "Bool.false" };

    Some(LetValue::Ctor {
        name: clean_kernel::Name::from_string(ctor_name),
        levels: vec![],
        args: vec![],
    })
}

/// Fold String.append.
fn fold_string_append(args: &[Arg], ctx: &ConstFoldCtx) -> Option<LetValue> {
    if args.len() != 2 {
        return None;
    }

    let a = match ctx.arg_to_literal(&args[0])? {
        Literal::String(s) => s.clone(),
        _ => return None,
    };

    let b = match ctx.arg_to_literal(&args[1])? {
        Literal::String(s) => s.clone(),
        _ => return None,
    };

    Some(LetValue::Lit(Literal::String(
        format!("{}{}", &*a, &*b).into(),
    )))
}

/// Fold String.length.
fn fold_string_length(args: &[Arg], ctx: &ConstFoldCtx) -> Option<LetValue> {
    if args.len() != 1 {
        return None;
    }

    let s = match ctx.arg_to_literal(&args[0])? {
        Literal::String(s) => s,
        _ => return None,
    };

    Some(LetValue::Lit(Literal::Nat(BigNat::Small(
        s.chars().count() as u64,
    ))))
}

/// Fold Bool.not.
fn fold_bool_not(args: &[Arg], ctx: &ConstFoldCtx) -> Option<LetValue> {
    // Bool.not takes a single Bool argument
    // We'd need to track constructor info to fold this properly
    // For now, skip - requires SimpValue pass with constructor tracking
    let _ = (args, ctx);
    None
}

/// Apply constant folding to a let-value.
fn fold_value(value: &LetValue, ctx: &ConstFoldCtx) -> LetValue {
    match value {
        LetValue::Const {
            name,
            levels: _,
            args,
        } => {
            if let Some(folded) = try_fold_const(&name.to_string(), args, ctx) {
                folded
            } else {
                value.clone()
            }
        }
        _ => value.clone(),
    }
}

/// CodeFolder that performs constant folding during traversal.
///
/// Delegates structural recursion to the CodeFolder trait. Overrides
/// fold_let to fold constant values and record results, and
/// fold_fun/fold_join_point/fold_cases for context save/restore.
struct ConstFoldFolder {
    ctx: ConstFoldCtx,
}

impl CodeFolder for ConstFoldFolder {
    fn fold_let(&mut self, decl: LetDecl, body: Code) -> Code {
        self.ctx.constants.remove(&decl.fvar_id);
        let new_value = fold_value(&decl.value, &self.ctx);
        if let LetValue::Lit(lit) = &new_value {
            self.ctx.record(decl.fvar_id, lit.clone());
        }
        Code::Let(
            LetDecl {
                value: new_value,
                ..decl
            },
            Box::new(self.fold_code(&body)),
        )
    }

    fn fold_fun(&mut self, decl: FunDecl, body: Code) -> Code {
        let saved = self.ctx.constants.clone();
        let new_fun_body = self.fold_code(&decl.body);
        self.ctx.constants = saved;
        Code::Fun(
            FunDecl {
                body: Box::new(new_fun_body),
                ..decl
            },
            Box::new(self.fold_code(&body)),
        )
    }

    fn fold_join_point(&mut self, decl: FunDecl, body: Code) -> Code {
        let saved = self.ctx.constants.clone();
        let new_jp_body = self.fold_code(&decl.body);
        self.ctx.constants = saved;
        Code::JoinPoint(
            FunDecl {
                body: Box::new(new_jp_body),
                ..decl
            },
            Box::new(self.fold_code(&body)),
        )
    }

    fn fold_cases(&mut self, cases: Cases) -> Code {
        let saved = self.ctx.constants.clone();
        let Cases {
            type_name,
            result_type,
            scrutinee,
            alts,
        } = cases;
        let mut new_alts = Vec::with_capacity(alts.len());
        for alt in alts {
            self.ctx.constants = saved.clone();
            new_alts.push(self.fold_alt(alt));
        }
        self.ctx.constants = saved;
        Code::Cases(Cases {
            type_name,
            result_type,
            scrutinee,
            alts: new_alts,
        })
    }
}

/// Apply constant folding to a declaration.
///
/// Evaluates constant expressions at compile time, replacing
/// operations on known literals with their results.
pub fn fold_constants(decl: &Decl) -> Decl {
    let body = match &decl.body {
        DeclValue::Code(code) => {
            let mut folder = ConstFoldFolder {
                ctx: ConstFoldCtx::new(),
            };
            DeclValue::Code(Box::new(folder.fold_code(code)))
        }
        DeclValue::Extern(attr) => DeclValue::Extern(attr.clone()),
    };

    Decl {
        name: decl.name.clone(),
        level_params: decl.level_params.clone(),
        ty: decl.ty.clone(),
        params: decl.params.clone(),
        body,
        recursive: decl.recursive,
    }
}

/// Apply constant folding directly to a Code block.
pub fn fold_constants_in_code(code: &Code) -> Code {
    ConstFoldFolder {
        ctx: ConstFoldCtx::new(),
    }
    .fold_code(code)
}

#[cfg(test)]
mod tests;
