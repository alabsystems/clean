// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reference Count Insertion
//!
//! Inserts `inc` and `dec` operations for reference counting based on
//! borrow annotations. Based on "Counting Immutable Beans" (Ullrich & de Moura).
//!
//! # Algorithm Overview
//!
//! Traverses code **backward**, tracking live variables:
//! 1. At `return x`: x is live
//! 2. At `let x := v; body`: remove x from live set, process value
//! 3. Insert `inc` before consuming owned values
//! 4. Insert `dec` when variables become dead
//!
//! # Key Rules
//!
//! - Borrowed parameters never inc/dec'd
//! - Owned parameters eventually dec'd if not returned (their death `dec`
//!   sits on every return path, so a consuming use of a PARAM always
//!   compensates with an `inc`)
//! - Consuming sites (constructor stores, owned call args, dynamic applies,
//!   reuse) `inc` a consumed operand ONLY when it stays live afterwards; a
//!   non-param local's LAST use transfers its ownership to the consumer
//!   outright (Perceus's dec-free last use — see
//!   [`helpers::add_inc_for_consumed`]). The pre-R2 behavior of
//!   unconditionally inc'ing every consumed operand leaked one reference
//!   per consuming last use (a local has no death `dec` anywhere: not at
//!   its binding — it WAS live — and not at return — only params dec
//!   there); `List.recOn`'s synthesized `go` leaked per cons step exactly
//!   this way.
//!
//! Part of #963 - Compiler IR infrastructure.

use crate::lcnf::{Alt, Arg, Cases, Code, Decl, DeclValue, FunDecl};
use crate::rc::borrow::{BorrowMap, Ownership};
use crate::rc::FVarIdAllocator;
use clean_kernel::{Expr, ExprKind, FVarId, Name};
use std::collections::{HashMap, HashSet};
use std::sync::LazyLock;

/// Cached set of scalar type names that never need RC operations.
///
/// Initialized once; avoids String allocation on every `is_scalar_type` call.
/// Matches Lean 4's `IRType.isScalar`: all types stored by value at runtime.
/// `Nat` and `Int` are intentionally absent — they are boxed BigNum objects.
static SCALAR_TYPES: LazyLock<HashSet<Name>> = LazyLock::new(|| {
    [
        "Bool", "UInt8", "UInt16", "UInt32", "UInt64", "USize", "Float", "Float32", "Float64",
        "Char", "Unit", "PUnit",
    ]
    .iter()
    .map(|s| Name::from_string(s))
    .collect()
});

mod helpers;
use helpers::{process_let_value, wrap_dec, wrap_inc};

// Re-exports for test access via `use super::*;`
#[cfg(test)]
pub(crate) use crate::lcnf::{LetDecl, LetValue};

/// Check if a type expression is a scalar type that never needs RC.
///
/// Matches Lean 4's `!isPossibleRef` gate in `ExplicitRC.lean`. Scalar types
/// are stored by value and never require `inc`/`dec` operations. Erased types
/// (Unit, PUnit) also skip RC as they carry no runtime data.
///
/// Conservative: unknown types return `false` (assumed to be possible refs).
fn is_scalar_type(ty: &Expr) -> bool {
    let head = ty.strip_mdata().get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        SCALAR_TYPES.contains(name)
    } else {
        false
    }
}

/// Live variable tracking during RC insertion.
#[derive(Clone, Debug, Default)]
struct LiveVars {
    /// Variables that are still live after this point.
    vars: HashSet<FVarId>,
    /// Variables derived from borrowed parameters (skip inc/dec).
    borrows: HashSet<FVarId>,
}

impl LiveVars {
    fn new() -> Self {
        Self::default()
    }

    /// Mark a variable as live.
    fn mark_live(&mut self, fvar: FVarId) {
        self.vars.insert(fvar);
    }

    /// Mark a variable as dead (remove from live set).
    fn mark_dead(&mut self, fvar: FVarId) {
        self.vars.remove(&fvar);
    }

    /// Check if a variable is live.
    fn is_live(&self, fvar: FVarId) -> bool {
        self.vars.contains(&fvar)
    }

    /// Check if a variable is borrowed (skip RC operations).
    fn is_borrowed(&self, fvar: FVarId) -> bool {
        self.borrows.contains(&fvar)
    }

    /// Mark a variable as borrowed.
    fn mark_borrowed(&mut self, fvar: FVarId) {
        self.borrows.insert(fvar);
    }
}

/// Context for RC insertion.
struct RCContext<'a> {
    /// Borrow annotations for all functions.
    borrow_map: &'a BorrowMap,
    /// Current function's parameter ownership.
    params: Vec<(FVarId, Ownership)>,
    /// Variables derived from other variables (for borrowed propagation).
    derived_from: HashMap<FVarId, FVarId>,
    /// Maps FVarId to its type expression, for scalar type exclusion.
    type_map: HashMap<FVarId, Expr>,
    /// Locals bound to `LetValue::Erased` (erased proofs/types). They carry
    /// no runtime object — `emit_c` materializes them as a null/zero
    /// placeholder — so every RC operation on them is at best a no-op and at
    /// worst a crash (`clean_inc(NULL)` in `Char.ofNat`'s invalid arm, R3).
    erased_locals: HashSet<FVarId>,
    /// FVarId allocator for generating fresh identifiers.
    alloc: FVarIdAllocator,
}

impl<'a> RCContext<'a> {
    fn new(borrow_map: &'a BorrowMap) -> Self {
        Self {
            borrow_map,
            params: Vec::new(),
            derived_from: HashMap::new(),
            type_map: HashMap::new(),
            erased_locals: HashSet::new(),
            alloc: FVarIdAllocator::for_insert_rc(),
        }
    }

    /// Generate a fresh FVarId.
    fn fresh_fvar(&mut self) -> FVarId {
        self.alloc.fresh().expect("FVarId overflow in insert_rc")
    }

    /// Register a variable's type for scalar exclusion.
    fn register_type(&mut self, fvar: FVarId, ty: &Expr) {
        self.type_map.insert(fvar, ty.clone());
    }

    /// Check if a variable should use RC (is a reference type and not borrowed).
    ///
    /// Matches Lean 4's gating logic: `isPossibleRef && !isBorrowed`.
    /// Variables with scalar types (Bool, UIntN, Float, etc.) never need RC.
    fn needs_rc(&self, fvar: FVarId, live: &LiveVars) -> bool {
        // Erased bindings carry no runtime object; RC ops on their
        // null/zero placeholder crash (`clean_inc(NULL)`).
        if self.erased_locals.contains(&fvar) {
            return false;
        }

        // Scalar types never need RC (Lean 4: isPossibleRef gate)
        if let Some(ty) = self.type_map.get(&fvar) {
            if is_scalar_type(ty) {
                return false;
            }
        }

        // Borrowed variables skip RC
        if live.is_borrowed(fvar) {
            return false;
        }

        // Check if this is a borrowed parameter
        for (param_fvar, ownership) in &self.params {
            if *param_fvar == fvar && *ownership == Ownership::Borrowed {
                return false;
            }
        }

        // Check if derived from borrowed
        if let Some(source) = self.derived_from.get(&fvar) {
            if live.is_borrowed(*source) {
                return false;
            }
        }

        true
    }

    /// Whether `fvar` is one of the enclosing declaration's parameters.
    ///
    /// Params take their death `dec` on EVERY return path
    /// ([`insert_rc_return`] decs owned, non-returned params regardless of
    /// earlier uses), so a consuming use of a param must always compensate
    /// with an `inc` — the last-use ownership TRANSFER applies only to
    /// non-param locals, whose ownership has no other sink.
    fn is_param(&self, fvar: FVarId) -> bool {
        self.params.iter().any(|(param, _)| *param == fvar)
    }
}

/// Insert RC operations into a declaration.
pub fn insert_rc(decl: &Decl, borrow_map: &BorrowMap) -> Decl {
    let body = match &decl.body {
        DeclValue::Code(code) => {
            let mut ctx = RCContext::new(borrow_map);

            // Set up parameter ownership and type info from borrow info
            if let Some(fn_borrow) = borrow_map.get(&decl.name) {
                for (idx, param) in decl.params.iter().enumerate() {
                    let ownership = if idx < fn_borrow.params.len() {
                        fn_borrow.params[idx]
                    } else {
                        Ownership::Owned // Default to owned
                    };
                    ctx.params.push((param.fvar_id, ownership));
                    ctx.register_type(param.fvar_id, &param.ty);
                }
            } else {
                // No borrow info, all owned
                for param in &decl.params {
                    ctx.params.push((param.fvar_id, Ownership::Owned));
                    ctx.register_type(param.fvar_id, &param.ty);
                }
            }

            // Initialize live vars with borrowed parameters
            let mut live = LiveVars::new();
            for (fvar, ownership) in &ctx.params {
                if *ownership == Ownership::Borrowed {
                    live.mark_borrowed(*fvar);
                }
            }

            let result = insert_rc_in_code(code, &mut live, &mut ctx);
            DeclValue::Code(Box::new(result))
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

/// Insert RC operations into code (without declaration context).
pub fn insert_rc_in_code_standalone(code: &Code, borrow_map: &BorrowMap) -> Code {
    let mut ctx = RCContext::new(borrow_map);
    let mut live = LiveVars::new();
    insert_rc_in_code(code, &mut live, &mut ctx)
}

/// Insert RC operations into a Code block.
fn insert_rc_in_code(code: &Code, live: &mut LiveVars, ctx: &mut RCContext) -> Code {
    match code {
        Code::Return(fvar) => insert_rc_return(*fvar, live, ctx),
        Code::Let(decl, body) => {
            ctx.register_type(decl.fvar_id, &decl.ty);
            // Register BEFORE the backward walk into the body, so uses of
            // the binding (processed first) already see it as erased.
            if matches!(decl.value, crate::lcnf::LetValue::Erased) {
                ctx.erased_locals.insert(decl.fvar_id);
            }
            let new_body = insert_rc_in_code(body, live, ctx);
            let was_live = live.is_live(decl.fvar_id);
            // Lean 4 ExplicitRC: addDecIfNeeded decl.fvarId k
            // Dec dead let-bound values that are reference types to prevent leaks.
            let new_body = if !was_live && ctx.needs_rc(decl.fvar_id, live) {
                wrap_dec(decl.fvar_id, new_body, ctx)
            } else {
                new_body
            };
            live.mark_dead(decl.fvar_id);
            process_let_value(decl, new_body, was_live, live, ctx)
        }
        Code::Fun(fun_decl, body) => insert_rc_fun(fun_decl, body, live, ctx),
        Code::JoinPoint(jp_decl, body) => insert_rc_join_point(jp_decl, body, live, ctx),
        Code::Cases(cases) => insert_rc_cases(cases, live, ctx),
        Code::Jmp { jp, args } => {
            for arg in args {
                if let Arg::FVar(fvar) = arg {
                    live.mark_live(*fvar);
                }
            }
            Code::Jmp {
                jp: *jp,
                args: args.clone(),
            }
        }
        Code::Unreachable(ty) => Code::Unreachable(ty.clone()),
    }
}

/// Insert RC for return statement: dec owned params not being returned,
/// inc borrowed params that are being returned.
///
/// Lean 4 ExplicitRC.lean line 615: `if isPossibleRef && isBorrowed then addInc`
fn insert_rc_return(fvar: FVarId, live: &mut LiveVars, ctx: &mut RCContext) -> Code {
    live.mark_live(fvar);
    let mut result = Code::Return(fvar);

    // Inc borrowed params being returned. The caller retains ownership of the
    // borrowed reference, but the return value must also be owned.
    let is_borrowed_param = ctx
        .params
        .iter()
        .any(|(p, o)| *p == fvar && *o == Ownership::Borrowed);
    if is_borrowed_param {
        let ty_is_ref = ctx
            .type_map
            .get(&fvar)
            .map(|ty| !is_scalar_type(ty))
            .unwrap_or(true);
        if ty_is_ref {
            result = wrap_inc(fvar, result, ctx);
        }
    }

    let decs: Vec<_> = ctx
        .params
        .iter()
        .filter(|(param_fvar, ownership)| {
            *ownership == Ownership::Owned && *param_fvar != fvar && ctx.needs_rc(*param_fvar, live)
        })
        .map(|(fvar, _)| *fvar)
        .collect();
    for param_fvar in decs {
        result = wrap_dec(param_fvar, result, ctx);
    }
    result
}

/// Insert RC for nested function declaration.
fn insert_rc_fun(
    fun_decl: &FunDecl,
    body: &Code,
    live: &mut LiveVars,
    ctx: &mut RCContext,
) -> Code {
    for param in &fun_decl.params {
        ctx.register_type(param.fvar_id, &param.ty);
    }
    let fun_body = insert_rc_in_code(&fun_decl.body, live, ctx);
    let new_decl = FunDecl {
        fvar_id: fun_decl.fvar_id,
        name: fun_decl.name.clone(),
        params: fun_decl.params.clone(),
        ty: fun_decl.ty.clone(),
        body: Box::new(fun_body),
    };
    Code::Fun(new_decl, Box::new(insert_rc_in_code(body, live, ctx)))
}

/// Insert RC for join point declaration.
fn insert_rc_join_point(
    jp_decl: &FunDecl,
    body: &Code,
    live: &mut LiveVars,
    ctx: &mut RCContext,
) -> Code {
    for param in &jp_decl.params {
        ctx.register_type(param.fvar_id, &param.ty);
    }
    let jp_body = insert_rc_in_code(&jp_decl.body, live, ctx);
    let new_decl = FunDecl {
        fvar_id: jp_decl.fvar_id,
        name: jp_decl.name.clone(),
        params: jp_decl.params.clone(),
        ty: jp_decl.ty.clone(),
        body: Box::new(jp_body),
    };
    Code::JoinPoint(new_decl, Box::new(insert_rc_in_code(body, live, ctx)))
}

/// Insert RC for cases expression: process each branch independently.
fn insert_rc_cases(cases: &Cases, live: &mut LiveVars, ctx: &mut RCContext) -> Code {
    let saved_live = live.clone();
    let mut branch_lives: Vec<HashSet<FVarId>> = Vec::new();
    let new_alts: Vec<Alt> = cases
        .alts
        .iter()
        .map(|alt| {
            let mut branch_live = saved_live.clone();
            let (new_alt, final_live) = process_case_alt(alt, &mut branch_live, ctx);
            branch_lives.push(final_live);
            new_alt
        })
        .collect();
    for branch in &branch_lives {
        live.vars.extend(branch);
    }
    live.mark_live(cases.scrutinee);
    Code::Cases(Cases {
        type_name: cases.type_name.clone(),
        result_type: cases.result_type.clone(),
        scrutinee: cases.scrutinee,
        alts: new_alts,
    })
}

/// Process a case alternative.
fn process_case_alt(alt: &Alt, live: &mut LiveVars, ctx: &mut RCContext) -> (Alt, HashSet<FVarId>) {
    match alt {
        Alt::Ctor {
            ctor_name,
            params,
            body,
        } => {
            // Register case alt pattern variable types for scalar exclusion
            for param in params {
                ctx.register_type(param.fvar_id, &param.ty);
            }
            let new_body = insert_rc_in_code(body, live, ctx);

            // Dec pattern variables that are dead
            // Collect which params need dec before mutating ctx
            let decs: Vec<_> = params
                .iter()
                .filter(|param| !live.is_live(param.fvar_id) && ctx.needs_rc(param.fvar_id, live))
                .map(|param| param.fvar_id)
                .collect();
            let mut final_body = new_body;
            for fvar_id in decs {
                final_body = wrap_dec(fvar_id, final_body, ctx);
            }
            for param in params {
                live.mark_dead(param.fvar_id);
            }

            (
                Alt::Ctor {
                    ctor_name: ctor_name.clone(),
                    params: params.clone(),
                    body: Box::new(final_body),
                },
                live.vars.clone(),
            )
        }
        Alt::Default(body) => {
            let new_body = insert_rc_in_code(body, live, ctx);
            (Alt::Default(Box::new(new_body)), live.vars.clone())
        }
    }
}

#[cfg(test)]
mod tests;
