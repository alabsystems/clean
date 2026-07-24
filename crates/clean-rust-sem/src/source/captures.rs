// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Closure capture analysis for source ingestion.
//!
//! Collects variable names referenced in an expression tree to compute
//! the set of captured variables for closures. This is an over-approximation:
//! names from `Expr::Var` are collected without subtracting locally-bound
//! variables. The interpreter handles spurious captures gracefully (lookups
//! that fail are silently skipped).

use std::collections::HashSet;

use crate::expr::{EnumVariantPayload, Expr, MatchArm, Stmt};

pub(super) fn collect_expr_var_names(expr: &Expr, names: &mut HashSet<String>) {
    match expr {
        Expr::Var { name, .. } => {
            names.insert(name.clone());
        }
        Expr::Literal(_) | Expr::Continue { .. } => {}
        // Single sub-expression (combined via renaming to `sub`)
        Expr::UnOp { expr: sub, .. }
        | Expr::Cast { expr: sub, .. }
        | Expr::Deref(sub)
        | Expr::RawDeref(sub)
        | Expr::AddrOf { expr: sub, .. }
        | Expr::Field { base: sub, .. }
        | Expr::ArrayRepeat { value: sub, .. }
        | Expr::UnionFieldAccess {
            union_expr: sub, ..
        }
        | Expr::Closure { body: sub, .. }
        | Expr::Panic { message: sub }
        | Expr::Loop { body: sub, .. }
        | Expr::Unsafe { block: sub }
        | Expr::Await { base: sub }
        | Expr::Async { body: sub, .. } => collect_expr_var_names(sub, names),
        // Two sub-expressions (combined via renaming to `a`, `b`)
        Expr::BinOp {
            left: a, right: b, ..
        }
        | Expr::Assign {
            target: a,
            value: b,
        }
        | Expr::AssignOp {
            target: a,
            value: b,
            ..
        }
        | Expr::Index { base: a, index: b }
        | Expr::While {
            condition: a,
            body: b,
            ..
        }
        | Expr::For {
            iter: a, body: b, ..
        } => {
            collect_expr_var_names(a, names);
            collect_expr_var_names(b, names);
        }
        // Optional sub-expression
        Expr::Return(opt) | Expr::Break { value: opt, .. } => collect_opt_expr(opt, names),
        Expr::Range { start, end, .. } => {
            collect_opt_expr(start, names);
            collect_opt_expr(end, names);
        }
        // Expr + args slice
        Expr::Call { func: e, args, .. }
        | Expr::MethodCall {
            receiver: e, args, ..
        } => {
            collect_expr_var_names(e, names);
            collect_expr_slice(args, names);
        }
        Expr::Tuple(elems) | Expr::Array(elems) => collect_expr_slice(elems, names),
        // Compound
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_expr_var_names(condition, names);
            collect_expr_var_names(then_branch, names);
            collect_opt_expr(else_branch, names);
        }
        Expr::Match { scrutinee, arms } => {
            collect_expr_var_names(scrutinee, names);
            collect_match_arms(arms, names);
        }
        Expr::Block { stmts, expr } => {
            collect_stmts_var_names(stmts, names);
            collect_opt_expr(expr, names);
        }
        Expr::Struct { fields, .. } => collect_named_fields(fields, names),
        Expr::UnionInit { field: (_, e), .. } => collect_expr_var_names(e, names),
        Expr::EnumVariant { payload, .. } => collect_payload_var_names(payload, names),
        Expr::InlineAsm(asm) => {
            for operand in &asm.operands {
                match operand {
                    crate::expr::AsmOperand::In { expr, .. } => {
                        collect_expr_var_names(expr, names);
                    }
                    crate::expr::AsmOperand::Out { expr, .. } => {
                        if let Some(e) = expr {
                            collect_expr_var_names(e, names);
                        }
                    }
                    crate::expr::AsmOperand::InOut {
                        in_expr, out_expr, ..
                    } => {
                        collect_expr_var_names(in_expr, names);
                        if let Some(e) = out_expr {
                            collect_expr_var_names(e, names);
                        }
                    }
                    crate::expr::AsmOperand::Const(_) | crate::expr::AsmOperand::Sym(_) => {}
                }
            }
        }
    }
}

fn collect_opt_expr(opt: &Option<Box<Expr>>, names: &mut HashSet<String>) {
    if let Some(e) = opt {
        collect_expr_var_names(e, names);
    }
}

fn collect_expr_slice(exprs: &[Expr], names: &mut HashSet<String>) {
    for e in exprs {
        collect_expr_var_names(e, names);
    }
}

fn collect_named_fields(fields: &[(String, Expr)], names: &mut HashSet<String>) {
    for (_, e) in fields {
        collect_expr_var_names(e, names);
    }
}

fn collect_stmts_var_names(stmts: &[Stmt], names: &mut HashSet<String>) {
    for stmt in stmts {
        match stmt {
            Stmt::Let {
                init, else_block, ..
            } => {
                collect_opt_expr(init, names);
                collect_opt_expr(else_block, names);
            }
            Stmt::Expr(e) => collect_expr_var_names(e, names),
            Stmt::Item(_) => {}
        }
    }
}

fn collect_match_arms(arms: &[MatchArm], names: &mut HashSet<String>) {
    for arm in arms {
        if let Some(guard) = &arm.guard {
            collect_expr_var_names(guard, names);
        }
        collect_expr_var_names(&arm.body, names);
    }
}

fn collect_payload_var_names(payload: &EnumVariantPayload, names: &mut HashSet<String>) {
    match payload {
        EnumVariantPayload::Unit => {}
        EnumVariantPayload::Tuple(exprs) => collect_expr_slice(exprs, names),
        EnumVariantPayload::Struct(fields) => collect_named_fields(fields, names),
    }
}
