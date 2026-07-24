// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Trait default body substitution for the Rust interpreter.
//!
//! When a concrete type uses a trait's default method body, all occurrences of
//! `<Self as TraitName>::method` must be rewritten to `<ConcreteType as TraitName>::method`.
//! This module implements recursive AST rewriting for expressions, statements, and items
//! to perform that substitution.

use super::Interpreter;
use crate::expr::{AsmOperand, EnumVariantPayload, Expr, MatchArm, Stmt};
use crate::types::RustType;

impl Interpreter {
    pub(super) fn trait_impl_function_name(
        type_name: &str,
        trait_name: &str,
        method_name: &str,
    ) -> String {
        format!("<{type_name} as {trait_name}>::{method_name}")
    }

    pub(super) fn substitute_trait_default_body_name(
        name: &str,
        concrete_self_ty: &RustType,
        trait_name: &str,
    ) -> String {
        let prefix = format!("<Self as {trait_name}>::");
        let Some(item_name) = name.strip_prefix(&prefix) else {
            return name.to_string();
        };
        let self_name = concrete_self_ty
            .name()
            .unwrap_or_else(|| "anonymous".to_string());
        format!("<{self_name} as {trait_name}>::{item_name}")
    }

    pub(super) fn substitute_trait_default_body_expr(
        expr: &Expr,
        concrete_self_ty: &RustType,
        trait_name: &str,
    ) -> Expr {
        // Short aliases to reduce per-arm verbosity.
        let rec =
            |e: &Expr| Self::substitute_trait_default_body_expr(e, concrete_self_ty, trait_name);
        let rec_box = |e: &Expr| Box::new(rec(e));
        let rec_opt = |o: &Option<Box<Expr>>| o.as_ref().map(|e| rec_box(e));
        let rec_vec = |v: &[Expr]| v.iter().map(&rec).collect();

        match expr {
            Expr::Literal(value) => Expr::Literal(value.clone()),
            Expr::Var { name, local_idx } => Expr::Var {
                name: Self::substitute_trait_default_body_name(name, concrete_self_ty, trait_name),
                local_idx: *local_idx,
            },
            Expr::Field { base, field } => Expr::Field {
                base: rec_box(base),
                field: field.clone(),
            },
            Expr::Index { base, index } => Expr::Index {
                base: rec_box(base),
                index: rec_box(index),
            },
            Expr::Deref(inner) => Expr::Deref(rec_box(inner)),
            Expr::AddrOf { mutability, expr } => Expr::AddrOf {
                mutability: *mutability,
                expr: rec_box(expr),
            },
            Expr::BinOp { op, left, right } => Expr::BinOp {
                op: *op,
                left: rec_box(left),
                right: rec_box(right),
            },
            Expr::UnOp { op, expr } => Expr::UnOp {
                op: *op,
                expr: rec_box(expr),
            },
            Expr::Cast { expr, target } => Expr::Cast {
                expr: rec_box(expr),
                target: target.clone(),
            },
            Expr::Call {
                func,
                args,
                type_args,
            } => Expr::Call {
                func: rec_box(func),
                args: rec_vec(args),
                type_args: type_args.clone(),
            },
            Expr::MethodCall {
                receiver,
                method,
                args,
                type_args,
            } => Expr::MethodCall {
                receiver: rec_box(receiver),
                method: method.clone(),
                args: rec_vec(args),
                type_args: type_args.clone(),
            },
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => Expr::If {
                condition: rec_box(condition),
                then_branch: rec_box(then_branch),
                else_branch: rec_opt(else_branch),
            },
            Expr::Match { scrutinee, arms } => Expr::Match {
                scrutinee: rec_box(scrutinee),
                arms: arms
                    .iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern.clone(),
                        guard: arm.guard.as_ref().map(&rec),
                        body: rec(&arm.body),
                    })
                    .collect(),
            },
            Expr::Block { stmts, expr } => Expr::Block {
                stmts: stmts
                    .iter()
                    .map(|s| {
                        Self::substitute_trait_default_body_stmt(s, concrete_self_ty, trait_name)
                    })
                    .collect(),
                expr: rec_opt(expr),
            },
            Expr::Tuple(elems) => Expr::Tuple(rec_vec(elems)),
            Expr::Array(elems) => Expr::Array(rec_vec(elems)),
            Expr::ArrayRepeat { value, count } => Expr::ArrayRepeat {
                value: rec_box(value),
                count: *count,
            },
            Expr::Struct {
                name,
                fields,
                type_args,
                const_args,
            } => Expr::Struct {
                name: name.clone(),
                fields: fields.iter().map(|(n, v)| (n.clone(), rec(v))).collect(),
                type_args: type_args.clone(),
                const_args: const_args.clone(),
            },
            Expr::UnionInit { name, field } => Expr::UnionInit {
                name: name.clone(),
                field: (field.0.clone(), rec_box(&field.1)),
            },
            Expr::UnionFieldAccess { union_expr, field } => Expr::UnionFieldAccess {
                union_expr: rec_box(union_expr),
                field: field.clone(),
            },
            Expr::EnumVariant {
                enum_name,
                variant,
                payload,
                type_args,
                const_args,
            } => Expr::EnumVariant {
                enum_name: enum_name.clone(),
                variant: variant.clone(),
                type_args: type_args.clone(),
                const_args: const_args.clone(),
                payload: match payload {
                    EnumVariantPayload::Unit => EnumVariantPayload::Unit,
                    EnumVariantPayload::Tuple(values) => EnumVariantPayload::Tuple(rec_vec(values)),
                    EnumVariantPayload::Struct(fields) => EnumVariantPayload::Struct(
                        fields.iter().map(|(n, v)| (n.clone(), rec(v))).collect(),
                    ),
                },
            },
            Expr::Closure {
                params,
                body,
                captures,
                capture_by_value,
            } => Expr::Closure {
                params: params.clone(),
                body: rec_box(body),
                captures: captures.clone(),
                capture_by_value: *capture_by_value,
            },
            Expr::Range {
                start,
                end,
                inclusive,
            } => Expr::Range {
                start: rec_opt(start),
                end: rec_opt(end),
                inclusive: *inclusive,
            },
            Expr::Return(expr) => Expr::Return(rec_opt(expr)),
            Expr::Break { label, value } => Expr::Break {
                label: label.clone(),
                value: rec_opt(value),
            },
            Expr::Continue { label } => Expr::Continue {
                label: label.clone(),
            },
            Expr::Loop { label, body } => Expr::Loop {
                label: label.clone(),
                body: rec_box(body),
            },
            Expr::While {
                label,
                condition,
                body,
            } => Expr::While {
                label: label.clone(),
                condition: rec_box(condition),
                body: rec_box(body),
            },
            Expr::For {
                label,
                pattern,
                iter,
                body,
            } => Expr::For {
                label: label.clone(),
                pattern: pattern.clone(),
                iter: rec_box(iter),
                body: rec_box(body),
            },
            Expr::Unsafe { block } => Expr::Unsafe {
                block: rec_box(block),
            },
            Expr::RawDeref(expr) => Expr::RawDeref(rec_box(expr)),
            Expr::Assign { target, value } => Expr::Assign {
                target: rec_box(target),
                value: rec_box(value),
            },
            Expr::AssignOp { op, target, value } => Expr::AssignOp {
                op: *op,
                target: rec_box(target),
                value: rec_box(value),
            },
            Expr::Panic { message } => Expr::Panic {
                message: rec_box(message),
            },
            Expr::Await { base } => Expr::Await {
                base: rec_box(base),
            },
            Expr::Async {
                capture_by_value,
                body,
            } => Expr::Async {
                capture_by_value: *capture_by_value,
                body: rec_box(body),
            },
            Expr::InlineAsm(asm) => Expr::InlineAsm(crate::expr::InlineAsm {
                template: asm.template.clone(),
                operands: asm
                    .operands
                    .iter()
                    .map(|operand| match operand {
                        AsmOperand::In { constraint, expr } => AsmOperand::In {
                            constraint: constraint.clone(),
                            expr: rec(expr),
                        },
                        AsmOperand::Out { constraint, expr } => AsmOperand::Out {
                            constraint: constraint.clone(),
                            expr: expr.as_ref().map(&rec),
                        },
                        AsmOperand::InOut {
                            constraint,
                            in_expr,
                            out_expr,
                        } => AsmOperand::InOut {
                            constraint: constraint.clone(),
                            in_expr: rec(in_expr),
                            out_expr: out_expr.as_ref().map(&rec),
                        },
                        AsmOperand::Const(expr) => AsmOperand::Const(rec(expr)),
                        AsmOperand::Sym(symbol) => {
                            AsmOperand::Sym(Self::substitute_trait_default_body_name(
                                symbol,
                                concrete_self_ty,
                                trait_name,
                            ))
                        }
                    })
                    .collect(),
                options: asm.options.clone(),
                clobbers: asm.clobbers.clone(),
            }),
        }
    }

    pub(super) fn substitute_trait_default_body_stmt(
        stmt: &Stmt,
        concrete_self_ty: &RustType,
        trait_name: &str,
    ) -> Stmt {
        let rec =
            |e: &Expr| Self::substitute_trait_default_body_expr(e, concrete_self_ty, trait_name);
        let rec_opt = |o: &Option<Box<Expr>>| o.as_ref().map(|e| Box::new(rec(e)));
        match stmt {
            Stmt::Let {
                pattern,
                ty,
                init,
                else_block,
            } => Stmt::Let {
                pattern: pattern.clone(),
                ty: ty.clone(),
                init: rec_opt(init),
                else_block: rec_opt(else_block),
            },
            Stmt::Expr(expr) => Stmt::Expr(rec(expr)),
            Stmt::Item(item) => Stmt::Item(Self::substitute_trait_default_body_item(
                item,
                concrete_self_ty,
                trait_name,
            )),
        }
    }
}
