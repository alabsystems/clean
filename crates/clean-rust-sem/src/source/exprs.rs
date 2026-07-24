// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::parser::Parser;
use super::SourceError;
use crate::expr::{EnumVariantPayload, Expr, MatchArm};
use crate::types::Mutability;

impl Parser {
    pub(super) fn parse_expr(&mut self, expr: &syn::Expr) -> Result<Expr, SourceError> {
        match expr {
            syn::Expr::Lit(_) => Ok(Expr::Literal(self.parse_lit_expr(expr)?)),
            syn::Expr::Path(path) => {
                self.validate_expr_path_generics(&path.path, "path expression")?;
                if path.qself.is_some() {
                    return self.parse_qself_path_expr(path);
                }
                if path.path.segments.len() > 1 {
                    return self.parse_path_expr(path);
                }
                let ident = path
                    .path
                    .segments
                    .last()
                    .ok_or_else(|| SourceError::Invalid {
                        context: "path expression",
                        detail: "missing path segment".to_string(),
                    })?
                    .ident
                    .to_string();
                Ok(Expr::Var {
                    name: ident,
                    local_idx: 0,
                })
            }
            syn::Expr::Paren(paren) => self.parse_expr(&paren.expr),
            syn::Expr::Group(group) => self.parse_expr(&group.expr),
            syn::Expr::Binary(binary) => self.parse_binary_expr(binary),
            syn::Expr::Unary(unary) => self.parse_unary(unary),
            syn::Expr::Cast(cast) => Ok(Expr::Cast {
                expr: Box::new(self.parse_expr(&cast.expr)?),
                target: self.parse_type(&cast.ty)?,
            }),
            syn::Expr::Call(call) => {
                if let syn::Expr::Path(path) = &*call.func {
                    return self.parse_path_call_expr(call, path);
                }
                Ok(Expr::Call {
                    func: Box::new(self.parse_expr(&call.func)?),
                    args: call
                        .args
                        .iter()
                        .map(|arg| self.parse_expr(arg))
                        .collect::<Result<Vec<_>, _>>()?,
                    type_args: vec![],
                })
            }
            syn::Expr::MethodCall(method) => {
                let method_name = method.method.to_string();
                let type_args =
                    self.parse_method_turbofish_type_args(method.turbofish.as_ref(), &method_name)?;
                Ok(Expr::MethodCall {
                    receiver: Box::new(self.parse_expr(&method.receiver)?),
                    method: method_name,
                    args: method
                        .args
                        .iter()
                        .map(|arg| self.parse_expr(arg))
                        .collect::<Result<Vec<_>, _>>()?,
                    type_args,
                })
            }
            syn::Expr::If(if_expr) => {
                // if let Pattern = expr { then } else { else }
                // desugars to: match expr { Pattern => then, _ => else }
                if let syn::Expr::Let(let_expr) = &*if_expr.cond {
                    return self.desugar_if_let(
                        let_expr,
                        &if_expr.then_branch,
                        &if_expr.else_branch,
                    );
                }
                Ok(Expr::If {
                    condition: Box::new(self.parse_expr(&if_expr.cond)?),
                    then_branch: Box::new(self.parse_block(&if_expr.then_branch)?),
                    else_branch: if_expr
                        .else_branch
                        .as_ref()
                        .map(|(_, expr)| self.parse_expr(expr).map(Box::new))
                        .transpose()?,
                })
            }
            syn::Expr::Match(match_expr) => Ok(Expr::Match {
                scrutinee: Box::new(self.parse_expr(&match_expr.expr)?),
                arms: match_expr
                    .arms
                    .iter()
                    .map(|arm| {
                        Ok(MatchArm {
                            pattern: self.parse_pattern(&arm.pat)?,
                            guard: arm
                                .guard
                                .as_ref()
                                .map(|(_, expr)| self.parse_expr(expr))
                                .transpose()?,
                            body: self.parse_expr(&arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, SourceError>>()?,
            }),
            syn::Expr::Const(expr_const) => self.parse_block(&expr_const.block),
            syn::Expr::Block(block) => self.parse_block(&block.block),
            syn::Expr::Tuple(tuple) => Ok(Expr::Tuple(
                tuple
                    .elems
                    .iter()
                    .map(|expr| self.parse_expr(expr))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            syn::Expr::Array(array) => Ok(Expr::Array(
                array
                    .elems
                    .iter()
                    .map(|expr| self.parse_expr(expr))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            syn::Expr::Repeat(repeat) => Ok(Expr::ArrayRepeat {
                value: Box::new(self.parse_expr(&repeat.expr)?),
                count: Self::parse_usize_expr(&repeat.len)?,
            }),
            syn::Expr::Struct(struct_expr) => self.parse_struct_expr(struct_expr),
            syn::Expr::Field(field) => Ok(Expr::Field {
                base: Box::new(self.parse_expr(&field.base)?),
                field: Self::member_name(&field.member),
            }),
            syn::Expr::Index(index) => Ok(Expr::Index {
                base: Box::new(self.parse_expr(&index.expr)?),
                index: Box::new(self.parse_expr(&index.index)?),
            }),
            syn::Expr::Reference(reference) => Ok(Expr::AddrOf {
                mutability: if reference.mutability.is_some() {
                    Mutability::Mutable
                } else {
                    Mutability::Shared
                },
                expr: Box::new(self.parse_expr(&reference.expr)?),
            }),
            syn::Expr::Return(ret) => Ok(Expr::Return(
                ret.expr
                    .as_ref()
                    .map(|expr| self.parse_expr(expr).map(Box::new))
                    .transpose()?,
            )),
            syn::Expr::Break(brk) => Ok(Expr::Break {
                label: brk.label.as_ref().map(Self::branch_label_name),
                value: brk
                    .expr
                    .as_ref()
                    .map(|expr| self.parse_expr(expr).map(Box::new))
                    .transpose()?,
            }),
            syn::Expr::Continue(cont) => Ok(Expr::Continue {
                label: cont.label.as_ref().map(Self::branch_label_name),
            }),
            syn::Expr::Loop(loop_expr) => Ok(Expr::Loop {
                label: loop_expr.label.as_ref().map(Self::loop_label_name),
                body: Box::new(self.parse_block(&loop_expr.body)?),
            }),
            syn::Expr::While(while_expr) => {
                // while let Pattern = expr { body }
                // desugars to: loop { match expr { Pattern => body, _ => break } }
                if let syn::Expr::Let(let_expr) = &*while_expr.cond {
                    return self.desugar_while_let(
                        let_expr,
                        &while_expr.body,
                        while_expr.label.as_ref(),
                    );
                }
                Ok(Expr::While {
                    label: while_expr.label.as_ref().map(Self::loop_label_name),
                    condition: Box::new(self.parse_expr(&while_expr.cond)?),
                    body: Box::new(self.parse_block(&while_expr.body)?),
                })
            }
            syn::Expr::ForLoop(for_loop) => Ok(Expr::For {
                label: for_loop.label.as_ref().map(Self::loop_label_name),
                pattern: Box::new(self.parse_pattern(&for_loop.pat)?),
                iter: Box::new(self.parse_expr(&for_loop.expr)?),
                body: Box::new(self.parse_block(&for_loop.body)?),
            }),
            syn::Expr::Unsafe(unsafe_expr) => Ok(Expr::Unsafe {
                block: Box::new(self.parse_block(&unsafe_expr.block)?),
            }),
            syn::Expr::Range(range) => Ok(Expr::Range {
                start: range
                    .start
                    .as_ref()
                    .map(|expr| self.parse_expr(expr).map(Box::new))
                    .transpose()?,
                end: range
                    .end
                    .as_ref()
                    .map(|expr| self.parse_expr(expr).map(Box::new))
                    .transpose()?,
                inclusive: matches!(range.limits, syn::RangeLimits::Closed(_)),
            }),
            syn::Expr::Macro(mac) => self.parse_macro_expr(mac),
            syn::Expr::Closure(closure) => self.parse_closure(closure),
            syn::Expr::Assign(assign) => Ok(Expr::Assign {
                target: Box::new(self.parse_expr(&assign.left)?),
                value: Box::new(self.parse_expr(&assign.right)?),
            }),
            syn::Expr::Try(try_expr) => self.desugar_try_operator(&try_expr.expr),
            syn::Expr::Async(async_expr) => Ok(Expr::Async {
                capture_by_value: async_expr.capture.is_some(),
                body: Box::new(self.parse_block(&async_expr.block)?),
            }),
            syn::Expr::Await(await_expr) => Ok(Expr::Await {
                base: Box::new(self.parse_expr(&await_expr.base)?),
            }),
            other => Err(Self::unsupported(
                "expression",
                format!("unsupported expression `{}`", Self::expr_kind(other)),
            )),
        }
    }

    fn parse_struct_expr(&mut self, struct_expr: &syn::ExprStruct) -> Result<Expr, SourceError> {
        self.validate_expr_path_generics(&struct_expr.path, "struct expression")?;
        if struct_expr.rest.is_some() {
            return self.desugar_struct_update(struct_expr);
        }
        let (type_args, const_args) = if struct_expr.path.segments.len() > 1 {
            self.parse_variant_path_generic_args(&struct_expr.path, "struct expression")?
        } else {
            self.parse_nominal_path_generic_args(&struct_expr.path, "struct expression")?
        };
        let fields = struct_expr
            .fields
            .iter()
            .map(|field| {
                Ok((
                    Self::member_name(&field.member),
                    self.parse_expr(&field.expr)?,
                ))
            })
            .collect::<Result<Vec<_>, SourceError>>()?;
        if struct_expr.path.segments.len() > 1 {
            let (enum_name, variant) =
                self.split_known_enum_path(&struct_expr.path, "struct expression")?;
            Ok(Expr::EnumVariant {
                enum_name,
                variant,
                payload: EnumVariantPayload::Struct(fields),
                type_args,
                const_args,
            })
        } else {
            let name = Self::path_to_string(&struct_expr.path);
            let canonical_name = if struct_expr.path.segments.len() == 1 {
                self.canonical_named_struct_name(&name)?
                    .unwrap_or_else(|| name.clone())
            } else {
                name.clone()
            };
            if self.is_known_union(&canonical_name) {
                if fields.len() != 1 {
                    return Err(SourceError::Invalid {
                        context: "union init",
                        detail: format!(
                            "union `{canonical_name}` must be initialized with exactly 1 field, got {}",
                            fields.len()
                        ),
                    });
                }
                let field = fields.into_iter().next().expect("len checked");
                Ok(Expr::UnionInit {
                    name: canonical_name,
                    field: (field.0, Box::new(field.1)),
                })
            } else {
                Ok(Expr::Struct {
                    name: canonical_name,
                    fields,
                    type_args,
                    const_args,
                })
            }
        }
    }
}
