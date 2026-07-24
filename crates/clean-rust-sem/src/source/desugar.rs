// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Desugaring of syntactic forms into core expression types.
//!
//! `if let` and `while let` are desugared into `match` expressions at parse
//! time so the evaluator only needs to handle the core `Match` and `Loop` forms.

use std::collections::HashSet;

use super::{parser::Parser, SourceError};
use crate::expr::{EnumPatternPayload, EnumVariantPayload, Expr, MatchArm, Pattern, Stmt};
use crate::values::Value;

impl Parser {
    /// Desugar `if let Pat = expr { then } else { else_branch }`
    /// into `match expr { Pat => then, _ => else_branch }`
    pub(super) fn desugar_if_let(
        &mut self,
        let_expr: &syn::ExprLet,
        then_branch: &syn::Block,
        else_branch: &Option<(syn::token::Else, Box<syn::Expr>)>,
    ) -> Result<Expr, SourceError> {
        let pattern = self.parse_pattern(&let_expr.pat)?;
        let scrutinee = self.parse_expr(&let_expr.expr)?;
        let then_body = self.parse_block(then_branch)?;
        let else_body = match else_branch {
            Some((_, expr)) => self.parse_expr(expr)?,
            None => Expr::Literal(Value::Unit),
        };
        Ok(Expr::Match {
            scrutinee: Box::new(scrutinee),
            arms: vec![
                MatchArm {
                    pattern,
                    guard: None,
                    body: then_body,
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: else_body,
                },
            ],
        })
    }

    /// Desugar `while let Pat = expr { body }`
    /// into `loop { match expr { Pat => body, _ => break } }`
    pub(super) fn desugar_while_let(
        &mut self,
        let_expr: &syn::ExprLet,
        body: &syn::Block,
        label: Option<&syn::Label>,
    ) -> Result<Expr, SourceError> {
        let pattern = self.parse_pattern(&let_expr.pat)?;
        let scrutinee = self.parse_expr(&let_expr.expr)?;
        let loop_body = self.parse_block(body)?;
        Ok(Expr::Loop {
            label: label.map(Self::loop_label_name),
            body: Box::new(Expr::Match {
                scrutinee: Box::new(scrutinee),
                arms: vec![
                    MatchArm {
                        pattern,
                        guard: None,
                        body: loop_body,
                    },
                    MatchArm {
                        pattern: Pattern::Wildcard,
                        guard: None,
                        body: Expr::Break {
                            label: None,
                            value: None,
                        },
                    },
                ],
            }),
        })
    }

    /// Desugar `Struct { field: value, ..base }` into a block that preserves
    /// Rust's evaluation order: explicit fields first, then the base expression.
    pub(super) fn desugar_struct_update(
        &mut self,
        struct_expr: &syn::ExprStruct,
    ) -> Result<Expr, SourceError> {
        // Struct update syntax (`..base`) is only valid for structs, never enum
        // variants, so multi-segment paths like `module::Foo { ..base }` resolve
        // through the last segment (structs are registered by simple name).
        let leaf_name = struct_expr
            .path
            .segments
            .last()
            .map(|seg| seg.ident.to_string())
            .unwrap_or_default();
        let Some(struct_name) = self.canonical_named_struct_name(&leaf_name)? else {
            return Err(Self::unsupported(
                "expression",
                format!(
                    "struct update syntax requires a known named struct `{}`",
                    Self::path_to_string(&struct_expr.path)
                ),
            ));
        };
        let known_fields = self
            .struct_field_names(&struct_name)
            .expect("canonical named struct should expose field metadata")
            .to_vec();
        let rest = struct_expr
            .rest
            .as_ref()
            .expect("desugar_struct_update only called when rest is present");

        let mut stmts = Vec::with_capacity(struct_expr.fields.len() + 1);
        let mut explicit_fields = Vec::with_capacity(struct_expr.fields.len());
        let mut explicit_names = HashSet::with_capacity(struct_expr.fields.len());

        for field in &struct_expr.fields {
            let field_name = Self::member_name(&field.member);
            let temp_name = self.fresh_synthetic_local("struct_field");
            stmts.push(Stmt::Let {
                pattern: Pattern::Binding {
                    name: temp_name.clone(),
                    mutable: false,
                    subpattern: None,
                },
                ty: None,
                init: Some(Box::new(self.parse_expr(&field.expr)?)),
                else_block: None,
            });
            explicit_names.insert(field_name.clone());
            explicit_fields.push((
                field_name,
                Expr::Var {
                    name: temp_name,
                    local_idx: 0,
                },
            ));
        }

        let base_name = self.fresh_synthetic_local("struct_base");
        stmts.push(Stmt::Let {
            pattern: Pattern::Binding {
                name: base_name.clone(),
                mutable: false,
                subpattern: None,
            },
            ty: None,
            init: Some(Box::new(self.parse_expr(rest)?)),
            else_block: None,
        });

        let mut fields = explicit_fields;
        for field_name in known_fields {
            if explicit_names.contains(&field_name) {
                continue;
            }
            fields.push((
                field_name.clone(),
                Expr::Field {
                    base: Box::new(Expr::Var {
                        name: base_name.clone(),
                        local_idx: 0,
                    }),
                    field: field_name,
                },
            ));
        }

        Ok(Expr::Block {
            stmts,
            expr: Some(Box::new(Expr::Struct {
                name: struct_name,
                fields,
                type_args: vec![],
                const_args: vec![],
            })),
        })
    }

    /// Desugar `expr?` into a match that handles both `Result` and `Option`.
    ///
    /// Without type inference, we emit match arms for both types:
    /// ```text
    /// match expr {
    ///     Result::Ok(val) => val,
    ///     Result::Err(e) => return Err(e),
    ///     Option::Some(val) => val,
    ///     Option::None => return None,
    /// }
    /// ```
    /// At runtime, only the matching enum type's arms will fire.
    pub(super) fn desugar_try_operator(&mut self, expr: &syn::Expr) -> Result<Expr, SourceError> {
        let scrutinee = self.parse_expr(expr)?;
        let val_name = self.fresh_synthetic_local("try_val");
        let err_name = self.fresh_synthetic_local("try_err");

        let val_binding = |name: &str| Pattern::Binding {
            name: name.to_string(),
            mutable: false,
            subpattern: None,
        };
        let val_ref = |name: &str| Expr::Var {
            name: name.to_string(),
            local_idx: 0,
        };

        Ok(Expr::Match {
            scrutinee: Box::new(scrutinee),
            arms: vec![
                // Result::Ok(val) => val
                MatchArm {
                    pattern: Pattern::EnumVariant {
                        enum_name: "Result".to_string(),
                        variant: "Ok".to_string(),
                        payload: EnumPatternPayload::Tuple(vec![val_binding(&val_name)]),
                    },
                    guard: None,
                    body: val_ref(&val_name),
                },
                // Result::Err(e) => return Err(e)
                MatchArm {
                    pattern: Pattern::EnumVariant {
                        enum_name: "Result".to_string(),
                        variant: "Err".to_string(),
                        payload: EnumPatternPayload::Tuple(vec![val_binding(&err_name)]),
                    },
                    guard: None,
                    body: Expr::Return(Some(Box::new(Expr::EnumVariant {
                        enum_name: "Result".to_string(),
                        variant: "Err".to_string(),
                        payload: EnumVariantPayload::Tuple(vec![val_ref(&err_name)]),
                        type_args: vec![],
                        const_args: vec![],
                    }))),
                },
                // Option::Some(val) => val
                MatchArm {
                    pattern: Pattern::EnumVariant {
                        enum_name: "Option".to_string(),
                        variant: "Some".to_string(),
                        payload: EnumPatternPayload::Tuple(vec![val_binding(&val_name)]),
                    },
                    guard: None,
                    body: val_ref(&val_name),
                },
                // Option::None => return None
                MatchArm {
                    pattern: Pattern::EnumVariant {
                        enum_name: "Option".to_string(),
                        variant: "None".to_string(),
                        payload: EnumPatternPayload::Unit,
                    },
                    guard: None,
                    body: Expr::Return(Some(Box::new(Expr::EnumVariant {
                        enum_name: "Option".to_string(),
                        variant: "None".to_string(),
                        payload: EnumVariantPayload::Unit,
                        type_args: vec![],
                        const_args: vec![],
                    }))),
                },
            ],
        })
    }
}
