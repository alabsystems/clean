// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::{parser::Parser, SourceError};
use crate::expr::{AsmOperand, AsmOptions, Expr, InlineAsm, Item};
use proc_macro2::TokenStream;
use syn::parse::{Parse, ParseStream};
use syn::{parenthesized, punctuated::Punctuated, Ident, LitStr, Token};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AsmMacroKind {
    Inline,
    Global,
}

enum RawAsmArg {
    Operand(RawAsmOperand),
    Options(Vec<String>),
    ClobberAbi(Vec<String>),
}

enum RawAsmOperand {
    In {
        constraint: String,
        expr: syn::Expr,
    },
    Out {
        constraint: String,
        expr: Option<syn::Expr>,
    },
    InOut {
        constraint: String,
        in_expr: syn::Expr,
        out_expr: Option<syn::Expr>,
    },
    Const(syn::Expr),
    Sym(syn::Path),
}

struct RawInlineAsm {
    template_segments: Vec<String>,
    args: Vec<RawAsmArg>,
}

impl Parse for RawInlineAsm {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let mut template_segments = Vec::new();
        while input.peek(LitStr) {
            template_segments.push(input.parse::<LitStr>()?.value());
            if input.is_empty() || !input.peek(Token![,]) {
                break;
            }
            let fork = input.fork();
            fork.parse::<Token![,]>()?;
            if !fork.peek(LitStr) {
                break;
            }
            input.parse::<Token![,]>()?;
        }

        if template_segments.is_empty() {
            return Err(input.error("asm! requires at least one string template"));
        }

        let mut args = Vec::new();
        while !input.is_empty() {
            input.parse::<Token![,]>()?;
            if input.is_empty() {
                break;
            }
            args.push(input.parse::<RawAsmArg>()?);
        }

        Ok(Self {
            template_segments,
            args,
        })
    }
}

impl Parse for RawAsmArg {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        if Self::parse_named_operand_prefix(input)? {
            // Prefix already consumed; actual operand parsing continues below.
        }

        if input.peek(Token![in]) {
            input.parse::<Token![in]>()?;
            let constraint = parse_constraint(input)?;
            let expr = input.parse::<syn::Expr>()?;
            return Ok(Self::Operand(RawAsmOperand::In { constraint, expr }));
        }

        if input.peek(Token![const]) {
            input.parse::<Token![const]>()?;
            let expr = input.parse::<syn::Expr>()?;
            return Ok(Self::Operand(RawAsmOperand::Const(expr)));
        }

        let ident = input.parse::<Ident>()?;
        match ident.to_string().as_str() {
            "out" | "lateout" => {
                let constraint = parse_constraint(input)?;
                let expr = parse_optional_output_expr(input)?;
                Ok(Self::Operand(RawAsmOperand::Out { constraint, expr }))
            }
            "inout" | "inlateout" => {
                let constraint = parse_constraint(input)?;
                let in_expr = input.parse::<syn::Expr>()?;
                let out_expr = if input.peek(Token![=>]) {
                    input.parse::<Token![=>]>()?;
                    parse_optional_output_expr(input)?
                } else {
                    Some(in_expr.clone())
                };
                Ok(Self::Operand(RawAsmOperand::InOut {
                    constraint,
                    in_expr,
                    out_expr,
                }))
            }
            "sym" => {
                let path = input.parse::<syn::Path>()?;
                Ok(Self::Operand(RawAsmOperand::Sym(path)))
            }
            "options" => {
                let content;
                parenthesized!(content in input);
                let options = Punctuated::<Ident, Token![,]>::parse_terminated(&content)?
                    .into_iter()
                    .map(|ident| ident.to_string())
                    .collect();
                Ok(Self::Options(options))
            }
            "clobber_abi" => {
                let content;
                parenthesized!(content in input);
                let clobbers = Punctuated::<LitStr, Token![,]>::parse_terminated(&content)?
                    .into_iter()
                    .map(|lit| lit.value())
                    .collect();
                Ok(Self::ClobberAbi(clobbers))
            }
            other => Err(input.error(format!("unsupported asm operand kind `{other}`"))),
        }
    }
}

impl RawAsmArg {
    fn parse_named_operand_prefix(input: ParseStream<'_>) -> syn::Result<bool> {
        if !input.peek(Ident) {
            return Ok(false);
        }
        let fork = input.fork();
        let _name = fork.parse::<Ident>()?;
        if !fork.peek(Token![=]) {
            return Ok(false);
        }
        input.parse::<Ident>()?;
        input.parse::<Token![=]>()?;
        Ok(true)
    }
}

fn parse_constraint(input: ParseStream<'_>) -> syn::Result<String> {
    let content;
    parenthesized!(content in input);
    let constraint = content.parse::<TokenStream>()?;
    Ok(constraint.to_string())
}

fn parse_optional_output_expr(input: ParseStream<'_>) -> syn::Result<Option<syn::Expr>> {
    if input.peek(Token![_]) {
        input.parse::<Token![_]>()?;
        Ok(None)
    } else {
        input.parse::<syn::Expr>().map(Some)
    }
}

impl Parser {
    pub(super) fn parse_inline_asm_macro(
        &mut self,
        tokens: &TokenStream,
    ) -> Result<Expr, SourceError> {
        let asm = self.parse_asm_tokens(tokens, AsmMacroKind::Inline)?;
        Ok(Expr::InlineAsm(asm))
    }

    pub(in crate::source) fn parse_global_asm_item(
        &mut self,
        mac: &syn::Macro,
    ) -> Result<Item, SourceError> {
        let asm = self.parse_asm_tokens(&mac.tokens, AsmMacroKind::Global)?;
        Ok(Item::GlobalAsm(asm))
    }

    fn parse_asm_tokens(
        &mut self,
        tokens: &TokenStream,
        kind: AsmMacroKind,
    ) -> Result<InlineAsm, SourceError> {
        let raw = syn::parse2::<RawInlineAsm>(tokens.clone()).map_err(SourceError::Parse)?;
        let mut operands = Vec::new();
        let mut options = AsmOptions::default();
        let mut clobbers = Vec::new();

        for arg in raw.args {
            match arg {
                RawAsmArg::Operand(raw_operand) => {
                    operands.push(self.lower_asm_operand(raw_operand, kind)?)
                }
                RawAsmArg::Options(names) => {
                    for name in names {
                        match name.as_str() {
                            "pure" => options.pure = true,
                            "nomem" => options.nomem = true,
                            "readonly" => options.readonly = true,
                            "preserves_flags" => options.preserves_flags = true,
                            "nostack" => options.nostack = true,
                            "noreturn" => options.noreturn = true,
                            "att_syntax" => options.att_syntax = true,
                            "raw" => options.raw = true,
                            "may_unwind" => options.may_unwind = true,
                            _ => {
                                return Err(SourceError::Unsupported {
                                    context: "asm option",
                                    detail: format!("unsupported asm option `{name}`"),
                                })
                            }
                        }
                    }
                }
                RawAsmArg::ClobberAbi(names) => clobbers.extend(names),
            }
        }

        Ok(InlineAsm {
            template: raw.template_segments.join("\n"),
            operands,
            options,
            clobbers,
        })
    }

    fn lower_asm_operand(
        &mut self,
        operand: RawAsmOperand,
        kind: AsmMacroKind,
    ) -> Result<AsmOperand, SourceError> {
        match operand {
            RawAsmOperand::In { .. } | RawAsmOperand::Out { .. } | RawAsmOperand::InOut { .. }
                if kind == AsmMacroKind::Global =>
            {
                Err(SourceError::Unsupported {
                    context: "global_asm operand",
                    detail: "global_asm! only supports `const` and `sym` operands".to_string(),
                })
            }
            RawAsmOperand::In { constraint, expr } => Ok(AsmOperand::In {
                constraint,
                expr: self.parse_expr(&expr)?,
            }),
            RawAsmOperand::Out { constraint, expr } => Ok(AsmOperand::Out {
                constraint,
                expr: expr
                    .as_ref()
                    .map(|expr| self.parse_expr(expr))
                    .transpose()?,
            }),
            RawAsmOperand::InOut {
                constraint,
                in_expr,
                out_expr,
            } => Ok(AsmOperand::InOut {
                constraint,
                in_expr: self.parse_expr(&in_expr)?,
                out_expr: out_expr
                    .as_ref()
                    .map(|expr| self.parse_expr(expr))
                    .transpose()?,
            }),
            RawAsmOperand::Const(expr) => Ok(AsmOperand::Const(self.parse_expr(&expr)?)),
            RawAsmOperand::Sym(path) => Ok(AsmOperand::Sym(Self::path_to_string(&path))),
        }
    }
}
