// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Macro desugaring for collection and inspection macros (`vec!`, `dbg!`,
//! `matches!`).

use super::super::{parser::Parser, SourceError};
use crate::expr::{Expr, MatchArm, Pattern};
use crate::values::Value;

impl Parser {
    pub(super) fn parse_vec_macro(
        &mut self,
        tokens: &proc_macro2::TokenStream,
    ) -> Result<Expr, SourceError> {
        use syn::parse::{Parse, ParseStream};

        enum VecMacroInput {
            List(syn::punctuated::Punctuated<syn::Expr, syn::Token![,]>),
            Repeat {
                value: Box<syn::Expr>,
                count: Box<syn::Expr>,
            },
        }

        impl Parse for VecMacroInput {
            fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
                if input.is_empty() {
                    return Ok(Self::List(syn::punctuated::Punctuated::new()));
                }

                let first: syn::Expr = input.parse()?;
                if input.peek(syn::Token![;]) {
                    input.parse::<syn::Token![;]>()?;
                    let count: syn::Expr = input.parse()?;
                    if !input.is_empty() {
                        return Err(input.error("unexpected tokens after vec! repeat syntax"));
                    }
                    return Ok(Self::Repeat {
                        value: Box::new(first),
                        count: Box::new(count),
                    });
                }

                let mut elems = syn::punctuated::Punctuated::new();
                elems.push_value(first);
                while input.peek(syn::Token![,]) {
                    let punct = input.parse::<syn::Token![,]>()?;
                    elems.push_punct(punct);
                    if input.is_empty() {
                        break;
                    }
                    elems.push_value(input.parse()?);
                }

                if !input.is_empty() {
                    return Err(input.error("expected `,` between vec! elements"));
                }

                Ok(Self::List(elems))
            }
        }

        match syn::parse2::<VecMacroInput>(tokens.clone()).map_err(SourceError::Parse)? {
            VecMacroInput::List(elems) => Ok(Expr::Array(
                elems
                    .iter()
                    .map(|expr| self.parse_expr(expr))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            VecMacroInput::Repeat { value, count } => Ok(Expr::ArrayRepeat {
                value: Box::new(self.parse_expr(&value)?),
                count: Self::parse_usize_expr(&count)?,
            }),
        }
    }

    pub(super) fn parse_dbg_macro(
        &mut self,
        tokens: &proc_macro2::TokenStream,
    ) -> Result<Expr, SourceError> {
        if tokens.is_empty() {
            return Ok(Expr::Literal(Value::Unit));
        }
        use syn::parse::Parser as SynParser;

        let args = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
            .parse2(tokens.clone())
            .map_err(SourceError::Parse)?;

        if args.len() == 1 {
            return self.parse_expr(args.first().expect("len checked"));
        }

        Ok(Expr::Tuple(
            args.iter()
                .map(|expr| self.parse_expr(expr))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }

    pub(super) fn parse_matches_macro(
        &mut self,
        tokens: &proc_macro2::TokenStream,
    ) -> Result<Expr, SourceError> {
        use syn::parse::{Parse, ParseStream};

        struct MatchesMacroInput {
            expr: syn::Expr,
            pat: syn::Pat,
            guard: Option<syn::Expr>,
        }

        impl Parse for MatchesMacroInput {
            fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
                let expr: syn::Expr = input.parse()?;
                input.parse::<syn::Token![,]>()?;
                let pat = syn::Pat::parse_multi_with_leading_vert(input)?;
                let guard = if input.peek(syn::Token![if]) {
                    input.parse::<syn::Token![if]>()?;
                    Some(input.parse()?)
                } else {
                    None
                };
                if input.peek(syn::Token![,]) {
                    input.parse::<syn::Token![,]>()?;
                }
                if !input.is_empty() {
                    return Err(input.error("unexpected tokens after matches! macro input"));
                }
                Ok(Self { expr, pat, guard })
            }
        }

        let input = syn::parse2::<MatchesMacroInput>(tokens.clone()).map_err(SourceError::Parse)?;
        Ok(Expr::Match {
            scrutinee: Box::new(self.parse_expr(&input.expr)?),
            arms: vec![
                MatchArm {
                    pattern: self.parse_pattern(&input.pat)?,
                    guard: input
                        .guard
                        .as_ref()
                        .map(|guard| self.parse_expr(guard))
                        .transpose()?,
                    body: Expr::Literal(Value::Bool(true)),
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    guard: None,
                    body: Expr::Literal(Value::Bool(false)),
                },
            ],
        })
    }
}
