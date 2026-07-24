// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Argument validation for compile-time environment macros (`env!`,
//! `option_env!`, `include_str!`, `include_bytes!`, `column!`, etc.).

use super::super::{parser::Parser, SourceError};

impl Parser {
    pub(super) fn validate_single_string_literal_macro_arg(
        tokens: &proc_macro2::TokenStream,
        macro_name: &'static str,
    ) -> Result<(), SourceError> {
        use syn::parse::Parser as SynParser;

        let args = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
            .parse2(tokens.clone())
            .map_err(SourceError::Parse)?;
        if args.len() != 1 {
            return Err(Self::unsupported(
                "macro",
                format!("{macro_name}! expects exactly 1 string-literal argument"),
            ));
        }
        match args.first() {
            Some(syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Str(value),
                ..
            })) => {
                let _ = value;
                Ok(())
            }
            Some(other) => Err(Self::unsupported(
                "macro",
                format!(
                    "{macro_name}! expects a string-literal argument, found `{}`",
                    Self::expr_kind(other)
                ),
            )),
            None => unreachable!("length checked above"),
        }
    }

    pub(super) fn validate_env_macro_args(
        tokens: &proc_macro2::TokenStream,
    ) -> Result<(), SourceError> {
        use syn::parse::Parser as SynParser;

        let args = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated
            .parse2(tokens.clone())
            .map_err(SourceError::Parse)?;
        if !(1..=2).contains(&args.len()) {
            return Err(Self::unsupported(
                "macro",
                "env! expects 1 or 2 string-literal arguments",
            ));
        }
        for arg in args.iter() {
            match arg {
                syn::Expr::Lit(syn::ExprLit {
                    lit: syn::Lit::Str(_),
                    ..
                }) => {}
                other => {
                    return Err(Self::unsupported(
                        "macro",
                        format!(
                            "env! expects string-literal arguments, found `{}`",
                            Self::expr_kind(other)
                        ),
                    ));
                }
            }
        }
        Ok(())
    }

    pub(super) fn validate_zero_arg_macro(
        tokens: &proc_macro2::TokenStream,
        macro_name: &str,
    ) -> Result<(), SourceError> {
        if tokens.is_empty() {
            return Ok(());
        }
        Err(Self::unsupported(
            "macro",
            format!("{macro_name}! expects no arguments"),
        ))
    }
}
