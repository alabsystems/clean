// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::SourceError;
use super::Parser;
use crate::types::{ConstGenericArg, RustType};

impl Parser {
    pub(crate) fn validate_expr_path_generics(
        &mut self,
        path: &syn::Path,
        context: &'static str,
    ) -> Result<(), SourceError> {
        let target = format!("path `{}`", Self::path_to_string(path));
        for segment in &path.segments {
            self.validate_expr_path_arguments(&segment.arguments, context, &target)?;
        }
        Ok(())
    }

    pub(crate) fn parse_path_call_type_args(
        &mut self,
        path: &syn::Path,
        context: &'static str,
    ) -> Result<Vec<RustType>, SourceError> {
        self.parse_nominal_path_type_args(path, context)
    }

    pub(crate) fn parse_nominal_path_type_args(
        &mut self,
        path: &syn::Path,
        context: &'static str,
    ) -> Result<Vec<RustType>, SourceError> {
        self.parse_path_type_args_at(path, context, path.segments.len().saturating_sub(1))
    }

    pub(crate) fn parse_variant_path_type_args(
        &mut self,
        path: &syn::Path,
        context: &'static str,
    ) -> Result<Vec<RustType>, SourceError> {
        let Some(segment_index) = path.segments.len().checked_sub(2) else {
            return Err(SourceError::Invalid {
                context,
                detail: "missing enum type segment".to_string(),
            });
        };
        self.parse_path_type_args_at(path, context, segment_index)
    }

    pub(crate) fn nominal_type_args(ty: &RustType) -> Vec<RustType> {
        match ty {
            RustType::Named { type_args, .. } => type_args.clone(),
            RustType::Cell { inner }
            | RustType::RefCell { inner }
            | RustType::UnsafeCell { inner }
            | RustType::Option { inner } => vec![(**inner).clone()],
            RustType::Result { ok, err } => vec![(**ok).clone(), (**err).clone()],
            _ => Vec::new(),
        }
    }

    pub(crate) fn nominal_const_args(ty: &RustType) -> Vec<ConstGenericArg> {
        match ty {
            RustType::Named { const_args, .. } => const_args.clone(),
            _ => Vec::new(),
        }
    }

    pub(crate) fn parse_method_turbofish_type_args(
        &mut self,
        turbofish: Option<&syn::AngleBracketedGenericArguments>,
        method_name: &str,
    ) -> Result<Vec<RustType>, SourceError> {
        turbofish.map_or(Ok(Vec::new()), |args| {
            self.parse_expr_generic_type_args(
                &args.args,
                "method call",
                &format!("method `{method_name}`"),
            )
        })
    }

    fn parse_path_type_args_at(
        &mut self,
        path: &syn::Path,
        context: &'static str,
        segment_index: usize,
    ) -> Result<Vec<RustType>, SourceError> {
        let target = format!("path `{}`", Self::path_to_string(path));
        let Some(segment) = path.segments.iter().nth(segment_index) else {
            return Err(SourceError::Invalid {
                context,
                detail: "missing path segment".to_string(),
            });
        };
        self.parse_expr_path_arguments(&segment.arguments, context, &target)
    }

    fn validate_expr_path_arguments(
        &mut self,
        arguments: &syn::PathArguments,
        context: &'static str,
        target: &str,
    ) -> Result<(), SourceError> {
        let _ = self.parse_expr_path_arguments(arguments, context, target)?;
        Ok(())
    }

    fn parse_expr_path_arguments(
        &mut self,
        arguments: &syn::PathArguments,
        context: &'static str,
        target: &str,
    ) -> Result<Vec<RustType>, SourceError> {
        match arguments {
            syn::PathArguments::None => Ok(Vec::new()),
            syn::PathArguments::AngleBracketed(args) => {
                self.parse_expr_generic_type_args(&args.args, context, target)
            }
            syn::PathArguments::Parenthesized(_) => Err(Self::unsupported(
                context,
                format!(
                    "parenthesized generic arguments in expression-position {target} are not yet supported"
                ),
            )),
        }
    }

    fn parse_expr_generic_type_args(
        &mut self,
        args: &syn::punctuated::Punctuated<syn::GenericArgument, syn::Token![,]>,
        context: &'static str,
        target: &str,
    ) -> Result<Vec<RustType>, SourceError> {
        let mut type_args = Vec::new();
        for arg in args {
            match arg {
                syn::GenericArgument::Type(ty) => type_args.push(self.parse_type(ty)?),
                syn::GenericArgument::Lifetime(_) => {}
                syn::GenericArgument::Const(_) => {
                    return Err(Self::unsupported(
                        context,
                        format!(
                            "const generic arguments in expression-position {target} are not yet supported"
                        ),
                    ));
                }
                syn::GenericArgument::AssocType(_)
                | syn::GenericArgument::AssocConst(_)
                | syn::GenericArgument::Constraint(_) => {
                    return Err(Self::unsupported(
                        context,
                        format!(
                            "associated generic arguments in expression-position {target} are not yet supported"
                        ),
                    ));
                }
                _ => {
                    return Err(Self::unsupported(
                        context,
                        format!("unsupported generic arguments in expression-position {target}"),
                    ));
                }
            }
        }
        Ok(type_args)
    }

    /// Parse generic args from an enum variant path, returning both type and const args.
    ///
    /// Const generic args in expression position are not yet supported, so the
    /// const_args vector is always empty for now.
    pub(crate) fn parse_variant_path_generic_args(
        &mut self,
        path: &syn::Path,
        context: &'static str,
    ) -> Result<(Vec<RustType>, Vec<ConstGenericArg>), SourceError> {
        let type_args = self.parse_variant_path_type_args(path, context)?;
        Ok((type_args, Vec::new()))
    }

    /// Parse generic args from a nominal path, returning both type and const args.
    pub(crate) fn parse_nominal_path_generic_args(
        &mut self,
        path: &syn::Path,
        context: &'static str,
    ) -> Result<(Vec<RustType>, Vec<ConstGenericArg>), SourceError> {
        let type_args = self.parse_nominal_path_type_args(path, context)?;
        Ok((type_args, Vec::new()))
    }
}
