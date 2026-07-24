// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{parser::Parser, SourceError};
use crate::expr::{EnumPatternPayload, Pattern};
use crate::types::Mutability;

impl Parser {
    pub(super) fn parse_pattern(&mut self, pat: &syn::Pat) -> Result<Pattern, SourceError> {
        match pat {
            syn::Pat::Wild(_) => Ok(Pattern::Wildcard),
            syn::Pat::Ident(pat_ident) => Ok(Pattern::Binding {
                name: pat_ident.ident.to_string(),
                mutable: pat_ident.mutability.is_some(),
                subpattern: pat_ident
                    .subpat
                    .as_ref()
                    .map(|(_, pat)| self.parse_pattern(pat).map(Box::new))
                    .transpose()?,
            }),
            syn::Pat::Tuple(tuple) => Ok(Pattern::Tuple(
                tuple
                    .elems
                    .iter()
                    .map(|pat| self.parse_pattern(pat))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            syn::Pat::Lit(pat_lit) => Ok(Pattern::Literal(self.parse_lit(&pat_lit.lit)?)),
            syn::Pat::Path(path) => self.parse_path_pattern(path),
            syn::Pat::Reference(reference) => Ok(Pattern::Ref {
                mutability: if reference.mutability.is_some() {
                    Mutability::Mutable
                } else {
                    Mutability::Shared
                },
                pattern: Box::new(self.parse_pattern(&reference.pat)?),
            }),
            syn::Pat::Paren(paren) => self.parse_pattern(&paren.pat),
            syn::Pat::Or(or_pat) => Ok(Pattern::Or(
                or_pat
                    .cases
                    .iter()
                    .map(|pat| self.parse_pattern(pat))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            syn::Pat::TupleStruct(tuple_struct) => self.parse_tuple_struct_pattern(tuple_struct),
            syn::Pat::Struct(struct_pat) => self.parse_struct_pattern(struct_pat),
            syn::Pat::Range(range) => Ok(Pattern::Range {
                start: self.parse_lit_expr(range.start.as_deref().ok_or_else(|| {
                    SourceError::Invalid {
                        context: "range pattern",
                        detail: "range pattern is missing a start bound".to_string(),
                    }
                })?)?,
                end: self.parse_lit_expr(range.end.as_deref().ok_or_else(|| {
                    SourceError::Invalid {
                        context: "range pattern",
                        detail: "range pattern is missing an end bound".to_string(),
                    }
                })?)?,
                inclusive: matches!(range.limits, syn::RangeLimits::Closed(_)),
            }),
            syn::Pat::Slice(slice) => Ok(Pattern::Slice(
                slice
                    .elems
                    .iter()
                    .map(|pat| self.parse_pattern(pat))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            syn::Pat::Rest(_) => Ok(Pattern::Rest),
            other => Err(Self::unsupported(
                "pattern",
                format!("unsupported pattern `{}`", Self::pattern_kind(other)),
            )),
        }
    }

    fn parse_tuple_struct_pattern(
        &mut self,
        tuple_struct: &syn::PatTupleStruct,
    ) -> Result<Pattern, SourceError> {
        let path = &tuple_struct.path;
        // Single-segment path: check if it's a known tuple struct or alias.
        if path.segments.len() == 1 {
            let name = path.segments.last().expect("len checked").ident.to_string();
            if let Some(name) = self.canonical_tuple_struct_name(&name)? {
                let fields = tuple_struct
                    .elems
                    .iter()
                    .enumerate()
                    .map(|(i, pat)| Ok((i.to_string(), self.parse_pattern(pat)?)))
                    .collect::<Result<Vec<_>, SourceError>>()?;
                return Ok(Pattern::Struct {
                    name,
                    fields,
                    rest: false,
                });
            }
        }
        // Multi-segment path or not a known tuple struct: treat as enum variant
        let (enum_name, variant) = self.split_known_enum_path(path, "tuple struct pattern")?;
        Ok(Pattern::EnumVariant {
            enum_name,
            variant,
            payload: EnumPatternPayload::Tuple(
                tuple_struct
                    .elems
                    .iter()
                    .map(|pat| self.parse_pattern(pat))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
        })
    }

    fn parse_struct_pattern(
        &mut self,
        struct_pat: &syn::PatStruct,
    ) -> Result<Pattern, SourceError> {
        let path = &struct_pat.path;
        let fields = struct_pat
            .fields
            .iter()
            .map(|field| {
                Ok((
                    Self::member_name(&field.member),
                    self.parse_pattern(&field.pat)?,
                ))
            })
            .collect::<Result<Vec<_>, SourceError>>()?;
        if path.segments.len() > 1 {
            let (enum_name, variant) = self.split_known_enum_path(path, "struct pattern")?;
            Ok(Pattern::EnumVariant {
                enum_name,
                variant,
                payload: EnumPatternPayload::Struct(fields),
            })
        } else {
            let name = path
                .segments
                .last()
                .ok_or_else(|| SourceError::Invalid {
                    context: "struct pattern",
                    detail: "missing type name".to_string(),
                })?
                .ident
                .to_string();
            let name = self.canonical_named_struct_name(&name)?.unwrap_or(name);
            Ok(Pattern::Struct {
                name,
                fields,
                rest: struct_pat.rest.is_some(),
            })
        }
    }

    fn parse_path_pattern(&mut self, path: &syn::PatPath) -> Result<Pattern, SourceError> {
        let (enum_name, variant) = self.split_known_enum_path(&path.path, "path pattern")?;
        Ok(Pattern::EnumVariant {
            enum_name,
            variant,
            payload: EnumPatternPayload::Unit,
        })
    }
}
