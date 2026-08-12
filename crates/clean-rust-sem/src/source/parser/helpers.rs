// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::SourceError;
use super::Parser;
use crate::stmt::{GenericParam, WherePredicate};
use crate::types::{Lifetime, TypeParamDef};

impl Parser {
    pub(crate) fn fresh_anon_lifetime(&mut self) -> Lifetime {
        let next = self.next_anon_lifetime;
        self.next_anon_lifetime += 1;
        Lifetime::Anonymous(next)
    }

    pub(crate) fn fresh_synthetic_local(&mut self, prefix: &str) -> String {
        let next = self.next_synthetic_local;
        self.next_synthetic_local += 1;
        format!("__clean$source${prefix}${next}")
    }

    pub(crate) fn parse_lifetime(lifetime: &syn::Lifetime) -> Lifetime {
        let name = lifetime.ident.to_string();
        if name == "static" {
            Lifetime::Static
        } else {
            Lifetime::Named(name)
        }
    }

    pub(crate) fn parse_generic_params(
        &mut self,
        generics: &syn::Generics,
    ) -> Result<Vec<GenericParam>, SourceError> {
        let mut generic_params = Vec::new();
        for param in &generics.params {
            match param {
                syn::GenericParam::Type(ty_param) => {
                    let mut bounds = Vec::new();
                    for bound in &ty_param.bounds {
                        bounds.push(Self::parse_type_bound_string(
                            bound,
                            "generic parameter",
                            &format!("bound on type parameter `{}`", ty_param.ident),
                        )?);
                    }
                    generic_params.push(GenericParam::Type(TypeParamDef {
                        id: self.next_type_param_id,
                        name: ty_param.ident.to_string(),
                        bounds,
                    }));
                    self.next_type_param_id += 1;
                }
                syn::GenericParam::Lifetime(lifetime) => {
                    generic_params
                        .push(GenericParam::Lifetime(lifetime.lifetime.ident.to_string()));
                }
                syn::GenericParam::Const(cp) => {
                    return Err(Self::unsupported(
                        "generic parameter",
                        format!("const generic parameter `{}`", cp.ident),
                    ));
                }
            }
        }
        Ok(generic_params)
    }

    pub(crate) fn parse_where_clause(
        &mut self,
        where_clause: Option<&syn::WhereClause>,
        context: &'static str,
        target: &str,
    ) -> Result<Vec<WherePredicate>, SourceError> {
        let Some(where_clause) = where_clause else {
            return Ok(Vec::new());
        };

        where_clause
            .predicates
            .iter()
            .map(|predicate| match predicate {
                syn::WherePredicate::Type(pred_type) => Ok(WherePredicate::Type {
                    ty: self.parse_type(&pred_type.bounded_ty)?,
                    bounds: pred_type
                        .bounds
                        .iter()
                        .map(|bound| Self::parse_type_bound_string(bound, context, target))
                        .collect::<Result<Vec<_>, _>>()?,
                }),
                syn::WherePredicate::Lifetime(pred_lifetime) => Ok(WherePredicate::Lifetime {
                    lifetime: pred_lifetime.lifetime.ident.to_string(),
                    bounds: pred_lifetime
                        .bounds
                        .iter()
                        .map(|bound| format!("'{}", bound.ident))
                        .collect(),
                }),
                _ => Err(Self::unsupported(
                    context,
                    format!("unsupported where predicate on {target}"),
                )),
            })
            .collect()
    }

    pub(crate) fn parse_usize_expr(expr: &syn::Expr) -> Result<usize, SourceError> {
        match expr {
            syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Int(int),
                ..
            }) => int
                .base10_parse::<usize>()
                .map_err(|err| SourceError::Invalid {
                    context: "usize expression",
                    detail: err.to_string(),
                }),
            _ => Err(Self::unsupported(
                "const expression",
                "only integer literal const expressions are supported",
            )),
        }
    }

    pub(crate) fn pat_ident_name(pat: &syn::Pat) -> Result<String, SourceError> {
        match pat {
            syn::Pat::Ident(pat_ident) => Ok(pat_ident.ident.to_string()),
            syn::Pat::Type(pat_type) => Self::pat_ident_name(&pat_type.pat),
            _ => Err(Self::unsupported(
                "parameter pattern",
                "only identifier parameters are supported",
            )),
        }
    }

    pub(crate) fn path_to_string(path: &syn::Path) -> String {
        path.segments
            .iter()
            .map(|segment| segment.ident.to_string())
            .collect::<Vec<_>>()
            .join("::")
    }

    /// Extract the trait name from a path, accepting (but not tracking) generic arguments.
    ///
    /// Generic type arguments on trait paths (e.g., `Iterator<Item = u32>`, `From<String>`)
    /// are syntactically validated by `syn` and accepted here.  The arguments are not
    /// stored because the current evaluator dispatches by trait name only.
    pub(crate) fn plain_trait_path_name(
        path: &syn::Path,
        context: &'static str,
        _target: &str,
    ) -> Result<String, SourceError> {
        path.segments
            .last()
            .map(|segment| segment.ident.to_string())
            .ok_or_else(|| SourceError::Invalid {
                context,
                detail: "missing trait path segment".to_string(),
            })
    }

    /// Resolve a trait bound to its trait name, accepting higher-ranked bounds.
    ///
    /// A higher-ranked trait bound such as `for<'a> Fn(&'a T)` is treated as a
    /// quantified bound: the universally-quantified lifetimes are erased and the
    /// bound simplifies to the underlying trait obligation (`Fn`). This is sound
    /// for the name-based trait dispatch the evaluator performs — the bound
    /// lifetimes do not affect which trait must be implemented and are erased.
    pub(crate) fn plain_trait_bound_name(
        trait_bound: &syn::TraitBound,
        context: &'static str,
        target: &str,
    ) -> Result<String, SourceError> {
        Self::plain_trait_path_name(&trait_bound.path, context, target)
    }

    pub(crate) fn parse_type_bound_string(
        bound: &syn::TypeParamBound,
        context: &'static str,
        target: &str,
    ) -> Result<String, SourceError> {
        match bound {
            syn::TypeParamBound::Trait(trait_bound) => {
                let bound_name = Self::plain_trait_bound_name(trait_bound, context, target)?;
                Ok(match trait_bound.modifier {
                    syn::TraitBoundModifier::None => bound_name,
                    syn::TraitBoundModifier::Maybe(_) => format!("?{bound_name}"),
                })
            }
            syn::TypeParamBound::Lifetime(lifetime) => Ok(format!("'{}", lifetime.ident)),
            _ => Err(Self::unsupported(
                context,
                format!("unsupported bound on {target}"),
            )),
        }
    }

    pub(crate) fn path_prefix(path: &syn::Path) -> Option<String> {
        if path.segments.len() <= 1 {
            None
        } else {
            Some(
                path.segments
                    .iter()
                    .take(path.segments.len() - 1)
                    .map(|segment| segment.ident.to_string())
                    .collect::<Vec<_>>()
                    .join("::"),
            )
        }
    }

    pub(crate) fn split_qualified_path(
        path: &syn::Path,
        context: &'static str,
    ) -> Result<(String, String), SourceError> {
        let variant = path
            .segments
            .last()
            .ok_or_else(|| SourceError::Invalid {
                context,
                detail: "missing path segment".to_string(),
            })?
            .ident
            .to_string();
        let Some(prefix) = Self::path_prefix(path) else {
            return Err(Self::unsupported(
                context,
                format!(
                    "unqualified path `{}` is not yet supported",
                    Self::path_to_string(path)
                ),
            ));
        };
        Ok((prefix, variant))
    }

    pub(crate) fn split_known_enum_path(
        &self,
        path: &syn::Path,
        context: &'static str,
    ) -> Result<(String, String), SourceError> {
        let (enum_name, variant) = Self::split_qualified_path(path, context)?;
        let resolved_enum_name = if enum_name == "Self" {
            self.current_inherent_self_enum_name().unwrap_or(enum_name)
        } else {
            enum_name
        };
        if self.enum_has_variant(&resolved_enum_name, &variant) {
            Ok((resolved_enum_name, variant))
        } else {
            Err(Self::unsupported(
                context,
                format!(
                    "qualified path `{}` does not refer to a known top-level enum variant",
                    Self::path_to_string(path)
                ),
            ))
        }
    }

    pub(crate) fn current_inherent_self_enum_name(&self) -> Option<String> {
        let context = self.type_context.as_ref()?;
        if context.trait_name.is_some() {
            return None;
        }
        self.canonical_enum_name(&context.self_ty)
    }

    pub(crate) fn loop_label_name(label: &syn::Label) -> String {
        label.name.ident.to_string()
    }

    pub(crate) fn branch_label_name(label: &syn::Lifetime) -> String {
        label.ident.to_string()
    }

    pub(crate) fn member_name(member: &syn::Member) -> String {
        match member {
            syn::Member::Named(ident) => ident.to_string(),
            syn::Member::Unnamed(index) => index.index.to_string(),
        }
    }

    pub(crate) fn unsupported(context: &'static str, detail: impl Into<String>) -> SourceError {
        SourceError::Unsupported {
            context,
            detail: detail.into(),
        }
    }

    pub(crate) fn item_kind(item: &syn::Item) -> &'static str {
        match item {
            syn::Item::Const(_) => "const",
            syn::Item::Enum(_) => "enum",
            syn::Item::Fn(_) => "fn",
            syn::Item::Impl(_) => "impl",
            syn::Item::Static(_) => "static",
            syn::Item::Struct(_) => "struct",
            syn::Item::Trait(_) => "trait",
            syn::Item::Type(_) => "type",
            syn::Item::Union(_) => "union",
            syn::Item::Use(_) => "use",
            syn::Item::Macro(_) => "macro invocation",
            syn::Item::ExternCrate(_) => "extern crate",
            syn::Item::ForeignMod(_) => "extern block",
            syn::Item::Mod(_) => "mod",
            syn::Item::TraitAlias(_) => "trait alias",
            _ => "other",
        }
    }

    pub(crate) fn impl_item_kind(item: &syn::ImplItem) -> &'static str {
        match item {
            syn::ImplItem::Const(_) => "const",
            syn::ImplItem::Fn(_) => "fn",
            syn::ImplItem::Type(_) => "type",
            syn::ImplItem::Macro(_) => "macro",
            _ => "other",
        }
    }

    pub(crate) fn type_kind(ty: &syn::Type) -> &'static str {
        match ty {
            syn::Type::Array(_) => "array",
            syn::Type::BareFn(_) => "bare fn",
            syn::Type::Never(_) => "never",
            syn::Type::Paren(_) => "paren",
            syn::Type::Path(_) => "path",
            syn::Type::Ptr(_) => "ptr",
            syn::Type::Reference(_) => "reference",
            syn::Type::Slice(_) => "slice",
            syn::Type::TraitObject(_) => "dyn trait",
            syn::Type::ImplTrait(_) => "impl trait",
            syn::Type::Tuple(_) => "tuple",
            syn::Type::Infer(_) => "infer",
            syn::Type::Group(_) => "group",
            _ => "other",
        }
    }

    pub(crate) fn pattern_kind(pat: &syn::Pat) -> &'static str {
        match pat {
            syn::Pat::Ident(_) => "ident",
            syn::Pat::Lit(_) => "lit",
            syn::Pat::Or(_) => "or",
            syn::Pat::Paren(_) => "paren",
            syn::Pat::Path(_) => "path",
            syn::Pat::Range(_) => "range",
            syn::Pat::Reference(_) => "reference",
            syn::Pat::Struct(_) => "struct",
            syn::Pat::Tuple(_) => "tuple",
            syn::Pat::TupleStruct(_) => "tuple struct",
            syn::Pat::Type(_) => "type ascription",
            syn::Pat::Wild(_) => "wild",
            syn::Pat::Slice(_) => "slice",
            syn::Pat::Rest(_) => "rest",
            _ => "other",
        }
    }

    /// Parse generic type parameters from a `syn::Generics`.
    ///
    /// Extracts type parameters with their trait bounds. Lifetime parameters
    /// are accepted but not tracked (they don't affect semantic lowering).
    /// Const generic parameters are rejected.
    pub(crate) fn parse_generics(
        generics: &syn::Generics,
    ) -> Result<Vec<TypeParamDef>, SourceError> {
        let mut type_params = Vec::new();
        for param in &generics.params {
            match param {
                syn::GenericParam::Type(ty_param) => {
                    let mut bounds = Vec::new();
                    for bound in &ty_param.bounds {
                        match bound {
                            syn::TypeParamBound::Trait(trait_bound) => {
                                bounds.push(Self::plain_trait_bound_name(
                                    trait_bound,
                                    "generic parameter",
                                    &format!("trait bound on type parameter `{}`", ty_param.ident),
                                )?)
                            }
                            syn::TypeParamBound::Lifetime(_) => {}
                            _ => {}
                        }
                    }
                    type_params.push(TypeParamDef {
                        id: 0,
                        name: ty_param.ident.to_string(),
                        bounds,
                    });
                }
                syn::GenericParam::Lifetime(_) => {
                    // Lifetime parameters are accepted but don't produce TypeParamDefs
                }
                syn::GenericParam::Const(cp) => {
                    return Err(Self::unsupported(
                        "generic parameter",
                        format!("const generic parameter `{}`", cp.ident),
                    ));
                }
            }
        }
        // Also collect bounds from where clauses
        if let Some(where_clause) = &generics.where_clause {
            for predicate in &where_clause.predicates {
                if let syn::WherePredicate::Type(pred_type) = predicate {
                    if let syn::Type::Path(type_path) = &pred_type.bounded_ty {
                        let name = Self::path_to_string(&type_path.path);
                        if let Some(tp) = type_params.iter_mut().find(|tp| tp.name == name) {
                            for bound in &pred_type.bounds {
                                if let syn::TypeParamBound::Trait(trait_bound) = bound {
                                    tp.bounds.push(Self::plain_trait_bound_name(
                                        trait_bound,
                                        "generic parameter",
                                        &format!("trait bound on type parameter `{}`", tp.name),
                                    )?);
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(type_params)
    }

    pub(crate) fn expr_kind(expr: &syn::Expr) -> &'static str {
        match expr {
            syn::Expr::Array(_) => "array",
            syn::Expr::Assign(_) => "assign",
            syn::Expr::Binary(_) => "binary",
            syn::Expr::Block(_) => "block",
            syn::Expr::Break(_) => "break",
            syn::Expr::Call(_) => "call",
            syn::Expr::Cast(_) => "cast",
            syn::Expr::Closure(_) => "closure",
            syn::Expr::Continue(_) => "continue",
            syn::Expr::Field(_) => "field",
            syn::Expr::ForLoop(_) => "for",
            syn::Expr::Group(_) => "group",
            syn::Expr::If(_) => "if",
            syn::Expr::Index(_) => "index",
            syn::Expr::Lit(_) => "literal",
            syn::Expr::Loop(_) => "loop",
            syn::Expr::Macro(_) => "macro",
            syn::Expr::Match(_) => "match",
            syn::Expr::MethodCall(_) => "method call",
            syn::Expr::Paren(_) => "paren",
            syn::Expr::Path(_) => "path",
            syn::Expr::Range(_) => "range",
            syn::Expr::Reference(_) => "reference",
            syn::Expr::Repeat(_) => "repeat",
            syn::Expr::Return(_) => "return",
            syn::Expr::Struct(_) => "struct",
            syn::Expr::Tuple(_) => "tuple",
            syn::Expr::Unary(_) => "unary",
            syn::Expr::Unsafe(_) => "unsafe",
            syn::Expr::Const(_) => "const block",
            syn::Expr::Let(_) => "let",
            syn::Expr::While(_) => "while",
            _ => "other",
        }
    }
}
