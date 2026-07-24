// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{parser::Parser, SourceError};
use crate::expr::{EnumVariantPayload, Expr};
use crate::types::RustType;

impl Parser {
    pub(super) fn parse_path_call_expr(
        &mut self,
        call: &syn::ExprCall,
        path: &syn::ExprPath,
    ) -> Result<Expr, SourceError> {
        self.validate_expr_path_generics(&path.path, "call expression")?;
        let type_args = self.parse_path_call_type_args(&path.path, "call expression")?;
        if let Some((self_ty, trait_name, method)) =
            self.parse_trait_qualified_call_target(path, "call expression")?
        {
            let Some(type_name) = self.canonical_nominal_type_name(&self_ty) else {
                return Err(Self::unsupported(
                    "call expression",
                    format!(
                        "trait-qualified call `<Type as {trait_name}>::{method}(...)` does not refer to a known nominal type"
                    ),
                ));
            };
            if !self.trait_impl_has_associated_function(&type_name, &trait_name, &method) {
                return Err(Self::unsupported(
                    "call expression",
                    format!(
                        "trait-qualified call `<{type_name} as {trait_name}>::{method}(...)` does not refer to a known associated function"
                    ),
                ));
            }
            return self.parse_trait_qualified_associated_function_call(
                &type_name,
                &trait_name,
                &method,
                &call.args,
                type_args,
            );
        }
        if let Some(self_ty) = self.parse_qself_call_self_type(path, "call expression")? {
            let method = path
                .path
                .segments
                .last()
                .expect("qself path has a final segment")
                .ident
                .to_string();
            if let Some(enum_name) = self.canonical_enum_name(&self_ty) {
                let type_args = Self::nominal_type_args(&self_ty);
                let const_args = Self::nominal_const_args(&self_ty);
                if self.enum_has_variant(&enum_name, &method) {
                    return self.parse_enum_variant_call_target(
                        enum_name,
                        method.clone(),
                        &call.args,
                        type_args,
                        const_args,
                        "call expression",
                        &format!("qself call `<Type>::{method}(...)`"),
                    );
                }
            }
            if let Some(type_name) = self.canonical_nominal_type_name(&self_ty) {
                if self.type_has_associated_function(&type_name, &method) {
                    return self.parse_associated_function_call(
                        &type_name, &method, &call.args, type_args,
                    );
                }
                return Err(Self::unsupported(
                    "call expression",
                    format!(
                        "qself call `<{type_name}>::{method}(...)` does not refer to a known top-level enum variant or a known associated function"
                    ),
                ));
            }
            return Err(Self::unsupported(
                "call expression",
                format!(
                    "qself call `<Type>::{method}` does not refer to a known top-level enum variant or a known nominal type"
                ),
            ));
        }
        if path.path.segments.len() > 1 {
            if let Some((enum_name, variant)) = self.resolve_enum_path(&path.path)? {
                let (type_args, const_args) =
                    self.parse_variant_path_generic_args(&path.path, "call expression")?;
                return self.parse_enum_variant_call_target(
                    enum_name,
                    variant,
                    &call.args,
                    type_args,
                    const_args,
                    "call expression",
                    &format!("qualified call `{}`", Self::path_to_string(&path.path)),
                );
            }
            if let Some(name) = self.associated_function_path_name(&path.path)? {
                return self.parse_function_path_call(name, &call.args, type_args);
            }
            return Err(Self::unsupported(
                "call expression",
                format!(
                    "qualified call `{}` does not refer to a known top-level enum variant or a known nominal type",
                    Self::path_to_string(&path.path)
                ),
            ));
        }
        if path.qself.is_none() && path.path.segments.len() == 1 {
            let name = path
                .path
                .segments
                .last()
                .expect("len checked")
                .ident
                .to_string();
            if let Some(canonical_name) = self.canonical_tuple_struct_name(&name)? {
                let (type_args, const_args) =
                    self.parse_nominal_path_generic_args(&path.path, "call expression")?;
                return self.parse_tuple_struct_call(
                    &canonical_name,
                    &call.args,
                    type_args,
                    const_args,
                );
            }
            if self.canonical_named_struct_name(&name)?.is_some() {
                return Err(Self::unsupported(
                    "call expression",
                    format!("named struct `{name}` must be constructed with field syntax"),
                ));
            }
        }
        Ok(Expr::Call {
            func: Box::new(self.parse_expr(&call.func)?),
            args: call
                .args
                .iter()
                .map(|arg| self.parse_expr(arg))
                .collect::<Result<Vec<_>, _>>()?,
            type_args,
        })
    }

    pub(super) fn parse_qself_path_expr(
        &mut self,
        path: &syn::ExprPath,
    ) -> Result<Expr, SourceError> {
        if let Some((self_ty, trait_name, item)) =
            self.parse_trait_qualified_call_target(path, "path expression")?
        {
            let Some(type_name) = self.canonical_nominal_type_name(&self_ty) else {
                return Err(Self::unsupported(
                    "path expression",
                    format!(
                        "trait-qualified path `<Type as {trait_name}>::{item}` does not refer to a known nominal type"
                    ),
                ));
            };
            if self.trait_impl_has_associated_function(&type_name, &trait_name, &item) {
                return Ok(Expr::Var {
                    name: format!("<{type_name} as {trait_name}>::{item}"),
                    local_idx: 0,
                });
            }
            if self.trait_impl_has_associated_constant(&type_name, &trait_name, &item) {
                return Ok(Expr::Var {
                    name: format!("<{type_name} as {trait_name}>::{item}"),
                    local_idx: 0,
                });
            }
            return Err(Self::unsupported(
                "path expression",
                "trait-qualified associated paths like `<Type as Trait>::ITEM` are not yet supported",
            ));
        }
        let Some(self_ty) = self.parse_qself_path_self_type(path, "path expression")? else {
            return self.parse_path_expr(path);
        };
        let item = path
            .path
            .segments
            .last()
            .expect("qself path has a final segment")
            .ident
            .to_string();
        if let Some(lit) = Self::try_resolve_associated_constant_on_type(&self_ty, &item) {
            return Ok(Expr::Literal(lit));
        }
        if let Some(enum_name) = self.canonical_enum_name(&self_ty) {
            if self.enum_has_unit_variant(&enum_name, &item) {
                return Ok(Expr::EnumVariant {
                    enum_name,
                    variant: item,
                    payload: EnumVariantPayload::Unit,
                    type_args: Self::nominal_type_args(&self_ty),
                    const_args: Self::nominal_const_args(&self_ty),
                });
            }
            if self.enum_has_tuple_variant(&enum_name, &item) {
                return Ok(Expr::Var {
                    name: format!("{enum_name}::{item}"),
                    local_idx: 0,
                });
            }
            if self.enum_has_variant(&enum_name, &item) {
                return Err(Self::unsupported(
                    "path expression",
                    format!(
                        "qself path `<Type>::{item}` refers to a struct enum variant and must be constructed with named fields"
                    ),
                ));
            }
        }
        if let Some(type_name) = self.canonical_nominal_type_name(&self_ty) {
            if self.type_has_associated_constant(&type_name, &item) {
                return Ok(Expr::Var {
                    name: format!("{type_name}::{item}"),
                    local_idx: 0,
                });
            }
            if self.type_has_associated_function(&type_name, &item) {
                return Ok(Expr::Var {
                    name: format!("{type_name}::{item}"),
                    local_idx: 0,
                });
            }
        }
        Err(Self::unsupported(
            "path expression",
            format!(
                "qself path `<Type>::{item}` does not refer to a known top-level enum variant, a known associated constant, or a known associated function"
            ),
        ))
    }

    pub(super) fn parse_path_expr(&mut self, path: &syn::ExprPath) -> Result<Expr, SourceError> {
        // Try resolving as a well-known associated constant (e.g., u32::MAX)
        if let Some(lit) = Self::try_resolve_associated_constant(&path.path) {
            return Ok(Expr::Literal(lit));
        }
        if let Some((enum_name, variant)) = self.resolve_enum_path(&path.path)? {
            if self.enum_has_unit_variant(&enum_name, &variant) {
                let (type_args, const_args) =
                    self.parse_variant_path_generic_args(&path.path, "path expression")?;
                return Ok(Expr::EnumVariant {
                    enum_name,
                    variant,
                    payload: EnumVariantPayload::Unit,
                    type_args,
                    const_args,
                });
            }
            if self.enum_has_tuple_variant(&enum_name, &variant) {
                return Ok(Expr::Var {
                    name: format!("{enum_name}::{variant}"),
                    local_idx: 0,
                });
            }
            if self.enum_has_variant(&enum_name, &variant) {
                return Err(Self::unsupported(
                    "path expression",
                    format!(
                        "qualified path `{}` refers to a struct enum variant and must be constructed with named fields",
                        Self::path_to_string(&path.path)
                    ),
                ));
            }
        }
        if let Some(name) = self.associated_constant_path_name(&path.path)? {
            return Ok(Expr::Var { name, local_idx: 0 });
        }
        if let Some(name) = self.associated_function_path_name(&path.path)? {
            return Ok(Expr::Var { name, local_idx: 0 });
        }
        Err(Self::unsupported(
            "path expression",
            format!(
                "qualified path `{}` does not refer to a known top-level enum variant, a known associated constant, or a known associated function",
                Self::path_to_string(&path.path)
            ),
        ))
    }

    pub(super) fn parse_enum_variant_call(
        &mut self,
        enum_name: String,
        variant: String,
        args: &syn::punctuated::Punctuated<syn::Expr, syn::token::Comma>,
        type_args: Vec<RustType>,
        const_args: Vec<crate::types::ConstGenericArg>,
    ) -> Result<Expr, SourceError> {
        Ok(Expr::EnumVariant {
            enum_name,
            variant,
            payload: EnumVariantPayload::Tuple(
                args.iter()
                    .map(|arg| self.parse_expr(arg))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            type_args,
            const_args,
        })
    }

    fn parse_enum_variant_call_target(
        &mut self,
        enum_name: String,
        variant: String,
        args: &syn::punctuated::Punctuated<syn::Expr, syn::token::Comma>,
        type_args: Vec<RustType>,
        const_args: Vec<crate::types::ConstGenericArg>,
        context: &'static str,
        target: &str,
    ) -> Result<Expr, SourceError> {
        if self.enum_has_tuple_variant(&enum_name, &variant) {
            return self.parse_enum_variant_call(enum_name, variant, args, type_args, const_args);
        }
        if self.enum_has_unit_variant(&enum_name, &variant) {
            return Err(Self::unsupported(
                context,
                format!("{target} refers to a unit enum variant and must not be called with `()`"),
            ));
        }
        Err(Self::unsupported(
            context,
            format!(
                "{target} refers to a struct enum variant and must be constructed with named fields"
            ),
        ))
    }

    pub(super) fn parse_associated_function_call(
        &mut self,
        type_name: &str,
        method: &str,
        args: &syn::punctuated::Punctuated<syn::Expr, syn::token::Comma>,
        type_args: Vec<RustType>,
    ) -> Result<Expr, SourceError> {
        self.parse_function_path_call(format!("{type_name}::{method}"), args, type_args)
    }

    pub(super) fn parse_trait_qualified_associated_function_call(
        &mut self,
        type_name: &str,
        trait_name: &str,
        method: &str,
        args: &syn::punctuated::Punctuated<syn::Expr, syn::token::Comma>,
        type_args: Vec<RustType>,
    ) -> Result<Expr, SourceError> {
        self.parse_function_path_call(
            format!("<{type_name} as {trait_name}>::{method}"),
            args,
            type_args,
        )
    }

    pub(super) fn parse_function_path_call(
        &mut self,
        name: String,
        args: &syn::punctuated::Punctuated<syn::Expr, syn::token::Comma>,
        type_args: Vec<RustType>,
    ) -> Result<Expr, SourceError> {
        Ok(Expr::Call {
            func: Box::new(Expr::Var { name, local_idx: 0 }),
            args: args
                .iter()
                .map(|arg| self.parse_expr(arg))
                .collect::<Result<Vec<_>, _>>()?,
            type_args,
        })
    }

    pub(super) fn parse_trait_qualified_call_target(
        &mut self,
        path: &syn::ExprPath,
        context: &'static str,
    ) -> Result<Option<(RustType, String, String)>, SourceError> {
        let Some(qself) = &path.qself else {
            return Ok(None);
        };
        if qself.as_token.is_none() || qself.position == 0 {
            return Ok(None);
        }
        if path.path.segments.len() != qself.position + 1 {
            return Err(Self::unsupported(
                context,
                "nested trait-qualified associated calls beyond `<Type as Trait>::item` are not yet supported",
            ));
        }

        for segment in path.path.segments.iter().take(qself.position) {
            if !matches!(segment.arguments, syn::PathArguments::None) {
                return Err(Self::unsupported(
                    context,
                    "trait-qualified associated calls with generic trait paths are not yet supported",
                ));
            }
        }

        let trait_segment = path
            .path
            .segments
            .iter()
            .nth(qself.position - 1)
            .ok_or_else(|| SourceError::Invalid {
                context,
                detail: "missing trait segment".to_string(),
            })?;
        let item_segment = path
            .path
            .segments
            .last()
            .ok_or_else(|| SourceError::Invalid {
                context,
                detail: "missing associated item segment".to_string(),
            })?;

        Ok(Some((
            self.parse_type(&qself.ty)?,
            trait_segment.ident.to_string(),
            item_segment.ident.to_string(),
        )))
    }

    fn parse_qself_path_self_type(
        &mut self,
        path: &syn::ExprPath,
        context: &'static str,
    ) -> Result<Option<RustType>, SourceError> {
        let Some(qself) = &path.qself else {
            return Ok(None);
        };
        if qself.as_token.is_some() || qself.position != 0 {
            return Err(Self::unsupported(
                context,
                "trait-qualified associated paths like `<Type as Trait>::ITEM` are not yet supported",
            ));
        }
        if path.path.segments.len() != 1 {
            return Err(Self::unsupported(
                context,
                "nested qself paths beyond `<Type>::ITEM` are not yet supported",
            ));
        }
        self.parse_type(&qself.ty).map(Some)
    }

    pub(super) fn parse_qself_call_self_type(
        &mut self,
        path: &syn::ExprPath,
        context: &'static str,
    ) -> Result<Option<RustType>, SourceError> {
        let Some(qself) = &path.qself else {
            return Ok(None);
        };
        if qself.as_token.is_some() || qself.position != 0 {
            return Err(Self::unsupported(
                context,
                "trait-qualified associated calls like `<Type as Trait>::item(...)` are not yet supported",
            ));
        }
        if path.path.segments.len() != 1 {
            return Err(Self::unsupported(
                context,
                "nested qself paths beyond `<Type>::item` are not yet supported",
            ));
        }
        self.parse_type(&qself.ty).map(Some)
    }

    pub(super) fn parse_tuple_struct_call(
        &mut self,
        name: &str,
        args: &syn::punctuated::Punctuated<syn::Expr, syn::token::Comma>,
        type_args: Vec<RustType>,
        const_args: Vec<crate::types::ConstGenericArg>,
    ) -> Result<Expr, SourceError> {
        Ok(Expr::Struct {
            name: name.to_string(),
            fields: args
                .iter()
                .enumerate()
                .map(|(index, arg)| Ok((index.to_string(), self.parse_expr(arg)?)))
                .collect::<Result<Vec<_>, SourceError>>()?,
            type_args,
            const_args,
        })
    }
}
