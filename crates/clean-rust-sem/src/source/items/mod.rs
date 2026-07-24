// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{parser::Parser, SourceError};
use crate::expr::Item;
use crate::types::{Mutability, RustType, StructField, Visibility};

mod block;
mod traits;

#[cfg(test)]
mod tests;

impl Parser {
    pub(super) fn parse_item(&mut self, item: syn::Item) -> Result<Item, SourceError> {
        match item {
            syn::Item::Fn(item_fn) => self.parse_fn_item(item_fn, None),
            syn::Item::Struct(item_struct) => self.parse_struct_item(item_struct),
            syn::Item::Enum(item_enum) => self.parse_enum_item(item_enum),
            syn::Item::Trait(item_trait) => self.parse_trait_item(item_trait),
            syn::Item::Union(item_union) => self.parse_union_item(item_union),
            syn::Item::Impl(item_impl) => self.parse_impl_item(item_impl),
            syn::Item::Const(item_const) => Ok(Item::Const {
                name: item_const.ident.to_string(),
                ty: self.parse_type(&item_const.ty)?,
                value: self.parse_expr(&item_const.expr)?,
            }),
            syn::Item::Static(item_static) => Ok(Item::Static {
                name: item_static.ident.to_string(),
                ty: self.parse_type(&item_static.ty)?,
                mutable: matches!(item_static.mutability, syn::StaticMutability::Mut(_)),
                value: self.parse_expr(&item_static.expr)?,
            }),
            syn::Item::Type(item_type) => self.parse_type_alias_item(&item_type, true),
            syn::Item::Use(_) => Err(Self::unsupported(
                "item",
                "use declarations are not yet resolved during source ingestion",
            )),
            syn::Item::Macro(item_macro) => {
                match Self::builtin_item_macro_dispatch_name(&item_macro.mac.path).as_deref() {
                    Some("global_asm") => self.parse_global_asm_item(&item_macro.mac),
                    _ => Err(Self::unsupported(
                        "item",
                        format!(
                            "unsupported item macro `{}!`",
                            Self::path_to_string(&item_macro.mac.path)
                        ),
                    )),
                }
            }
            other => Err(Self::unsupported(
                "item",
                format!("unsupported item kind `{}`", Self::item_kind(&other)),
            )),
        }
    }

    /// Parse a `type Name = Ty;` declaration into an [`Item::TypeAlias`].
    ///
    /// Generic type aliases (those with type/const parameters or a where
    /// clause) are rejected, matching the alias-resolution table, which only
    /// stores non-generic aliases. `block_scoped` records whether the alias was
    /// declared inside a block; it is purely informational because aliases are
    /// resolved structurally at parse time and carry no runtime behavior.
    fn parse_type_alias_item(
        &mut self,
        item_type: &syn::ItemType,
        block_scoped: bool,
    ) -> Result<Item, SourceError> {
        if !item_type.generics.params.is_empty() || item_type.generics.where_clause.is_some() {
            return Err(Self::unsupported(
                "type alias",
                format!("generic type alias `{}`", item_type.ident),
            ));
        }
        Ok(Item::TypeAlias {
            name: item_type.ident.to_string(),
            ty: self.parse_type(&item_type.ty)?,
            block_scoped,
        })
    }

    fn parse_fn_item(
        &mut self,
        item_fn: syn::ItemFn,
        self_ty: Option<&RustType>,
    ) -> Result<Item, SourceError> {
        let type_params = self.assign_type_param_ids(Self::parse_generics(&item_fn.sig.generics)?);
        self.with_type_params(&type_params, |parser| {
            let params = item_fn
                .sig
                .inputs
                .iter()
                .map(|arg| parser.parse_fn_arg(arg, self_ty))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Item::Fn {
                name: item_fn.sig.ident.to_string(),
                params,
                ret: parser.parse_return_type(&item_fn.sig.output)?,
                body: parser.parse_block(&item_fn.block)?,
                is_unsafe: item_fn.sig.unsafety.is_some(),
                is_async: item_fn.sig.asyncness.is_some(),
                type_params: type_params.clone(),
            })
        })
    }

    fn parse_struct_item(&mut self, item_struct: syn::ItemStruct) -> Result<Item, SourceError> {
        let (type_params, const_params) =
            self.parse_type_and_const_params(&item_struct.generics)?;
        let type_params = self.assign_type_param_ids(type_params);
        self.with_type_params(&type_params, |parser| {
            parser.with_const_params(&const_params, |parser| {
                let fields = match item_struct.fields {
                    syn::Fields::Named(fields) => fields
                        .named
                        .into_iter()
                        .map(|field| {
                            let name = field.ident.ok_or_else(|| SourceError::Invalid {
                                context: "struct field",
                                detail: "named field is missing an identifier".to_string(),
                            })?;
                            Ok::<_, SourceError>((name.to_string(), parser.parse_type(&field.ty)?))
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                    syn::Fields::Unit => Vec::new(),
                    syn::Fields::Unnamed(fields) => fields
                        .unnamed
                        .iter()
                        .enumerate()
                        .map(|(i, field)| {
                            Ok::<_, SourceError>((i.to_string(), parser.parse_type(&field.ty)?))
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                };
                Ok(Item::Struct {
                    name: item_struct.ident.to_string(),
                    fields,
                    type_params: type_params.clone(),
                    const_params: const_params.clone(),
                })
            })
        })
    }

    fn parse_enum_item(&mut self, item_enum: syn::ItemEnum) -> Result<Item, SourceError> {
        let (type_params, const_params) = self.parse_type_and_const_params(&item_enum.generics)?;
        let type_params = self.assign_type_param_ids(type_params);
        self.with_type_params(&type_params, |parser| {
            parser.with_const_params(&const_params, |parser| {
                let variants = item_enum
                    .variants
                    .into_iter()
                    .map(|variant| {
                        let discriminant = variant
                            .discriminant
                            .map(|(_, expr)| Self::parse_discriminant_expr(&expr))
                            .transpose()?;
                        let name = variant.ident.to_string();
                        match variant.fields {
                            syn::Fields::Unit => {
                                Ok::<_, SourceError>(crate::types::EnumVariant::Unit {
                                    name,
                                    discriminant,
                                })
                            }
                            syn::Fields::Unnamed(fields) => Ok(crate::types::EnumVariant::Tuple {
                                name,
                                fields: fields
                                    .unnamed
                                    .into_iter()
                                    .map(|field| parser.parse_type(&field.ty))
                                    .collect::<Result<Vec<_>, _>>()?,
                                discriminant,
                            }),
                            syn::Fields::Named(fields) => Ok(crate::types::EnumVariant::Struct {
                                name,
                                fields: fields
                                    .named
                                    .into_iter()
                                    .map(|field| {
                                        let field_name =
                                            field.ident.ok_or_else(|| SourceError::Invalid {
                                                context: "enum variant field",
                                                detail: "named field is missing an identifier"
                                                    .to_string(),
                                            })?;
                                        Ok::<_, SourceError>(StructField {
                                            name: field_name.to_string(),
                                            ty: parser.parse_type(&field.ty)?,
                                            visibility: Visibility::Private,
                                        })
                                    })
                                    .collect::<Result<Vec<_>, _>>()?,
                                discriminant,
                            }),
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Item::Enum {
                    name: item_enum.ident.to_string(),
                    variants,
                    type_params: type_params.clone(),
                    const_params: const_params.clone(),
                })
            })
        })
    }

    /// Parse an explicit enum discriminant expression (e.g., `= 42` or `= -1`).
    /// Only literal integers and negated literal integers are supported.
    fn parse_discriminant_expr(expr: &syn::Expr) -> Result<i128, SourceError> {
        match expr {
            syn::Expr::Lit(lit) => match &lit.lit {
                syn::Lit::Int(int) => {
                    let digits = int.base10_digits().replace('_', "");
                    digits.parse::<i128>().map_err(|_| {
                        Self::unsupported(
                            "enum discriminant",
                            format!("integer literal `{digits}` out of i128 range"),
                        )
                    })
                }
                _ => Err(Self::unsupported(
                    "enum discriminant",
                    "non-integer literal",
                )),
            },
            syn::Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Neg(_)) => {
                let positive = Self::parse_discriminant_expr(&unary.expr)?;
                positive.checked_neg().ok_or_else(|| {
                    Self::unsupported(
                        "enum discriminant",
                        format!("negation overflow on `{positive}`"),
                    )
                })
            }
            other => Err(Self::unsupported(
                "enum discriminant",
                format!(
                    "non-literal discriminant expression `{}`",
                    Self::expr_kind(other)
                ),
            )),
        }
    }

    fn parse_union_item(&mut self, item_union: syn::ItemUnion) -> Result<Item, SourceError> {
        let (type_params, const_params) = self.parse_type_and_const_params(&item_union.generics)?;
        let type_params = self.assign_type_param_ids(type_params);
        self.with_type_params(&type_params, |parser| {
            parser.with_const_params(&const_params, |parser| {
                let fields = item_union
                    .fields
                    .named
                    .into_iter()
                    .map(|field| {
                        let name = field.ident.ok_or_else(|| SourceError::Invalid {
                            context: "union field",
                            detail: "union field is missing an identifier".to_string(),
                        })?;
                        Ok::<_, SourceError>((name.to_string(), parser.parse_type(&field.ty)?))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Item::Union {
                    name: item_union.ident.to_string(),
                    fields,
                    type_params: type_params.clone(),
                    const_params: const_params.clone(),
                })
            })
        })
    }

    fn resolve_impl_trait_name(
        &self,
        item_impl: &syn::ItemImpl,
    ) -> Result<Option<String>, SourceError> {
        match &item_impl.trait_ {
            Some((Some(_bang), ..)) => Err(Self::unsupported(
                "impl",
                "negative trait impls (`impl !Trait for Type`) are not supported",
            )),
            Some((None, path, _)) => {
                let name = Self::plain_trait_path_name(path, "impl", "trait impl header")?;
                if self.is_unsafe_trait(&name) && item_impl.unsafety.is_none() {
                    return Err(Self::unsupported(
                        "impl",
                        format!("unsafe trait `{name}` requires `unsafe impl`"),
                    ));
                }
                Ok(Some(name))
            }
            None => Ok(None),
        }
    }

    fn parse_impl_item(&mut self, item_impl: syn::ItemImpl) -> Result<Item, SourceError> {
        let trait_name = self.resolve_impl_trait_name(&item_impl)?;
        let (type_params, const_params) = self.parse_type_and_const_params(&item_impl.generics)?;
        let type_params = self.assign_type_param_ids(type_params);
        let is_trait_impl = trait_name.is_some();
        self.with_type_params(&type_params, |parser| {
            parser.with_const_params(&const_params, |parser| {
                let self_ty = parser.parse_type(&item_impl.self_ty)?;
                let impl_self_ty = self_ty.clone();
                let trait_context = trait_name.clone();
                let items = parser.with_type_context(
                    impl_self_ty.clone(),
                    trait_context.clone(),
                    move |parser| {
                        item_impl
                            .items
                            .into_iter()
                            .filter(|item| !matches!(item, syn::ImplItem::Macro(_)))
                            .map(|item| match item {
                                syn::ImplItem::Fn(method) => {
                                    parser.parse_impl_method(method, &impl_self_ty)
                                }
                                syn::ImplItem::Type(item_type) => parser
                                    .parse_impl_associated_type(
                                        item_type,
                                        trait_context.as_deref(),
                                    ),
                                syn::ImplItem::Const(item_const) => {
                                    let const_name = if is_trait_impl {
                                        parser.qualify_trait_associated_item_name(
                                            &impl_self_ty,
                                            trait_context
                                                .as_deref()
                                                .expect("trait impl tracks its trait name"),
                                            &item_const.ident.to_string(),
                                        )
                                    } else {
                                        parser.qualify_inherent_associated_item_name(
                                            &impl_self_ty,
                                            &item_const.ident.to_string(),
                                        )
                                    };
                                    Ok(Item::Const {
                                        name: const_name,
                                        ty: parser.parse_type(&item_const.ty)?,
                                        value: parser.parse_expr(&item_const.expr)?,
                                    })
                                }
                                other => Err(Self::unsupported(
                                    "impl item",
                                    format!(
                                        "unsupported impl item `{}`",
                                        Self::impl_item_kind(&other)
                                    ),
                                )),
                            })
                            .collect::<Result<Vec<_>, _>>()
                    },
                )?;
                Ok(Item::Impl {
                    self_ty,
                    trait_name: trait_name.clone(),
                    items,
                    type_params: type_params.clone(),
                    const_params: const_params.clone(),
                })
            })
        })
    }

    fn parse_impl_associated_type(
        &mut self,
        item_type: syn::ImplItemType,
        trait_name: Option<&str>,
    ) -> Result<Item, SourceError> {
        let Some(trait_name) = trait_name else {
            return Err(Self::unsupported(
                "impl item",
                "inherent associated types are not yet supported",
            ));
        };

        let assoc_name = item_type.ident.to_string();
        if item_type.defaultness.is_some() {
            return Err(Self::unsupported(
                "impl item",
                format!("default associated type `{assoc_name}` in impl of trait `{trait_name}`"),
            ));
        }
        let generic_params = self.parse_generic_params(&item_type.generics)?;
        let assoc_type_params = generic_params
            .iter()
            .filter_map(|param| param.as_type_param().cloned())
            .collect::<Vec<_>>();

        self.with_type_params(&assoc_type_params, |parser| {
            let target = format!("associated type `{assoc_name}` in impl of trait `{trait_name}`");
            Ok(Item::ImplAssociatedType {
                name: assoc_name.clone(),
                ty: parser.parse_type(&item_type.ty)?,
                generic_params: generic_params.clone(),
                where_clause: parser.parse_where_clause(
                    item_type.generics.where_clause.as_ref(),
                    "impl item",
                    &target,
                )?,
            })
        })
    }

    fn parse_impl_method(
        &mut self,
        method: syn::ImplItemFn,
        self_ty: &RustType,
    ) -> Result<Item, SourceError> {
        let type_params = self.assign_type_param_ids(Self::parse_generics(&method.sig.generics)?);
        self.with_type_params(&type_params, |parser| {
            let params = method
                .sig
                .inputs
                .iter()
                .map(|arg| parser.parse_fn_arg(arg, Some(self_ty)))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Item::Fn {
                name: method.sig.ident.to_string(),
                params,
                ret: parser.parse_return_type(&method.sig.output)?,
                body: parser.parse_block(&method.block)?,
                is_unsafe: method.sig.unsafety.is_some(),
                is_async: method.sig.asyncness.is_some(),
                type_params: type_params.clone(),
            })
        })
    }

    fn parse_fn_arg(
        &mut self,
        arg: &syn::FnArg,
        self_ty: Option<&RustType>,
    ) -> Result<(String, RustType), SourceError> {
        match arg {
            syn::FnArg::Typed(pat_ty) => {
                let name = Self::pat_ident_name(&pat_ty.pat)?;
                Ok((name, self.parse_type(&pat_ty.ty)?))
            }
            syn::FnArg::Receiver(receiver) => {
                let self_ty = self_ty.ok_or_else(|| SourceError::Invalid {
                    context: "receiver",
                    detail: "receiver outside impl method".to_string(),
                })?;
                let ty = if let Some((_, lifetime)) = &receiver.reference {
                    RustType::Reference {
                        lifetime: lifetime
                            .as_ref()
                            .map_or_else(|| self.fresh_anon_lifetime(), Self::parse_lifetime),
                        mutability: if receiver.mutability.is_some() {
                            Mutability::Mutable
                        } else {
                            Mutability::Shared
                        },
                        inner: Box::new(self_ty.clone()),
                    }
                } else {
                    self_ty.clone()
                };
                Ok(("self".to_string(), ty))
            }
        }
    }

    fn parse_return_type(&mut self, ret: &syn::ReturnType) -> Result<RustType, SourceError> {
        match ret {
            syn::ReturnType::Default => Ok(RustType::Unit),
            syn::ReturnType::Type(_, ty) => self.parse_type(ty),
        }
    }

    fn qualify_inherent_associated_item_name(&self, self_ty: &RustType, item_name: &str) -> String {
        self.canonical_nominal_type_name(self_ty)
            .map(|type_name| format!("{type_name}::{item_name}"))
            .unwrap_or_else(|| item_name.to_string())
    }

    fn qualify_trait_associated_item_name(
        &self,
        self_ty: &RustType,
        trait_name: &str,
        item_name: &str,
    ) -> String {
        let type_name = self_ty.name().unwrap_or_else(|| "anonymous".to_string());
        format!("<{type_name} as {trait_name}>::{item_name}")
    }
}
