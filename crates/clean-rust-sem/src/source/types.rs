// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{parser::Parser, SourceError};
use crate::types::{ConstGenericArg, FloatType, IntType, Lifetime, Mutability, RustType, UintType};

impl Parser {
    pub(super) fn parse_type(&mut self, ty: &syn::Type) -> Result<RustType, SourceError> {
        match ty {
            syn::Type::Path(type_path) => self.parse_type_path(type_path),
            syn::Type::Reference(reference) => Ok(RustType::Reference {
                lifetime: reference
                    .lifetime
                    .as_ref()
                    .map_or_else(|| self.fresh_anon_lifetime(), Self::parse_lifetime),
                mutability: if reference.mutability.is_some() {
                    Mutability::Mutable
                } else {
                    Mutability::Shared
                },
                inner: Box::new(self.parse_type(&reference.elem)?),
            }),
            syn::Type::Ptr(ptr) => Ok(RustType::RawPtr {
                mutability: if ptr.mutability.is_some() {
                    Mutability::Mutable
                } else {
                    Mutability::Shared
                },
                inner: Box::new(self.parse_type(&ptr.elem)?),
            }),
            syn::Type::Array(array) => Ok(RustType::Array {
                element: Box::new(self.parse_type(&array.elem)?),
                len: self.parse_array_len_arg(&array.len)?,
            }),
            syn::Type::Slice(slice) => Ok(RustType::Slice {
                elem: Box::new(self.parse_type(&slice.elem)?),
            }),
            syn::Type::Tuple(tuple) => {
                if tuple.elems.is_empty() {
                    Ok(RustType::Unit)
                } else {
                    Ok(RustType::Tuple(
                        tuple
                            .elems
                            .iter()
                            .map(|elem| self.parse_type(elem))
                            .collect::<Result<Vec<_>, _>>()?,
                    ))
                }
            }
            syn::Type::BareFn(function) => Ok(RustType::Function {
                params: function
                    .inputs
                    .iter()
                    .map(|input| self.parse_type(&input.ty))
                    .collect::<Result<Vec<_>, _>>()?,
                ret: Box::new(match &function.output {
                    syn::ReturnType::Default => RustType::Unit,
                    syn::ReturnType::Type(_, ty) => self.parse_type(ty)?,
                }),
            }),
            syn::Type::Never(_) => Ok(RustType::Never),
            syn::Type::Paren(paren) => self.parse_type(&paren.elem),
            syn::Type::TraitObject(trait_object) => self.parse_dyn_trait_type(trait_object),
            syn::Type::ImplTrait(impl_trait) => self.parse_impl_trait_type(impl_trait),
            syn::Type::Infer(_) => Ok(RustType::Infer),
            syn::Type::Group(group) => self.parse_type(&group.elem),
            other => Err(Self::unsupported(
                "type",
                format!("unsupported type `{}`", Self::type_kind(other)),
            )),
        }
    }

    fn parse_type_path(&mut self, type_path: &syn::TypePath) -> Result<RustType, SourceError> {
        match &type_path.qself {
            Some(qself) => self.parse_projection_type(qself, &type_path.path),
            None => self.parse_path_type(&type_path.path),
        }
    }

    fn parse_path_type(&mut self, path: &syn::Path) -> Result<RustType, SourceError> {
        if let Some(self_ty) = self.parse_self_path_type(path)? {
            return Ok(self_ty);
        }
        let Some(segment) = path.segments.last() else {
            return Err(SourceError::Invalid {
                context: "type path",
                detail: "empty type path".to_string(),
            });
        };
        let name = segment.ident.to_string();
        if path.segments.len() == 1 {
            if let Some(type_param) = self.resolve_type_param(&name) {
                if !matches!(segment.arguments, syn::PathArguments::None) {
                    return Err(SourceError::Invalid {
                        context: "type parameter",
                        detail: format!(
                            "type parameter `{name}` does not accept generic arguments"
                        ),
                    });
                }
                return Ok(RustType::TypeParam(type_param));
            }
            if matches!(segment.arguments, syn::PathArguments::None) {
                if let Some(alias) = self.resolve_type_alias(&name)? {
                    return Ok(alias);
                }
            }
        }
        if let Some(ty) = Self::builtin_type(&name) {
            return Ok(ty);
        }
        if let Some(ty) = self.special_type(segment, &name)? {
            return Ok(ty);
        }
        let (type_args, lifetime_args, const_args) = self.generic_args(segment)?;
        Ok(RustType::Named {
            name: Self::path_to_string(path),
            type_args,
            lifetime_args,
            const_args,
        })
    }

    fn parse_self_path_type(&mut self, path: &syn::Path) -> Result<Option<RustType>, SourceError> {
        let Some(first) = path.segments.first() else {
            return Ok(None);
        };
        if first.ident != "Self" {
            return Ok(None);
        }
        if !matches!(first.arguments, syn::PathArguments::None) {
            return Err(Self::unsupported(
                "type",
                "`Self` paths with generic arguments are not yet supported",
            ));
        }

        match path.segments.len() {
            1 => {
                let Some(context) = &self.type_context else {
                    return Err(Self::unsupported(
                        "type",
                        "`Self` type is only supported inside trait or impl items",
                    ));
                };
                Ok(Some(context.self_ty.clone()))
            }
            2 => {
                let Some(context) = &self.type_context else {
                    return Err(Self::unsupported(
                        "type",
                        "`Self::Assoc` associated type projections require a trait context",
                    ));
                };
                let Some(trait_name) = &context.trait_name else {
                    return Err(Self::unsupported(
                        "type",
                        "`Self::Assoc` associated type projections require a trait context",
                    ));
                };

                let assoc_segment = path
                    .segments
                    .iter()
                    .nth(1)
                    .expect("len checked for `Self::Assoc` path");
                let self_ty = context.self_ty.clone();
                let trait_name = trait_name.to_string();
                let (assoc_type_args, assoc_lifetime_args, assoc_const_args) =
                    self.generic_args(assoc_segment)?;

                Ok(Some(RustType::TypeProjection {
                    self_ty: Box::new(self_ty),
                    trait_name,
                    assoc_name: assoc_segment.ident.to_string(),
                    assoc_type_args,
                    assoc_lifetime_args,
                    const_args: assoc_const_args,
                }))
            }
            _ => Err(Self::unsupported(
                "type",
                "nested `Self` paths beyond `Self::Assoc` are not yet supported",
            )),
        }
    }

    fn parse_projection_type(
        &mut self,
        qself: &syn::QSelf,
        path: &syn::Path,
    ) -> Result<RustType, SourceError> {
        if qself.as_token.is_none() || qself.position == 0 {
            return Err(Self::unsupported(
                "type",
                "only `<T as Trait>::Assoc` associated type projections are supported",
            ));
        }
        if path.segments.len() != qself.position + 1 {
            return Err(Self::unsupported(
                "type",
                "nested qualified paths beyond `<T as Trait>::Assoc` are not yet supported",
            ));
        }

        for segment in path.segments.iter().take(qself.position) {
            if !matches!(segment.arguments, syn::PathArguments::None) {
                return Err(Self::unsupported(
                    "type",
                    "qualified trait paths with generic arguments are not yet supported",
                ));
            }
        }

        let assoc_segment = path.segments.last().ok_or_else(|| SourceError::Invalid {
            context: "type projection",
            detail: "missing associated type segment".to_string(),
        })?;
        let (assoc_type_args, assoc_lifetime_args, assoc_const_args) =
            self.generic_args(assoc_segment)?;

        let trait_segment = path
            .segments
            .iter()
            .nth(qself.position - 1)
            .ok_or_else(|| SourceError::Invalid {
                context: "type projection",
                detail: "missing trait segment".to_string(),
            })?;

        Ok(RustType::TypeProjection {
            self_ty: Box::new(self.parse_type(&qself.ty)?),
            trait_name: trait_segment.ident.to_string(),
            assoc_name: assoc_segment.ident.to_string(),
            assoc_type_args,
            assoc_lifetime_args,
            const_args: assoc_const_args,
        })
    }

    fn builtin_type(name: &str) -> Option<RustType> {
        Some(match name {
            "bool" => RustType::Bool,
            "char" => RustType::Char,
            "str" => RustType::Str,
            "u8" => RustType::Uint(UintType::U8),
            "u16" => RustType::Uint(UintType::U16),
            "u32" => RustType::Uint(UintType::U32),
            "u64" => RustType::Uint(UintType::U64),
            "u128" => RustType::Uint(UintType::U128),
            "usize" => RustType::Uint(UintType::Usize),
            "i8" => RustType::Int(IntType::I8),
            "i16" => RustType::Int(IntType::I16),
            "i32" => RustType::Int(IntType::I32),
            "i64" => RustType::Int(IntType::I64),
            "i128" => RustType::Int(IntType::I128),
            "isize" => RustType::Int(IntType::Isize),
            "f32" => RustType::Float(FloatType::F32),
            "f64" => RustType::Float(FloatType::F64),
            _ => return None,
        })
    }

    fn special_type(
        &mut self,
        segment: &syn::PathSegment,
        name: &str,
    ) -> Result<Option<RustType>, SourceError> {
        match name {
            "Option" => Ok(Some(RustType::Option {
                inner: Box::new(self.single_type_arg(segment, "Option")?),
            })),
            "Vec" => Ok(Some(RustType::Vec {
                element: Box::new(self.single_type_arg(segment, "Vec")?),
            })),
            "Box" => Ok(Some(RustType::Box {
                inner: Box::new(self.single_type_arg(segment, "Box")?),
            })),
            "Pin" => Ok(Some(RustType::Pin {
                inner: Box::new(self.single_type_arg(segment, "Pin")?),
            })),
            "Result" => self.parse_result_type(segment).map(Some),
            _ => Ok(None),
        }
    }

    fn parse_result_type(&mut self, segment: &syn::PathSegment) -> Result<RustType, SourceError> {
        let mut args = self.type_args(segment)?;
        if args.len() != 2 {
            return Err(SourceError::Invalid {
                context: "type",
                detail: format!("Result expects 2 type arguments, got {}", args.len()),
            });
        }
        let err = args.pop().expect("len checked");
        let ok = args.pop().expect("len checked");
        Ok(RustType::Result {
            ok: Box::new(ok),
            err: Box::new(err),
        })
    }

    fn type_args(&mut self, segment: &syn::PathSegment) -> Result<Vec<RustType>, SourceError> {
        let (type_args, lifetime_args, const_args) = self.generic_args(segment)?;
        if !lifetime_args.is_empty() {
            return Err(Self::unsupported(
                "type argument",
                "lifetime arguments are not accepted here",
            ));
        }
        if !const_args.is_empty() {
            return Err(Self::unsupported(
                "type argument",
                "const arguments are not accepted here",
            ));
        }
        Ok(type_args)
    }

    fn single_type_arg(
        &mut self,
        segment: &syn::PathSegment,
        type_name: &str,
    ) -> Result<RustType, SourceError> {
        let args = self.type_args(segment)?;
        if args.len() != 1 {
            return Err(SourceError::Invalid {
                context: "type argument",
                detail: format!("{type_name} expects 1 type argument, got {}", args.len()),
            });
        }
        Ok(args.into_iter().next().expect("len checked"))
    }

    fn generic_args(
        &mut self,
        segment: &syn::PathSegment,
    ) -> Result<(Vec<RustType>, Vec<Lifetime>, Vec<ConstGenericArg>), SourceError> {
        match &segment.arguments {
            syn::PathArguments::None => Ok((Vec::new(), Vec::new(), Vec::new())),
            syn::PathArguments::AngleBracketed(args) => {
                let mut type_args = Vec::new();
                let mut lifetime_args = Vec::new();
                let mut const_args = Vec::new();
                for arg in &args.args {
                    match arg {
                        syn::GenericArgument::Type(ty) => type_args.push(self.parse_type(ty)?),
                        syn::GenericArgument::Lifetime(lifetime) => {
                            lifetime_args.push(Self::parse_lifetime(lifetime));
                        }
                        syn::GenericArgument::Const(expr) => {
                            const_args.push(self.parse_const_generic_arg(expr)?);
                        }
                        _ => {
                            return Err(Self::unsupported(
                                "generic argument",
                                "associated generic arguments are not yet supported",
                            ))
                        }
                    }
                }
                Ok((type_args, lifetime_args, const_args))
            }
            syn::PathArguments::Parenthesized(parens) => {
                let params = parens
                    .inputs
                    .iter()
                    .map(|ty| self.parse_type(ty))
                    .collect::<Result<Vec<_>, _>>()?;
                let ret = match &parens.output {
                    syn::ReturnType::Default => RustType::Unit,
                    syn::ReturnType::Type(_, ty) => self.parse_type(ty)?,
                };
                Ok((
                    vec![RustType::Function {
                        params,
                        ret: Box::new(ret),
                    }],
                    Vec::new(),
                    Vec::new(),
                ))
            }
        }
    }

    fn parse_dyn_trait_type(
        &mut self,
        trait_object: &syn::TypeTraitObject,
    ) -> Result<RustType, SourceError> {
        let mut traits = Vec::new();
        for bound in &trait_object.bounds {
            match bound {
                syn::TypeParamBound::Trait(trait_bound) => {
                    traits.push(Self::plain_trait_bound_name(
                        trait_bound,
                        "type",
                        "dyn trait bound",
                    )?);
                }
                syn::TypeParamBound::Lifetime(_) => {}
                _ => {}
            }
        }
        let Some((trait_name, auto_traits)) = traits.split_first() else {
            return Err(Self::unsupported(
                "type",
                "dyn trait object with no trait bounds",
            ));
        };
        Ok(RustType::DynTrait {
            trait_name: trait_name.clone(),
            auto_traits: auto_traits.to_vec(),
        })
    }

    fn parse_impl_trait_type(
        &mut self,
        impl_trait: &syn::TypeImplTrait,
    ) -> Result<RustType, SourceError> {
        let mut traits = Vec::new();
        for bound in &impl_trait.bounds {
            match bound {
                syn::TypeParamBound::Trait(trait_bound) => {
                    traits.push(Self::plain_trait_bound_name(
                        trait_bound,
                        "type",
                        "impl trait bound",
                    )?);
                }
                syn::TypeParamBound::Lifetime(_) => {}
                _ => {}
            }
        }
        if traits.is_empty() {
            return Err(Self::unsupported("type", "impl trait with no trait bounds"));
        }
        Ok(RustType::ImplTrait { traits })
    }
}
