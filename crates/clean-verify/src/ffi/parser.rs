// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parsing helpers for converting Rust source fragments into FFI boundary
//! specifications via `syn`.

use syn::{
    FnArg, ForeignItem, ForeignItemFn, GenericArgument, Item, ItemEnum, ItemForeignMod, ItemStruct,
    ItemType, ItemUnion, Lit, Pat, PathArguments, ReturnType, Type,
};

use super::error::FfiBoundaryParseError;
use super::helpers::is_ffi_primitive_name;
use super::types::{
    FfiBoundarySpec, FfiEnumVariant, FfiExternBlock, FfiField, FfiFunctionContract, FfiParam,
    FfiTypeDecl, FfiTypeDeclKind, FfiTypeRef,
};

/// Parse a Rust source fragment into an [`FfiBoundarySpec`].
pub(crate) fn parse_source(source: &str) -> Result<FfiBoundarySpec, FfiBoundaryParseError> {
    let file = syn::parse_file(source)
        .map_err(|err| FfiBoundaryParseError::ParseSource(err.to_string()))?;

    let mut spec = FfiBoundarySpec::default();
    for item in &file.items {
        match item {
            Item::Struct(item) => spec.insert_type(parse_struct_decl(item)?)?,
            Item::Union(item) => spec.insert_type(parse_union_decl(item)?)?,
            Item::Enum(item) => spec.insert_type(parse_enum_decl(item)?)?,
            Item::Type(item) => spec.insert_type(parse_alias_decl(item))?,
            Item::ForeignMod(item) => spec.extern_blocks.push(parse_extern_block(item)),
            _ => {}
        }
    }

    Ok(spec)
}

fn parse_struct_decl(item: &ItemStruct) -> Result<FfiTypeDecl, FfiBoundaryParseError> {
    Ok(FfiTypeDecl {
        name: item.ident.to_string(),
        repr_c: has_repr_c(&item.attrs, item.ident.to_string())?,
        is_generic: !item.generics.params.is_empty(),
        kind: FfiTypeDeclKind::Struct {
            fields: parse_fields(&item.fields),
        },
    })
}

fn parse_union_decl(item: &ItemUnion) -> Result<FfiTypeDecl, FfiBoundaryParseError> {
    let fields = item
        .fields
        .named
        .iter()
        .map(|field| FfiField {
            name: field.ident.as_ref().map(ToString::to_string),
            ty: parse_type(&field.ty),
        })
        .collect();

    Ok(FfiTypeDecl {
        name: item.ident.to_string(),
        repr_c: has_repr_c(&item.attrs, item.ident.to_string())?,
        is_generic: !item.generics.params.is_empty(),
        kind: FfiTypeDeclKind::Union { fields },
    })
}

fn parse_enum_decl(item: &ItemEnum) -> Result<FfiTypeDecl, FfiBoundaryParseError> {
    let variants = item
        .variants
        .iter()
        .map(|variant| FfiEnumVariant {
            name: variant.ident.to_string(),
            fields: parse_fields(&variant.fields),
        })
        .collect();

    Ok(FfiTypeDecl {
        name: item.ident.to_string(),
        repr_c: has_repr_c(&item.attrs, item.ident.to_string())?,
        is_generic: !item.generics.params.is_empty(),
        kind: FfiTypeDeclKind::Enum { variants },
    })
}

fn parse_alias_decl(item: &ItemType) -> FfiTypeDecl {
    FfiTypeDecl {
        name: item.ident.to_string(),
        repr_c: false,
        is_generic: !item.generics.params.is_empty(),
        kind: FfiTypeDeclKind::Alias {
            target: parse_type(&item.ty),
        },
    }
}

pub(crate) fn parse_extern_block(item: &ItemForeignMod) -> FfiExternBlock {
    let abi = abi_name(&item.abi.name);
    let functions = item
        .items
        .iter()
        .filter_map(|item| match item {
            ForeignItem::Fn(function) => Some(parse_foreign_fn(function, &abi)),
            _ => None,
        })
        .collect();

    FfiExternBlock { abi, functions }
}

fn parse_foreign_fn(item: &ForeignItemFn, abi: &str) -> FfiFunctionContract {
    let inputs = item
        .sig
        .inputs
        .iter()
        .enumerate()
        .filter_map(|(index, arg)| match arg {
            FnArg::Typed(pat_ty) => Some(FfiParam {
                name: match &*pat_ty.pat {
                    Pat::Ident(ident) => ident.ident.to_string(),
                    _ => format!("arg{index}"),
                },
                ty: parse_type(&pat_ty.ty),
            }),
            FnArg::Receiver(_) => None,
        })
        .collect();

    let output = match &item.sig.output {
        ReturnType::Default => None,
        ReturnType::Type(_, ty) => Some(parse_type(ty)),
    };

    FfiFunctionContract {
        name: item.sig.ident.to_string(),
        abi: abi.to_string(),
        inputs,
        output,
        variadic: item.sig.variadic.is_some(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
    }
}

fn parse_fields(fields: &syn::Fields) -> Vec<FfiField> {
    match fields {
        syn::Fields::Named(fields) => fields
            .named
            .iter()
            .map(|field| FfiField {
                name: field.ident.as_ref().map(ToString::to_string),
                ty: parse_type(&field.ty),
            })
            .collect(),
        syn::Fields::Unnamed(fields) => fields
            .unnamed
            .iter()
            .map(|field| FfiField {
                name: None,
                ty: parse_type(&field.ty),
            })
            .collect(),
        syn::Fields::Unit => Vec::new(),
    }
}

pub(crate) fn parse_type(ty: &Type) -> FfiTypeRef {
    match ty {
        Type::Path(type_path) => parse_path_type(type_path),
        Type::Ptr(ptr) => FfiTypeRef::RawPointer {
            mutable: ptr.mutability.is_some(),
            inner: Box::new(parse_type(&ptr.elem)),
        },
        Type::Reference(reference) => FfiTypeRef::Reference {
            mutable: reference.mutability.is_some(),
            lifetime: reference.lifetime.as_ref().map(ToString::to_string),
            inner: Box::new(parse_type(&reference.elem)),
        },
        Type::Array(array) => FfiTypeRef::Array {
            inner: Box::new(parse_type(&array.elem)),
            len: render_expr(&array.len),
        },
        Type::Slice(slice) => FfiTypeRef::Slice(Box::new(parse_type(&slice.elem))),
        Type::Tuple(tuple) if tuple.elems.is_empty() => FfiTypeRef::Unit,
        Type::Tuple(tuple) => FfiTypeRef::Tuple(tuple.elems.iter().map(parse_type).collect()),
        Type::BareFn(function) => {
            let inputs = function
                .inputs
                .iter()
                .map(|arg| parse_type(&arg.ty))
                .collect();
            let output = match &function.output {
                ReturnType::Default => None,
                ReturnType::Type(_, ty) => Some(Box::new(parse_type(ty))),
            };
            FfiTypeRef::BareFunction {
                abi: abi_name(&function.abi.as_ref().and_then(|abi| abi.name.clone())),
                inputs,
                output,
            }
        }
        _ => FfiTypeRef::Unsupported(render_type(ty)),
    }
}

fn parse_path_type(type_path: &syn::TypePath) -> FfiTypeRef {
    if type_path.qself.is_some() {
        return FfiTypeRef::Unsupported(render_type(&Type::Path(type_path.clone())));
    }

    let has_generics = type_path
        .path
        .segments
        .iter()
        .any(|segment| !matches!(segment.arguments, PathArguments::None));
    let rendered = render_path(&type_path.path);

    if has_generics {
        return FfiTypeRef::Unsupported(rendered);
    }

    let leaf = type_path
        .path
        .segments
        .last()
        .map(|segment| segment.ident.to_string())
        .unwrap_or(rendered.clone());
    if is_ffi_primitive_name(&leaf) {
        FfiTypeRef::Primitive(leaf)
    } else {
        FfiTypeRef::Named(rendered)
    }
}

fn abi_name(name: &Option<syn::LitStr>) -> String {
    name.as_ref()
        .map(syn::LitStr::value)
        .unwrap_or_else(|| "C".to_string())
}

fn has_repr_c(attrs: &[syn::Attribute], item: String) -> Result<bool, FfiBoundaryParseError> {
    let mut repr_c = false;
    for attr in attrs {
        if attr.path().is_ident("repr") {
            attr.parse_nested_meta(|meta| {
                if meta.path.is_ident("C") {
                    repr_c = true;
                }
                Ok(())
            })
            .map_err(|err| FfiBoundaryParseError::MalformedAttribute {
                item: item.clone(),
                detail: err.to_string(),
            })?;
        }
    }
    Ok(repr_c)
}

fn render_type(ty: &Type) -> String {
    match ty {
        Type::Path(type_path) => render_path(&type_path.path),
        Type::Ptr(ptr) => {
            let qualifier = if ptr.mutability.is_some() {
                "mut"
            } else {
                "const"
            };
            format!("*{qualifier} {}", render_type(&ptr.elem))
        }
        Type::Reference(reference) => match (reference.mutability.is_some(), &reference.lifetime) {
            (true, Some(lifetime)) => format!("&{lifetime} mut {}", render_type(&reference.elem)),
            (false, Some(lifetime)) => format!("&{lifetime} {}", render_type(&reference.elem)),
            (true, None) => format!("&mut {}", render_type(&reference.elem)),
            (false, None) => format!("&{}", render_type(&reference.elem)),
        },
        Type::Array(array) => format!(
            "[{}; {}]",
            render_type(&array.elem),
            render_expr(&array.len)
        ),
        Type::Slice(slice) => format!("[{}]", render_type(&slice.elem)),
        Type::Tuple(tuple) => {
            let rendered = tuple
                .elems
                .iter()
                .map(render_type)
                .collect::<Vec<_>>()
                .join(", ");
            format!("({rendered})")
        }
        Type::BareFn(function) => {
            let abi = abi_name(&function.abi.as_ref().and_then(|abi| abi.name.clone()));
            let rendered_inputs = function
                .inputs
                .iter()
                .map(|arg| render_type(&arg.ty))
                .collect::<Vec<_>>()
                .join(", ");
            match &function.output {
                ReturnType::Default => format!("extern \"{abi}\" fn({rendered_inputs})"),
                ReturnType::Type(_, output) => {
                    format!(
                        "extern \"{abi}\" fn({rendered_inputs}) -> {}",
                        render_type(output)
                    )
                }
            }
        }
        _ => "unsupported-type".to_string(),
    }
}

fn render_path(path: &syn::Path) -> String {
    path.segments
        .iter()
        .map(render_path_segment)
        .collect::<Vec<_>>()
        .join("::")
}

fn render_path_segment(segment: &syn::PathSegment) -> String {
    match &segment.arguments {
        PathArguments::None => segment.ident.to_string(),
        PathArguments::AngleBracketed(args) => {
            let rendered = args
                .args
                .iter()
                .map(|arg| match arg {
                    GenericArgument::Type(ty) => render_type(ty),
                    GenericArgument::Lifetime(lifetime) => lifetime.to_string(),
                    GenericArgument::Const(expr) => render_expr(expr),
                    _ => "...".to_string(),
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("{}<{rendered}>", segment.ident)
        }
        PathArguments::Parenthesized(args) => {
            let rendered_inputs = args
                .inputs
                .iter()
                .map(render_type)
                .collect::<Vec<_>>()
                .join(", ");
            match &args.output {
                ReturnType::Default => format!("{}({rendered_inputs})", segment.ident),
                ReturnType::Type(_, output) => {
                    format!(
                        "{}({rendered_inputs}) -> {}",
                        segment.ident,
                        render_type(output)
                    )
                }
            }
        }
    }
}

fn render_expr(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(expr) => match &expr.lit {
            Lit::Int(value) => value.base10_digits().to_string(),
            Lit::Bool(value) => value.value.to_string(),
            Lit::Char(value) => value.value().to_string(),
            Lit::Str(value) => value.value(),
            _ => "_".to_string(),
        },
        syn::Expr::Path(path) => render_path(&path.path),
        _ => "_".to_string(),
    }
}
