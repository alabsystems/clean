// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Semantic AST to VIR lowering.

mod async_lowering;
mod block_lowering;
mod calls;
mod closure_lowering;
mod coercion_autoderef;
mod coercion_lowering;
mod context;
mod context_state;
mod control_flow;
mod destination_init;
mod enum_construction;
mod enum_support;
mod error;
mod future_type_inference;
mod inline_asm_lowering;
mod let_lowering;
mod loop_support;
mod match_lowering;
mod ops;
mod pattern_binding;
mod retag;
mod rvalue_lowering;
mod scoped_symbols;
mod scoped_type_inference;
mod slice_lowering;
mod type_helpers;
mod type_inference;
mod typing;
mod unwind_cleanup;

use crate::expr::{Expr, Item};
use crate::nll::NllResult;
use crate::types::RustType;
use crate::vir::Body;
use std::collections::BTreeMap;

pub use error::VirLoweringError;

#[derive(Debug, Clone, Default)]
pub struct LoweredProgram {
    pub functions: BTreeMap<String, Body>,
}

#[derive(Debug, Clone)]
struct ImplContext {
    self_ty_name: String,
    trait_name: Option<String>,
}

impl LoweredProgram {
    #[must_use]
    pub fn check_borrows(&self) -> BTreeMap<String, NllResult> {
        self.functions
            .iter()
            .map(|(name, body)| (name.clone(), crate::nll::check_body(body)))
            .collect()
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct ProgramSymbols {
    struct_fields: BTreeMap<String, BTreeMap<String, RustType>>,
    fn_sigs: BTreeMap<String, FnSig>,
    method_aliases: BTreeMap<String, String>,
    enum_variants: BTreeMap<String, BTreeMap<String, EnumVariantInfo>>,
    /// Trait method signatures keyed by `trait_name` then `method_name`.
    ///
    /// Populated from `Item::TraitDef`. Unlike `fn_sigs` (which records the
    /// signatures of concrete `impl` bodies under their canonical qualified
    /// names), these are the trait *declaration's* method signatures and are
    /// the only signatures available when dispatching through a `dyn Trait`
    /// trait object, where the concrete implementing type is erased.
    trait_method_sigs: BTreeMap<String, BTreeMap<String, TraitMethodSig>>,
}

#[derive(Debug, Clone)]
pub(crate) struct FnSig {
    pub(crate) params: Vec<(String, RustType)>,
    pub(crate) ret: RustType,
    pub(crate) future_output: Option<RustType>,
}

/// A trait method's declared signature, used for `dyn Trait` dynamic dispatch.
///
/// The receiver mode (`self` / `&self` / `&mut self`) is kept distinct from the
/// explicit parameters because, for a trait object, the receiver operand is
/// constructed from the trait-object value itself rather than from an explicit
/// argument expression.
#[derive(Debug, Clone)]
pub(crate) struct TraitMethodSig {
    pub(crate) receiver: crate::types::ReceiverMode,
    pub(crate) params: Vec<RustType>,
    pub(crate) ret: RustType,
    /// For `async fn` trait methods, the awaited output type (the declared
    /// `ret` before it is wrapped into an `impl Future`).
    pub(crate) future_output: Option<RustType>,
}

#[derive(Debug, Clone)]
pub(crate) struct EnumVariantInfo {
    pub(crate) variant_index: u32,
    pub(crate) discriminant: u128,
    pub(crate) payload: EnumPayloadInfo,
}

#[derive(Debug, Clone)]
pub(crate) enum EnumPayloadInfo {
    Unit,
    Tuple(Vec<RustType>),
    Struct {
        type_name: String,
        fields: Vec<(String, RustType)>,
    },
}

impl EnumPayloadInfo {
    pub(crate) fn payload_type(&self) -> RustType {
        match self {
            Self::Unit => RustType::Unit,
            Self::Tuple(fields) => RustType::Tuple(fields.clone()),
            Self::Struct { type_name, .. } => RustType::Named {
                name: type_name.clone(),
                type_args: Vec::new(),
                lifetime_args: Vec::new(),
                const_args: Vec::new(),
            },
        }
    }
}

impl ProgramSymbols {
    pub(crate) fn collect(items: &[Item]) -> Self {
        let mut symbols = Self::default();
        symbols.collect_into(items, None);
        symbols
    }

    fn collect_into(&mut self, items: &[Item], impl_context: Option<&ImplContext>) {
        for item in items {
            match item {
                Item::Fn {
                    name,
                    params,
                    ret,
                    is_async,
                    ..
                } => self.collect_fn_sig(impl_context, name, params, ret, *is_async),
                Item::Struct { name, fields, .. } | Item::Union { name, fields, .. } => {
                    self.collect_struct_fields(name, fields)
                }
                Item::Enum { name, variants, .. } => self.collect_enum_variants(name, variants),
                Item::TraitDef(def) => self.collect_trait_method_sigs(def),
                Item::Impl {
                    self_ty,
                    trait_name,
                    items,
                    ..
                } => {
                    let nested_context = ImplContext {
                        self_ty_name: self_ty.name().unwrap_or_else(|| "anonymous".to_string()),
                        trait_name: trait_name.clone(),
                    };
                    self.collect_into(items, Some(&nested_context));
                }
                _ => {}
            }
        }
    }

    fn collect_fn_sig(
        &mut self,
        impl_context: Option<&ImplContext>,
        name: &str,
        params: &[(String, RustType)],
        ret: &RustType,
        is_async: bool,
    ) {
        let qualified = qualified_function_name(impl_context, name);
        self.fn_sigs.insert(
            qualified.clone(),
            FnSig {
                params: params.to_vec(),
                ret: lowered_function_return_type(ret, is_async),
                future_output: is_async.then(|| ret.clone()),
            },
        );
        if let Some(ImplContext {
            self_ty_name,
            trait_name,
        }) = impl_context
        {
            let alias = format!("{self_ty_name}::{name}");
            if trait_name.is_some() {
                self.method_aliases.entry(alias).or_insert(qualified);
            } else {
                // Inherent methods outrank trait methods for method-call syntax.
                self.method_aliases.insert(alias, qualified);
            }
        }
    }

    fn collect_struct_fields(&mut self, name: &str, fields: &[(String, RustType)]) {
        let field_types = fields
            .iter()
            .map(|(field_name, field_ty)| (field_name.clone(), field_ty.clone()))
            .collect();
        self.struct_fields.insert(name.to_string(), field_types);
    }

    /// Record a trait's method signatures so calls dispatched through a
    /// `dyn Trait` trait object can recover the receiver/parameter/return
    /// types that the erased trait-object type no longer carries.
    fn collect_trait_method_sigs(&mut self, def: &crate::stmt::TraitDef) {
        let method_sigs = def
            .methods
            .iter()
            .map(|method| {
                (
                    method.name.clone(),
                    TraitMethodSig {
                        receiver: method.receiver,
                        params: method.params.clone(),
                        ret: lowered_function_return_type(&method.ret, method.is_async),
                        future_output: method.is_async.then(|| method.ret.clone()),
                    },
                )
            })
            .collect();
        self.trait_method_sigs.insert(def.name.clone(), method_sigs);
    }

    /// Look up a trait method's declared signature for `dyn Trait` dispatch.
    pub(crate) fn trait_method_sig(
        &self,
        trait_name: &str,
        method: &str,
    ) -> Option<&TraitMethodSig> {
        self.trait_method_sigs
            .get(trait_name)
            .and_then(|methods| methods.get(method))
    }

    fn collect_enum_variants(&mut self, enum_name: &str, variants: &[crate::types::EnumVariant]) {
        let mut next_discriminant: i128 = 0;
        let mut variant_map = BTreeMap::new();
        for (variant_index, variant) in variants.iter().enumerate() {
            let (variant_name, discriminant, payload) =
                self.collect_enum_variant(enum_name, variant, next_discriminant);
            next_discriminant = discriminant.saturating_add(1);
            variant_map.insert(
                variant_name,
                EnumVariantInfo {
                    variant_index: variant_index as u32,
                    discriminant: discriminant as u128,
                    payload,
                },
            );
        }
        self.enum_variants
            .insert(enum_name.to_string(), variant_map);
    }

    fn collect_enum_variant(
        &mut self,
        enum_name: &str,
        variant: &crate::types::EnumVariant,
        next_discriminant: i128,
    ) -> (String, i128, EnumPayloadInfo) {
        match variant {
            crate::types::EnumVariant::Unit { name, discriminant } => (
                name.clone(),
                discriminant.unwrap_or(next_discriminant),
                EnumPayloadInfo::Unit,
            ),
            crate::types::EnumVariant::Tuple {
                name,
                fields,
                discriminant,
            } => (
                name.clone(),
                discriminant.unwrap_or(next_discriminant),
                EnumPayloadInfo::Tuple(fields.clone()),
            ),
            crate::types::EnumVariant::Struct {
                name: variant_name,
                fields,
                discriminant,
            } => {
                let type_name = format!("{enum_name}::{variant_name}");
                let field_types: Vec<_> = fields
                    .iter()
                    .map(|field| (field.name.clone(), field.ty.clone()))
                    .collect();
                self.struct_fields
                    .insert(type_name.clone(), field_types.iter().cloned().collect());
                (
                    variant_name.clone(),
                    discriminant.unwrap_or(next_discriminant),
                    EnumPayloadInfo::Struct {
                        type_name,
                        fields: field_types,
                    },
                )
            }
        }
    }

    pub(crate) fn field_type(&self, type_name: &str, field: &str) -> Option<&RustType> {
        self.struct_fields
            .get(type_name)
            .and_then(|fields| fields.get(field))
    }

    pub(crate) fn fn_ret_type(&self, name: &str) -> Option<&RustType> {
        self.resolve_fn_sig(name).map(|sig| &sig.ret)
    }

    pub(crate) fn fn_type(&self, name: &str) -> Option<RustType> {
        self.resolve_fn_sig(name).map(|sig| RustType::Function {
            params: sig.params.iter().map(|(_, ty)| ty.clone()).collect(),
            ret: Box::new(sig.ret.clone()),
        })
    }

    pub(crate) fn fn_future_output_type(&self, name: &str) -> Option<&RustType> {
        self.resolve_fn_sig(name)
            .and_then(|sig| sig.future_output.as_ref())
    }

    pub(crate) fn fn_param_types(&self, name: &str) -> Option<Vec<RustType>> {
        self.resolve_fn_sig(name)
            .map(|sig| sig.params.iter().map(|(_, ty)| ty.clone()).collect())
    }

    pub(crate) fn resolve_method_name(&self, type_name: &str, method: &str) -> String {
        let alias = format!("{type_name}::{method}");
        self.method_aliases.get(&alias).cloned().unwrap_or(alias)
    }

    pub(crate) fn enum_variant(&self, enum_name: &str, variant: &str) -> Option<&EnumVariantInfo> {
        self.enum_variants
            .get(enum_name)
            .and_then(|variants| variants.get(variant))
    }

    fn resolve_fn_sig(&self, name: &str) -> Option<&FnSig> {
        self.fn_sigs.get(name).or_else(|| {
            self.method_aliases
                .get(name)
                .and_then(|canonical| self.fn_sigs.get(canonical))
        })
    }
}

pub(crate) fn lower_items(items: &[Item]) -> Result<LoweredProgram, VirLoweringError> {
    let symbols = ProgramSymbols::collect(items);
    let mut functions = BTreeMap::new();
    lower_item_list(items, None, &symbols, &mut functions)?;
    Ok(LoweredProgram { functions })
}

fn lower_item_list(
    items: &[Item],
    impl_context: Option<&ImplContext>,
    symbols: &ProgramSymbols,
    functions: &mut BTreeMap<String, Body>,
) -> Result<(), VirLoweringError> {
    for item in items {
        match item {
            Item::Fn {
                name,
                params,
                ret,
                body,
                is_async,
                ..
            } => {
                let qualified_name = qualified_function_name(impl_context, name);
                let lowered_ret = lowered_function_return_type(ret, *is_async);
                let synthetic_async_body;
                let lowered_body = if *is_async {
                    synthetic_async_body = Expr::Async {
                        capture_by_value: true,
                        body: Box::new(body.clone()),
                    };
                    &synthetic_async_body
                } else {
                    body
                };
                let (lowered, closure_bodies) = context::lower_function_with_closures(
                    &qualified_name,
                    params,
                    &lowered_ret,
                    lowered_body,
                    symbols,
                )?;
                functions.insert(qualified_name, lowered);
                for (closure_name, closure_body) in closure_bodies {
                    functions.insert(closure_name, closure_body);
                }
            }
            Item::Impl {
                self_ty,
                trait_name,
                items,
                ..
            } => {
                let nested_context = ImplContext {
                    self_ty_name: self_ty.name().unwrap_or_else(|| "anonymous".to_string()),
                    trait_name: trait_name.clone(),
                };
                lower_item_list(items, Some(&nested_context), symbols, functions)?;
            }
            _ => {}
        }
    }

    Ok(())
}

fn qualified_function_name(impl_context: Option<&ImplContext>, name: &str) -> String {
    match impl_context {
        Some(ImplContext {
            self_ty_name,
            trait_name: Some(trait_name),
        }) => format!("<{self_ty_name} as {trait_name}>::{name}"),
        Some(ImplContext {
            self_ty_name,
            trait_name: None,
        }) => format!("{self_ty_name}::{name}"),
        None => name.to_string(),
    }
}

fn lowered_function_return_type(ret: &RustType, is_async: bool) -> RustType {
    if is_async {
        RustType::ImplTrait {
            traits: vec!["Future".to_string()],
        }
    } else {
        ret.clone()
    }
}
