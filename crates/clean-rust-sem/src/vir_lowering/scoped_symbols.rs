// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Block-scoped symbol visibility for VIR lowering.

use super::context::FunctionLoweringContext;
use super::{
    lowered_function_return_type, EnumVariantInfo, FnSig, ProgramSymbols, VirLoweringError,
};
use crate::expr::Expr;
use crate::item::Item;
use crate::types::RustType;
use std::collections::BTreeMap;

#[derive(Debug, Clone, Default)]
pub(super) struct SymbolScope {
    struct_fields: BTreeMap<String, BTreeMap<String, RustType>>,
    enum_variants: BTreeMap<String, BTreeMap<String, EnumVariantInfo>>,
    fn_sigs: BTreeMap<String, FnSig>,
}

impl<'a> FunctionLoweringContext<'a> {
    /// Register a block-scoped item's symbols (struct fields, enum variants,
    /// function signatures) into the current lexical scope so that later
    /// statements in the same block can resolve references to it.
    ///
    /// This records only declarations, never code. Function *bodies* are
    /// lowered separately by [`Self::register_and_lower_scoped_item`]; the
    /// signature-only registration here is what the type-inference walk
    /// (`observe_stmt_for_type_inference`) needs and what forked contexts
    /// reuse without paying to re-lower bodies they would discard.
    pub(super) fn register_scoped_item(&mut self, item: &Item) -> Result<(), VirLoweringError> {
        match item {
            Item::Struct { .. } | Item::Enum { .. } | Item::Union { .. } => {
                let mut scoped_symbols = ProgramSymbols::default();
                scoped_symbols.collect_into(std::slice::from_ref(item), None);
                let scope = self.current_scope_mut()?;
                scope
                    .symbols
                    .struct_fields
                    .extend(scoped_symbols.struct_fields);
                scope
                    .symbols
                    .enum_variants
                    .extend(scoped_symbols.enum_variants);
                Ok(())
            }
            Item::Fn {
                name,
                params,
                ret,
                is_async,
                ..
            } => {
                // A block-scoped `fn` is a plain item, not a closure: it does
                // not capture the enclosing environment. Its name is visible
                // only within the enclosing block, so we key its signature in
                // the current scope rather than the program-wide table.
                let sig = FnSig {
                    params: params.clone(),
                    ret: lowered_function_return_type(ret, *is_async),
                    future_output: is_async.then(|| ret.clone()),
                };
                self.current_scope_mut()?
                    .symbols
                    .fn_sigs
                    .insert(name.clone(), sig);
                Ok(())
            }
            // Type aliases are resolved structurally during source ingestion
            // (the alias name is substituted for its underlying type before
            // lowering), so a block-scoped alias introduces no symbol here.
            Item::TypeAlias { .. } => Ok(()),
            other => Err(VirLoweringError::Unsupported {
                context: "block item",
                detail: format!("nested item lowering is not implemented for `{other:?}`"),
            }),
        }
    }

    /// Register a block-scoped item and, for function items, additionally lower
    /// the function body so it appears in the program's function table.
    ///
    /// This is the real-lowering entry point (driven from `lower_stmt`). The
    /// nested function is lowered exactly like a top-level function — a fresh
    /// lowering context keyed by its name, with no environment capture — using
    /// the currently visible symbols so it can call sibling block-scoped
    /// functions and recurse into itself.
    pub(super) fn register_and_lower_scoped_item(
        &mut self,
        item: &Item,
    ) -> Result<(), VirLoweringError> {
        self.register_scoped_item(item)?;
        if let Item::Fn {
            name,
            params,
            ret,
            body,
            is_async,
            ..
        } = item
        {
            self.lower_scoped_fn(name, params, ret, body, *is_async)?;
        }
        Ok(())
    }

    fn lower_scoped_fn(
        &mut self,
        name: &str,
        params: &[(String, RustType)],
        ret: &RustType,
        body: &Expr,
        is_async: bool,
    ) -> Result<(), VirLoweringError> {
        let lowered_ret = lowered_function_return_type(ret, is_async);
        let synthetic_async_body;
        let lowered_body = if is_async {
            synthetic_async_body = Expr::Async {
                capture_by_value: true,
                body: Box::new(body.clone()),
            };
            &synthetic_async_body
        } else {
            body
        };
        // The nested fn must see the symbols visible at its definition site
        // (program symbols plus enclosing block-scoped items) so that calls to
        // itself (recursion) and to sibling block-scoped functions resolve.
        let visible_symbols = self.visible_symbols();
        let (lowered, nested_closures) = super::context::lower_function_with_closures(
            name,
            params,
            &lowered_ret,
            lowered_body,
            &visible_symbols,
        )?;
        // Block-scoped functions and their nested closures flow into the same
        // flat function table as top-level functions via `closure_bodies`,
        // which `lower_item_list` merges into the `LoweredProgram`.
        self.closure_bodies.push((name.to_string(), lowered));
        self.closure_bodies.extend(nested_closures);
        Ok(())
    }

    pub(super) fn field_type(&self, type_name: &str, field: &str) -> Option<&RustType> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| {
                scope
                    .symbols
                    .struct_fields
                    .get(type_name)
                    .and_then(|fields| fields.get(field))
            })
            .or_else(|| self.symbols.field_type(type_name, field))
    }

    pub(super) fn enum_variant(&self, enum_name: &str, variant: &str) -> Option<&EnumVariantInfo> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| {
                scope
                    .symbols
                    .enum_variants
                    .get(enum_name)
                    .and_then(|variants| variants.get(variant))
            })
            .or_else(|| self.symbols.enum_variant(enum_name, variant))
    }

    /// Find a block-scoped function signature, searching inner scopes first so
    /// an inner shadowing definition wins over an outer one. Returns `None`
    /// when no enclosing block declares `name`, leaving program-wide
    /// resolution to the caller's `.or_else(...)` fallback.
    fn scoped_fn_sig(&self, name: &str) -> Option<&FnSig> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.symbols.fn_sigs.get(name))
    }

    pub(super) fn fn_ret_type(&self, name: &str) -> Option<&RustType> {
        self.scoped_fn_sig(name)
            .map(|sig| &sig.ret)
            .or_else(|| self.symbols.fn_ret_type(name))
    }

    pub(super) fn fn_type(&self, name: &str) -> Option<RustType> {
        self.scoped_fn_sig(name)
            .map(|sig| RustType::Function {
                params: sig.params.iter().map(|(_, ty)| ty.clone()).collect(),
                ret: Box::new(sig.ret.clone()),
            })
            .or_else(|| self.symbols.fn_type(name))
    }

    pub(super) fn fn_future_output_type(&self, name: &str) -> Option<&RustType> {
        self.scoped_fn_sig(name)
            .and_then(|sig| sig.future_output.as_ref())
            .or_else(|| self.symbols.fn_future_output_type(name))
    }

    pub(super) fn resolve_method_name(&self, type_name: &str, method: &str) -> String {
        self.symbols.resolve_method_name(type_name, method)
    }

    pub(super) fn visible_symbols(&self) -> ProgramSymbols {
        let mut symbols = self.symbols.clone();
        for scope in &self.scopes {
            symbols
                .struct_fields
                .extend(scope.symbols.struct_fields.clone());
            symbols
                .enum_variants
                .extend(scope.symbols.enum_variants.clone());
            // Promote block-scoped function signatures into the flat symbol
            // table the nested function's own lowering context consults. This
            // makes recursion (the fn calling itself) and calls to sibling
            // block-scoped functions resolve while lowering the body.
            symbols.fn_sigs.extend(scope.symbols.fn_sigs.clone());
        }
        symbols
    }
}
