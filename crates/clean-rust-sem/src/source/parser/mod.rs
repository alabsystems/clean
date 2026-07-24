// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{SourceError, SourceProgram};
use crate::types::{ConstParamDef, RustType, TypeParamDef, TypeVar};
use std::collections::{HashMap, HashSet};

mod associated_items;
mod const_generics;
mod expr_path_generics;
mod helpers;
mod registry;

#[derive(Clone)]
pub(super) struct ItemRegistrySnapshot {
    known_enums: HashSet<String>,
    known_enum_variants: HashMap<String, HashSet<String>>,
    known_tuple_enum_variants: HashMap<String, HashSet<String>>,
    known_unit_enum_variants: HashMap<String, HashSet<String>>,
    known_nominal_types: HashSet<String>,
    known_trait_constants: HashMap<String, HashSet<String>>,
    known_trait_methods: HashMap<String, HashSet<String>>,
    known_trait_impl_constants: HashMap<String, HashMap<String, HashSet<String>>>,
    known_trait_impl_methods: HashMap<String, HashMap<String, HashSet<String>>>,
    known_associated_constants: HashMap<String, HashSet<String>>,
    known_associated_functions: HashMap<String, HashSet<String>>,
    known_struct_fields: HashMap<String, Vec<String>>,
    known_tuple_structs: HashSet<String>,
    unsafe_traits: HashSet<String>,
    known_unions: HashSet<String>,
    type_aliases: HashMap<String, syn::Type>,
    resolved_type_aliases: HashMap<String, RustType>,
    resolving_type_aliases: HashSet<String>,
}

#[derive(Clone)]
pub(in crate::source) struct TypeContext {
    pub(in crate::source) self_ty: RustType,
    pub(in crate::source) trait_name: Option<String>,
}

#[derive(Default)]
pub(super) struct Parser {
    next_anon_lifetime: u32,
    next_synthetic_local: u32,
    next_type_param_id: u32,
    known_enums: HashSet<String>,
    known_enum_variants: HashMap<String, HashSet<String>>,
    known_tuple_enum_variants: HashMap<String, HashSet<String>>,
    known_unit_enum_variants: HashMap<String, HashSet<String>>,
    known_nominal_types: HashSet<String>,
    known_trait_constants: HashMap<String, HashSet<String>>,
    known_trait_methods: HashMap<String, HashSet<String>>,
    known_trait_impl_constants: HashMap<String, HashMap<String, HashSet<String>>>,
    known_trait_impl_methods: HashMap<String, HashMap<String, HashSet<String>>>,
    known_associated_constants: HashMap<String, HashSet<String>>,
    known_associated_functions: HashMap<String, HashSet<String>>,
    known_struct_fields: HashMap<String, Vec<String>>,
    known_tuple_structs: HashSet<String>,
    unsafe_traits: HashSet<String>,
    known_unions: HashSet<String>,
    type_aliases: HashMap<String, syn::Type>,
    resolved_type_aliases: HashMap<String, RustType>,
    resolving_type_aliases: HashSet<String>,
    pub(in crate::source) type_context: Option<TypeContext>,
    type_param_scopes: Vec<HashMap<String, TypeVar>>,
    const_param_scopes: Vec<HashMap<String, RustType>>,
}

impl Parser {
    pub(super) fn assign_type_param_ids(
        &mut self,
        type_params: Vec<TypeParamDef>,
    ) -> Vec<TypeParamDef> {
        type_params
            .into_iter()
            .map(|mut type_param| {
                type_param.id = self.next_type_param_id;
                self.next_type_param_id += 1;
                type_param
            })
            .collect()
    }

    pub(super) fn parse_source(&mut self, source: &str) -> Result<SourceProgram, SourceError> {
        let file = syn::parse_file(source)?;
        self.collect_top_level_items(&file.items)?;
        let items = file
            .items
            .into_iter()
            .filter(|item| {
                // Item-position macros are dropped, *except* recognized
                // item-level macros (e.g. `global_asm!`) which `parse_item`
                // lowers into a dedicated semantic item.
                if let syn::Item::Macro(item_macro) = item {
                    return Self::builtin_item_macro_dispatch_name(&item_macro.mac.path).is_some();
                }
                !matches!(
                    item,
                    syn::Item::Type(_)
                        | syn::Item::Use(_)
                        | syn::Item::ExternCrate(_)
                        | syn::Item::Mod(_)
                        | syn::Item::ForeignMod(_)
                        | syn::Item::TraitAlias(_)
                )
            })
            .map(|item| self.parse_item(item))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(SourceProgram { items })
    }

    pub(super) fn with_type_context<T>(
        &mut self,
        self_ty: RustType,
        trait_name: Option<String>,
        f: impl FnOnce(&mut Self) -> Result<T, SourceError>,
    ) -> Result<T, SourceError> {
        let prev = self.type_context.replace(TypeContext {
            self_ty,
            trait_name,
        });
        let result = f(self);
        self.type_context = prev;
        result
    }

    pub(super) fn with_type_params<T>(
        &mut self,
        type_params: &[TypeParamDef],
        f: impl FnOnce(&mut Self) -> Result<T, SourceError>,
    ) -> Result<T, SourceError> {
        let mut scope = HashMap::with_capacity(type_params.len());
        for type_param in type_params {
            scope.insert(
                type_param.name.clone(),
                TypeVar {
                    id: type_param.id,
                    name: Some(type_param.name.clone()),
                },
            );
        }
        self.type_param_scopes.push(scope);
        let result = f(self);
        self.type_param_scopes.pop();
        result
    }

    pub(super) fn with_const_params<T>(
        &mut self,
        const_params: &[ConstParamDef],
        f: impl FnOnce(&mut Self) -> Result<T, SourceError>,
    ) -> Result<T, SourceError> {
        let mut scope = HashMap::with_capacity(const_params.len());
        for const_param in const_params {
            scope.insert(const_param.name.clone(), const_param.ty.clone());
        }
        self.const_param_scopes.push(scope);
        let result = f(self);
        self.const_param_scopes.pop();
        result
    }

    pub(super) fn with_isolated_type_params<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<T, SourceError>,
    ) -> Result<T, SourceError> {
        let prev = std::mem::take(&mut self.type_param_scopes);
        let prev_const = std::mem::take(&mut self.const_param_scopes);
        let result = f(self);
        self.type_param_scopes = prev;
        self.const_param_scopes = prev_const;
        result
    }

    pub(in crate::source) fn resolve_type_param(&self, name: &str) -> Option<TypeVar> {
        self.type_param_scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }

    pub(in crate::source) fn resolve_const_param(&self, name: &str) -> Option<RustType> {
        self.const_param_scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
    }
}
