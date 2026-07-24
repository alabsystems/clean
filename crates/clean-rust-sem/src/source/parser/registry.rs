// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::SourceError;
use super::{ItemRegistrySnapshot, Parser};
use crate::types::RustType;
use std::collections::HashSet;

impl Parser {
    pub(super) fn collect_top_level_items(
        &mut self,
        items: &[syn::Item],
    ) -> Result<(), SourceError> {
        self.known_enums.clear();
        self.known_enum_variants.clear();
        self.known_tuple_enum_variants.clear();
        self.known_unit_enum_variants.clear();
        self.known_nominal_types.clear();
        self.known_trait_constants.clear();
        self.known_trait_methods.clear();
        self.known_trait_impl_constants.clear();
        self.known_trait_impl_methods.clear();
        self.known_associated_constants.clear();
        self.known_associated_functions.clear();
        self.known_struct_fields.clear();
        self.known_tuple_structs.clear();
        self.unsafe_traits.clear();
        self.known_unions.clear();
        self.type_aliases.clear();
        self.resolved_type_aliases.clear();
        self.resolving_type_aliases.clear();

        self.seed_builtin_enums();
        self.seed_builtin_types();
        self.collect_visible_items(items.iter())?;
        self.collect_inherent_associated_items(items.iter())?;
        self.collect_trait_associated_items(items.iter())?;
        Ok(())
    }

    /// Register built-in enum types (`Option`, `Result`) so their variant
    /// paths (`Option::Some`, `Result::Ok`, etc.) are recognized without
    /// requiring a user-defined enum declaration.
    fn seed_builtin_enums(&mut self) {
        self.known_enums.insert("Option".to_string());
        self.known_enum_variants.insert(
            "Option".to_string(),
            ["Some", "None"].iter().map(|s| s.to_string()).collect(),
        );
        self.known_tuple_enum_variants.insert(
            "Option".to_string(),
            ["Some"].iter().map(|s| s.to_string()).collect(),
        );
        self.known_unit_enum_variants.insert(
            "Option".to_string(),
            ["None"].iter().map(|s| s.to_string()).collect(),
        );
        self.known_enums.insert("Result".to_string());
        self.known_enum_variants.insert(
            "Result".to_string(),
            ["Ok", "Err"].iter().map(|s| s.to_string()).collect(),
        );
        self.known_tuple_enum_variants.insert(
            "Result".to_string(),
            ["Ok", "Err"].iter().map(|s| s.to_string()).collect(),
        );
        self.known_unit_enum_variants
            .insert("Result".to_string(), HashSet::new());
    }

    /// Register standard-library nominal types (`String`, `Vec`, `Box`, etc.)
    /// so their associated-function paths (`String::new`, `Vec::with_capacity`,
    /// etc.) are recognized without requiring a user-defined struct declaration.
    fn seed_builtin_types(&mut self) {
        for name in [
            "String",
            "Vec",
            "Box",
            "Cell",
            "RefCell",
            "UnsafeCell",
            "OnceCell",
            "OnceLock",
            "Mutex",
            "RwLock",
            "HashMap",
            "HashSet",
            "BTreeMap",
            "BTreeSet",
        ] {
            self.known_nominal_types.insert(name.to_string());
        }
        for name in [
            "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
            "f32", "f64", "bool", "char",
        ] {
            self.known_nominal_types.insert(name.to_string());
        }
        self.known_associated_functions.insert(
            "String".to_string(),
            ["new", "from"]
                .iter()
                .map(|name| name.to_string())
                .collect(),
        );
        self.known_associated_functions.insert(
            "Vec".to_string(),
            ["new", "with_capacity"]
                .iter()
                .map(|name| name.to_string())
                .collect(),
        );
        self.known_associated_functions.insert(
            "Box".to_string(),
            ["new"].iter().map(|name| name.to_string()).collect(),
        );
        self.known_associated_functions.insert(
            "Cell".to_string(),
            ["new"].iter().map(|name| name.to_string()).collect(),
        );
        self.known_associated_functions.insert(
            "RefCell".to_string(),
            ["new"].iter().map(|name| name.to_string()).collect(),
        );
        self.known_associated_functions.insert(
            "UnsafeCell".to_string(),
            ["new"].iter().map(|name| name.to_string()).collect(),
        );
        self.known_associated_functions.insert(
            "OnceCell".to_string(),
            ["new"].iter().map(|name| name.to_string()).collect(),
        );
        self.known_associated_functions.insert(
            "OnceLock".to_string(),
            ["new"].iter().map(|name| name.to_string()).collect(),
        );
        self.known_associated_functions.insert(
            "Mutex".to_string(),
            ["new"].iter().map(|name| name.to_string()).collect(),
        );
        self.known_associated_functions.insert(
            "RwLock".to_string(),
            ["new"].iter().map(|name| name.to_string()).collect(),
        );
    }

    pub(crate) fn collect_block_items(&mut self, stmts: &[syn::Stmt]) -> Result<(), SourceError> {
        let items = stmts
            .iter()
            .filter_map(|stmt| match stmt {
                syn::Stmt::Item(item) => Some(item),
                _ => None,
            })
            .collect::<Vec<_>>();
        self.collect_visible_items(items.iter().copied())?;
        self.collect_inherent_associated_items(items.iter().copied())?;
        self.collect_trait_associated_items(items.iter().copied())?;
        Ok(())
    }

    fn collect_visible_items<'a>(
        &mut self,
        items: impl IntoIterator<Item = &'a syn::Item>,
    ) -> Result<(), SourceError> {
        for item in items {
            match item {
                syn::Item::Enum(item_enum) => {
                    let name = item_enum.ident.to_string();
                    let variants = item_enum
                        .variants
                        .iter()
                        .map(|variant| variant.ident.to_string())
                        .collect::<HashSet<_>>();
                    let tuple_variants = item_enum
                        .variants
                        .iter()
                        .filter(|variant| matches!(variant.fields, syn::Fields::Unnamed(_)))
                        .map(|variant| variant.ident.to_string())
                        .collect::<HashSet<_>>();
                    let unit_variants = item_enum
                        .variants
                        .iter()
                        .filter(|variant| matches!(variant.fields, syn::Fields::Unit))
                        .map(|variant| variant.ident.to_string())
                        .collect::<HashSet<_>>();
                    self.known_enums.insert(name.clone());
                    self.known_enum_variants.insert(name.clone(), variants);
                    self.known_tuple_enum_variants
                        .insert(name.clone(), tuple_variants);
                    self.known_unit_enum_variants
                        .insert(name.clone(), unit_variants);
                    self.known_nominal_types.insert(name);
                }
                syn::Item::Struct(item_struct) => {
                    let name = item_struct.ident.to_string();
                    self.known_nominal_types.insert(name.clone());
                    match &item_struct.fields {
                        syn::Fields::Named(fields) => {
                            let field_names = fields
                                .named
                                .iter()
                                .filter_map(|field| field.ident.as_ref().map(ToString::to_string))
                                .collect::<Vec<_>>();
                            self.known_struct_fields.insert(name, field_names);
                        }
                        syn::Fields::Unnamed(_) => {
                            self.known_tuple_structs.insert(name);
                        }
                        syn::Fields::Unit => {}
                    }
                }
                syn::Item::Trait(item_trait) => {
                    if item_trait.unsafety.is_some() {
                        self.unsafe_traits.insert(item_trait.ident.to_string());
                    }
                    let constant_names = item_trait
                        .items
                        .iter()
                        .filter_map(|item| match item {
                            syn::TraitItem::Const(item_const) => Some(item_const.ident.to_string()),
                            _ => None,
                        })
                        .collect::<HashSet<_>>();
                    let method_names = item_trait
                        .items
                        .iter()
                        .filter_map(|item| match item {
                            syn::TraitItem::Fn(method) => Some(method.sig.ident.to_string()),
                            _ => None,
                        })
                        .collect::<HashSet<_>>();
                    self.known_trait_constants
                        .insert(item_trait.ident.to_string(), constant_names);
                    self.known_trait_methods
                        .insert(item_trait.ident.to_string(), method_names);
                }
                syn::Item::Union(item_union) => {
                    let name = item_union.ident.to_string();
                    self.known_nominal_types.insert(name.clone());
                    self.known_unions.insert(name.clone());
                    let field_names = item_union
                        .fields
                        .named
                        .iter()
                        .filter_map(|field| field.ident.as_ref().map(ToString::to_string))
                        .collect::<Vec<_>>();
                    self.known_struct_fields.insert(name, field_names);
                }
                syn::Item::Type(item_type) => self.register_type_alias(item_type)?,
                syn::Item::Use(item_use) => {
                    Self::collect_use_leaf_names(&item_use.tree, &mut self.known_nominal_types)
                }
                _ => {}
            }
        }

        let aliases = self.type_aliases.keys().cloned().collect::<Vec<_>>();
        for alias in aliases {
            let _ = self.resolve_type_alias(&alias)?;
        }

        Ok(())
    }

    fn collect_inherent_associated_items<'a>(
        &mut self,
        items: impl IntoIterator<Item = &'a syn::Item>,
    ) -> Result<(), SourceError> {
        for item in items {
            let syn::Item::Impl(item_impl) = item else {
                continue;
            };
            if item_impl.trait_.is_some() {
                continue;
            }

            let self_ty = self.parse_type(&item_impl.self_ty)?;
            let Some(type_name) = self.canonical_nominal_type_name(&self_ty) else {
                continue;
            };

            let mut method_names = Vec::new();
            let mut constant_names = Vec::new();
            for impl_item in &item_impl.items {
                match impl_item {
                    syn::ImplItem::Fn(method) => {
                        method_names.push(method.sig.ident.to_string());
                    }
                    syn::ImplItem::Const(item_const) => {
                        constant_names.push(item_const.ident.to_string());
                    }
                    _ => {}
                }
            }
            self.known_associated_functions
                .entry(type_name.clone())
                .or_default()
                .extend(method_names);
            self.known_associated_constants
                .entry(type_name)
                .or_default()
                .extend(constant_names);
        }
        Ok(())
    }

    pub(crate) fn snapshot_item_registries(&self) -> ItemRegistrySnapshot {
        ItemRegistrySnapshot {
            known_enums: self.known_enums.clone(),
            known_enum_variants: self.known_enum_variants.clone(),
            known_tuple_enum_variants: self.known_tuple_enum_variants.clone(),
            known_unit_enum_variants: self.known_unit_enum_variants.clone(),
            known_nominal_types: self.known_nominal_types.clone(),
            known_trait_constants: self.known_trait_constants.clone(),
            known_trait_methods: self.known_trait_methods.clone(),
            known_trait_impl_constants: self.known_trait_impl_constants.clone(),
            known_trait_impl_methods: self.known_trait_impl_methods.clone(),
            known_associated_constants: self.known_associated_constants.clone(),
            known_associated_functions: self.known_associated_functions.clone(),
            known_struct_fields: self.known_struct_fields.clone(),
            known_tuple_structs: self.known_tuple_structs.clone(),
            unsafe_traits: self.unsafe_traits.clone(),
            known_unions: self.known_unions.clone(),
            type_aliases: self.type_aliases.clone(),
            resolved_type_aliases: self.resolved_type_aliases.clone(),
            resolving_type_aliases: self.resolving_type_aliases.clone(),
        }
    }

    pub(crate) fn restore_item_registries(&mut self, snapshot: ItemRegistrySnapshot) {
        self.known_enums = snapshot.known_enums;
        self.known_enum_variants = snapshot.known_enum_variants;
        self.known_tuple_enum_variants = snapshot.known_tuple_enum_variants;
        self.known_unit_enum_variants = snapshot.known_unit_enum_variants;
        self.known_nominal_types = snapshot.known_nominal_types;
        self.known_trait_constants = snapshot.known_trait_constants;
        self.known_trait_methods = snapshot.known_trait_methods;
        self.known_trait_impl_constants = snapshot.known_trait_impl_constants;
        self.known_trait_impl_methods = snapshot.known_trait_impl_methods;
        self.known_associated_constants = snapshot.known_associated_constants;
        self.known_associated_functions = snapshot.known_associated_functions;
        self.known_struct_fields = snapshot.known_struct_fields;
        self.known_tuple_structs = snapshot.known_tuple_structs;
        self.unsafe_traits = snapshot.unsafe_traits;
        self.known_unions = snapshot.known_unions;
        self.type_aliases = snapshot.type_aliases;
        self.resolved_type_aliases = snapshot.resolved_type_aliases;
        self.resolving_type_aliases = snapshot.resolving_type_aliases;
    }

    fn register_type_alias(&mut self, item_type: &syn::ItemType) -> Result<(), SourceError> {
        if !item_type.generics.params.is_empty() || item_type.generics.where_clause.is_some() {
            return Err(Self::unsupported(
                "type alias",
                format!("generic type alias `{}`", item_type.ident),
            ));
        }
        self.type_aliases
            .insert(item_type.ident.to_string(), (*item_type.ty).clone());
        Ok(())
    }

    pub(crate) fn is_known_tuple_struct(&self, name: &str) -> bool {
        self.known_tuple_structs.contains(name)
    }

    pub(crate) fn is_known_union(&self, name: &str) -> bool {
        self.known_unions.contains(name)
    }

    pub(crate) fn is_unsafe_trait(&self, name: &str) -> bool {
        self.unsafe_traits.contains(name)
    }

    pub(crate) fn struct_field_names(&self, name: &str) -> Option<&[String]> {
        self.known_struct_fields.get(name).map(Vec::as_slice)
    }

    pub(crate) fn resolve_enum_path(
        &mut self,
        path: &syn::Path,
    ) -> Result<Option<(String, String)>, SourceError> {
        let Ok((enum_name, variant)) = Self::split_qualified_path(path, "enum path") else {
            return Ok(None);
        };
        if enum_name == "Self" {
            let Some(self_enum_name) = self.current_inherent_self_enum_name() else {
                return Ok(None);
            };
            if self.enum_has_variant(&self_enum_name, &variant) {
                return Ok(Some((self_enum_name, variant)));
            }
            return Ok(None);
        }
        if self.enum_has_variant(&enum_name, &variant) {
            return Ok(Some((enum_name, variant)));
        }
        let Some(alias_ty) = self.resolve_type_alias(&enum_name)? else {
            return Ok(None);
        };
        let Some(canonical_enum_name) = self.canonical_enum_name(&alias_ty) else {
            return Ok(None);
        };
        if self.enum_has_variant(&canonical_enum_name, &variant) {
            Ok(Some((canonical_enum_name, variant)))
        } else {
            Ok(None)
        }
    }

    pub(crate) fn resolve_type_alias(
        &mut self,
        name: &str,
    ) -> Result<Option<RustType>, SourceError> {
        if let Some(resolved) = self.resolved_type_aliases.get(name) {
            return Ok(Some(resolved.clone()));
        }
        let Some(alias_ty) = self.type_aliases.get(name).cloned() else {
            return Ok(None);
        };
        if !self.resolving_type_aliases.insert(name.to_string()) {
            return Err(SourceError::Invalid {
                context: "type alias",
                detail: format!("cyclic alias involving `{name}`"),
            });
        }

        let resolved = self.parse_type(&alias_ty);
        self.resolving_type_aliases.remove(name);

        let resolved = resolved?;
        self.resolved_type_aliases
            .insert(name.to_string(), resolved.clone());
        Ok(Some(resolved))
    }

    pub(crate) fn enum_has_variant(&self, enum_name: &str, variant: &str) -> bool {
        self.known_enum_variants
            .get(enum_name)
            .is_some_and(|variants| variants.contains(variant))
    }

    pub(crate) fn enum_has_unit_variant(&self, enum_name: &str, variant: &str) -> bool {
        self.known_unit_enum_variants
            .get(enum_name)
            .is_some_and(|variants| variants.contains(variant))
    }

    pub(crate) fn enum_has_tuple_variant(&self, enum_name: &str, variant: &str) -> bool {
        self.known_tuple_enum_variants
            .get(enum_name)
            .is_some_and(|variants| variants.contains(variant))
    }

    pub(crate) fn canonical_enum_name(&self, ty: &RustType) -> Option<String> {
        match ty {
            RustType::Named { name, .. } if self.known_enums.contains(name) => Some(name.clone()),
            RustType::Option { .. } => Some("Option".to_string()),
            RustType::Result { .. } => Some("Result".to_string()),
            _ => None,
        }
    }

    pub(crate) fn canonical_nominal_type_name(&self, ty: &RustType) -> Option<String> {
        match ty {
            RustType::Named { name, .. } if self.known_nominal_types.contains(name) => {
                Some(name.clone())
            }
            RustType::Vec { .. } => Some("Vec".to_string()),
            RustType::Box { .. } => Some("Box".to_string()),
            RustType::Cell { .. } => Some("Cell".to_string()),
            RustType::RefCell { .. } => Some("RefCell".to_string()),
            RustType::UnsafeCell { .. } => Some("UnsafeCell".to_string()),
            RustType::Option { .. } => Some("Option".to_string()),
            RustType::Result { .. } => Some("Result".to_string()),
            _ => None,
        }
    }

    pub(crate) fn type_has_associated_function(&self, type_name: &str, method: &str) -> bool {
        self.known_associated_functions
            .get(type_name)
            .is_some_and(|methods| methods.contains(method))
    }

    pub(crate) fn type_has_associated_constant(&self, type_name: &str, constant: &str) -> bool {
        self.known_associated_constants
            .get(type_name)
            .is_some_and(|constants| constants.contains(constant))
    }

    pub(crate) fn trait_has_associated_constant(&self, trait_name: &str, constant: &str) -> bool {
        self.known_trait_constants
            .get(trait_name)
            .is_some_and(|constants| constants.contains(constant))
    }

    /// Walk a `use`-tree and register every leaf name as a known nominal type.
    ///
    /// This is intentionally permissive: even function or constant imports will
    /// be registered as nominal types, which is harmless — the worst case is a
    /// spurious entry in `known_nominal_types` that is never queried. The
    /// benefit is that `use std::collections::HashMap;` makes `HashMap`
    /// available for associated-function and struct-field resolution.
    fn collect_use_leaf_names(tree: &syn::UseTree, out: &mut HashSet<String>) {
        match tree {
            syn::UseTree::Path(use_path) => {
                Self::collect_use_leaf_names(&use_path.tree, out);
            }
            syn::UseTree::Name(use_name) => {
                let name = use_name.ident.to_string();
                if name.chars().next().is_some_and(|c| c.is_uppercase()) {
                    out.insert(name);
                }
            }
            syn::UseTree::Rename(use_rename) => {
                let alias = use_rename.rename.to_string();
                if alias.chars().next().is_some_and(|c| c.is_uppercase()) {
                    out.insert(alias);
                }
            }
            syn::UseTree::Glob(_) => {
                // Glob imports (`use foo::*`) cannot be resolved without module
                // resolution, so we silently skip them.
            }
            syn::UseTree::Group(use_group) => {
                for item in &use_group.items {
                    Self::collect_use_leaf_names(item, out);
                }
            }
        }
    }
}
