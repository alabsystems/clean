// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::SourceError;
use super::Parser;
use std::collections::HashSet;

impl Parser {
    pub(super) fn collect_trait_associated_items<'a>(
        &mut self,
        items: impl IntoIterator<Item = &'a syn::Item>,
    ) -> Result<(), SourceError> {
        for item in items {
            let syn::Item::Impl(item_impl) = item else {
                continue;
            };
            let Some((_, trait_path, _)) = &item_impl.trait_ else {
                continue;
            };

            let self_ty = self.parse_type(&item_impl.self_ty)?;
            let Some(type_name) = self.canonical_nominal_type_name(&self_ty) else {
                continue;
            };
            let trait_name = Self::plain_trait_path_name(trait_path, "impl item", "trait impl")?;

            let method_names = item_impl
                .items
                .iter()
                .filter_map(|impl_item| match impl_item {
                    syn::ImplItem::Fn(method) => Some(method.sig.ident.to_string()),
                    _ => None,
                })
                .collect::<HashSet<_>>();
            let constant_names = item_impl
                .items
                .iter()
                .filter_map(|impl_item| match impl_item {
                    syn::ImplItem::Const(item_const) => Some(item_const.ident.to_string()),
                    _ => None,
                })
                .collect::<HashSet<_>>();

            self.known_trait_impl_methods
                .entry(type_name.clone())
                .or_default()
                .entry(trait_name.clone())
                .or_default()
                .extend(method_names);
            self.known_trait_impl_constants
                .entry(type_name)
                .or_default()
                .entry(trait_name)
                .or_default()
                .extend(constant_names);
        }
        Ok(())
    }

    pub(crate) fn associated_item_type_name(
        &mut self,
        path: &syn::Path,
    ) -> Result<Option<String>, SourceError> {
        let Some(prefix) = Self::path_prefix(path) else {
            return Ok(None);
        };
        if prefix == "Self" {
            if let Some(context) = &self.type_context {
                if context.trait_name.is_none() {
                    return Ok(self.canonical_nominal_type_name(&context.self_ty));
                }
            }
            return Ok(None);
        }
        if self.known_nominal_types.contains(&prefix) {
            return Ok(Some(prefix));
        }
        let Some(alias_ty) = self.resolve_type_alias(&prefix)? else {
            return Ok(None);
        };
        Ok(self.canonical_nominal_type_name(&alias_ty))
    }

    pub(crate) fn canonical_tuple_struct_name(
        &mut self,
        name: &str,
    ) -> Result<Option<String>, SourceError> {
        if self.is_known_tuple_struct(name) {
            return Ok(Some(name.to_string()));
        }

        let Some(alias_ty) = self.resolve_type_alias(name)? else {
            return Ok(None);
        };
        let Some(canonical_name) = self.canonical_nominal_type_name(&alias_ty) else {
            return Ok(None);
        };
        Ok(self
            .is_known_tuple_struct(&canonical_name)
            .then_some(canonical_name))
    }

    pub(crate) fn canonical_named_struct_name(
        &mut self,
        name: &str,
    ) -> Result<Option<String>, SourceError> {
        if self.struct_field_names(name).is_some() {
            return Ok(Some(name.to_string()));
        }

        let Some(alias_ty) = self.resolve_type_alias(name)? else {
            return Ok(None);
        };
        let Some(canonical_name) = self.canonical_nominal_type_name(&alias_ty) else {
            return Ok(None);
        };
        Ok(self
            .struct_field_names(&canonical_name)
            .is_some()
            .then_some(canonical_name))
    }

    pub(crate) fn associated_function_path_name(
        &mut self,
        path: &syn::Path,
    ) -> Result<Option<String>, SourceError> {
        if let Some(name) = self.trait_context_associated_function_name(path)? {
            return Ok(Some(name));
        }
        let Some(type_name) = self.associated_item_type_name(path)? else {
            return Ok(None);
        };
        let method = path
            .segments
            .last()
            .expect("path has at least one segment")
            .ident
            .to_string();
        if self.type_has_associated_function(&type_name, &method) {
            Ok(Some(format!("{type_name}::{method}")))
        } else {
            Ok(None)
        }
    }

    fn trait_context_associated_function_name(
        &self,
        path: &syn::Path,
    ) -> Result<Option<String>, SourceError> {
        let Some(prefix) = Self::path_prefix(path) else {
            return Ok(None);
        };
        if prefix != "Self" {
            return Ok(None);
        }
        let Some(context) = &self.type_context else {
            return Ok(None);
        };
        let Some(trait_name) = context.trait_name.as_ref() else {
            return Ok(None);
        };
        let method = path
            .segments
            .last()
            .expect("path has at least one segment")
            .ident
            .to_string();
        if let Some(type_name) = self.canonical_nominal_type_name(&context.self_ty) {
            if self.type_has_associated_function(&type_name, &method) {
                return Ok(Some(format!("{type_name}::{method}")));
            }
        }
        if self
            .known_trait_methods
            .get(trait_name)
            .is_some_and(|methods| methods.contains(&method))
        {
            let self_name = context.self_ty.name().unwrap_or_else(|| "Self".to_string());
            return Ok(Some(format!("<{self_name} as {trait_name}>::{method}")));
        }
        Ok(None)
    }

    pub(crate) fn associated_constant_path_name(
        &mut self,
        path: &syn::Path,
    ) -> Result<Option<String>, SourceError> {
        if let Some(name) = self.trait_context_associated_constant_name(path)? {
            return Ok(Some(name));
        }
        let Some(type_name) = self.associated_item_type_name(path)? else {
            return Ok(None);
        };
        let constant = path
            .segments
            .last()
            .expect("path has at least one segment")
            .ident
            .to_string();
        if self.type_has_associated_constant(&type_name, &constant) {
            Ok(Some(format!("{type_name}::{constant}")))
        } else {
            Ok(None)
        }
    }

    fn trait_context_associated_constant_name(
        &self,
        path: &syn::Path,
    ) -> Result<Option<String>, SourceError> {
        let Some(prefix) = Self::path_prefix(path) else {
            return Ok(None);
        };
        if prefix != "Self" {
            return Ok(None);
        }
        let Some(context) = &self.type_context else {
            return Ok(None);
        };
        let Some(trait_name) = context.trait_name.as_ref() else {
            return Ok(None);
        };
        let constant = path
            .segments
            .last()
            .expect("path has at least one segment")
            .ident
            .to_string();
        if let Some(type_name) = self.canonical_nominal_type_name(&context.self_ty) {
            if self.type_has_associated_constant(&type_name, &constant) {
                return Ok(Some(format!("{type_name}::{constant}")));
            }
            if self.trait_impl_has_associated_constant(&type_name, trait_name, &constant) {
                return Ok(Some(format!("<{type_name} as {trait_name}>::{constant}")));
            }
            return Ok(None);
        }
        if self.trait_has_associated_constant(trait_name, &constant) {
            let self_name = context.self_ty.name().unwrap_or_else(|| "Self".to_string());
            return Ok(Some(format!("<{self_name} as {trait_name}>::{constant}")));
        }
        Ok(None)
    }

    pub(crate) fn trait_impl_has_associated_function(
        &self,
        type_name: &str,
        trait_name: &str,
        method: &str,
    ) -> bool {
        let Some(trait_impls) = self.known_trait_impl_methods.get(type_name) else {
            return false;
        };
        let Some(explicit_methods) = trait_impls.get(trait_name) else {
            return false;
        };
        explicit_methods.contains(method)
            || self
                .known_trait_methods
                .get(trait_name)
                .is_some_and(|methods| methods.contains(method))
    }

    pub(crate) fn trait_impl_has_associated_constant(
        &self,
        type_name: &str,
        trait_name: &str,
        constant: &str,
    ) -> bool {
        self.known_trait_impl_constants
            .get(type_name)
            .and_then(|trait_impls| trait_impls.get(trait_name))
            .is_some_and(|constants| constants.contains(constant))
    }
}
