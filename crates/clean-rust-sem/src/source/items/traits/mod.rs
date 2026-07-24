// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

mod associated_types;
mod methods;

use crate::expr::Item;
use crate::source::parser::Parser;
use crate::source::SourceError;
use crate::stmt::{AssociatedConstDef, TraitDef};

impl Parser {
    pub(in crate::source) fn parse_trait_item(
        &mut self,
        item_trait: syn::ItemTrait,
    ) -> Result<Item, SourceError> {
        let trait_name = item_trait.ident.to_string();
        if item_trait.auto_token.is_some() {
            return Err(Self::unsupported(
                "trait",
                format!("auto trait `{trait_name}`"),
            ));
        }
        let type_params = self.assign_type_param_ids(Self::parse_generics(&item_trait.generics)?);
        let supertraits = Self::parse_supertraits(&item_trait, &trait_name)?;

        self.with_type_params(&type_params, |parser| {
            let mut methods = Vec::new();
            let mut associated_types = Vec::new();
            let mut associated_constants = Vec::new();
            let mut default_bodies = std::collections::HashMap::new();
            let trait_self_ty = Self::placeholder_self_type();

            for item in item_trait.items {
                match item {
                    syn::TraitItem::Fn(method) => {
                        let trait_name_for_method = trait_name.clone();
                        let (sig, default_body) = parser.with_type_context(
                            trait_self_ty.clone(),
                            Some(trait_name_for_method.clone()),
                            |p| p.parse_trait_method_with_optional_default(method),
                        )?;
                        if let Some(body) = default_body {
                            default_bodies.insert(sig.name.clone(), body);
                        }
                        methods.push(sig);
                    }
                    syn::TraitItem::Type(assoc_ty) => {
                        let trait_name_for_assoc = trait_name.clone();
                        associated_types.push(parser.with_type_context(
                            trait_self_ty.clone(),
                            Some(trait_name_for_assoc.clone()),
                            |p| p.parse_trait_associated_type(assoc_ty, &trait_name_for_assoc),
                        )?);
                    }
                    syn::TraitItem::Const(assoc_const) => {
                        associated_constants.push(AssociatedConstDef {
                            name: assoc_const.ident.to_string(),
                            ty: parser.parse_type(&assoc_const.ty)?,
                            has_default: assoc_const.default.is_some(),
                        });
                    }
                    syn::TraitItem::Macro(_) => {
                        // Macro invocations inside trait definitions (e.g.,
                        // delegation macros) cannot be expanded without a macro
                        // engine, but silently skipping them is safe — they
                        // don't affect the trait's method/type/constant surface
                        // that we track.
                        continue;
                    }
                    _ => {
                        return Err(Self::unsupported(
                            "trait item",
                            format!("unsupported member in trait `{trait_name}`"),
                        ));
                    }
                }
            }

            let mut def =
                TraitDef::with_associated_types(trait_name.clone(), methods, associated_types);
            def.supertraits = supertraits.clone();
            def.associated_constants = associated_constants;
            def.default_bodies = default_bodies;
            def.type_params = type_params.clone();
            Ok(Item::TraitDef(def))
        })
    }

    fn parse_supertraits(
        item_trait: &syn::ItemTrait,
        trait_name: &str,
    ) -> Result<Vec<String>, SourceError> {
        let mut supertraits = Vec::new();
        for bound in &item_trait.supertraits {
            match bound {
                syn::TypeParamBound::Trait(trait_bound) => {
                    let name = Self::plain_trait_bound_name(
                        trait_bound,
                        "trait",
                        &format!("supertrait of `{trait_name}`"),
                    )?;
                    supertraits.push(name);
                }
                syn::TypeParamBound::Lifetime(_) => {
                    // Lifetime bounds like `trait Foo: 'static` are
                    // accepted silently — they constrain lifetime inference
                    // but don't affect method dispatch.
                }
                _ => {
                    return Err(Self::unsupported(
                        "trait",
                        format!("unsupported supertrait bound on `{trait_name}`"),
                    ));
                }
            }
        }

        Ok(supertraits)
    }
}
