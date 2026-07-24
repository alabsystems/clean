// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::source::parser::Parser;
use crate::source::SourceError;
use crate::stmt::AssociatedTypeDef;

impl Parser {
    pub(super) fn parse_trait_associated_type(
        &mut self,
        assoc_ty: syn::TraitItemType,
        trait_name: &str,
    ) -> Result<AssociatedTypeDef, SourceError> {
        let assoc_name = assoc_ty.ident.to_string();
        let generic_params = self.parse_generic_params(&assoc_ty.generics)?;
        let assoc_type_params = generic_params
            .iter()
            .filter_map(|param| param.as_type_param().cloned())
            .collect::<Vec<_>>();

        self.with_type_params(&assoc_type_params, |parser| {
            let target = format!("associated type `{assoc_name}` in trait `{trait_name}`");
            let bounds = assoc_ty
                .bounds
                .iter()
                .map(|bound| Self::parse_type_bound_string(bound, "trait item", &target))
                .collect::<Result<Vec<_>, _>>()?;
            let where_clause = parser.parse_where_clause(
                assoc_ty.generics.where_clause.as_ref(),
                "trait item",
                &target,
            )?;
            let default = assoc_ty
                .default
                .map(|(_, ty)| parser.parse_type(&ty))
                .transpose()?;

            Ok(AssociatedTypeDef {
                name: assoc_name.clone(),
                generic_params: generic_params.clone(),
                bounds,
                where_clause,
                default,
            })
        })
    }
}
