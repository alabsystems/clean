// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Semireducible definition registration for type-level aliases.
//!
//! Provides `add_definition_reducible` — registers a definition as
//! `Declaration::Definition` with regular reducibility instead of
//! `Declaration::Opaque`.
//! Use only for simple one-step type aliases (e.g., `is_def_eq := DefEq`)
//! that the kernel must unfold during definitional equality checking.
//!
//! Part of #464: bypass Opaque alias barrier for type preservation derivation.

use clean_kernel::{Declaration, Name};

use super::definition::SpecDefinition;
use super::error::SpecError;
use super::Specification;

impl Specification {
    /// Add a definition as a semireducible Definition (not Opaque).
    ///
    /// Use for simple type-level aliases (e.g., `is_def_eq := DefEq`) that the
    /// kernel must unfold during definitional equality checking. These are one-step
    /// reductions, so the "expensive/infinite reduction" concern from #1385 does
    /// not apply.
    pub(crate) fn add_definition_reducible(
        &mut self,
        mut def: SpecDefinition,
    ) -> Result<(), SpecError> {
        let type_expr = self.elaborate_source(&def.type_src, &format!("type of {}", def.name))?;
        def.elaborated_type = Some(type_expr.clone());

        let value_src = def.value_src.as_ref().ok_or_else(|| {
            SpecError::ParseError(format!(
                "add_definition_reducible requires a value for {}",
                def.name
            ))
        })?;
        let value_expr = self.elaborate_source(value_src, &format!("value of {}", def.name))?;
        def.elaborated_value = Some(value_expr.clone());

        let level_params = {
            let mut params = Vec::new();
            Self::collect_level_params_expr(&type_expr, &mut params);
            Self::collect_level_params_expr(&value_expr, &mut params);
            params
        };

        // Register as a regular Definition so the kernel can unfold during
        // defEq checking in default transparency, without upgrading the alias
        // to fully reducible unfolding in `TransparencyMode::Reducible`.
        let decl = Declaration::Definition {
            name: Name::from_string(&def.name),
            level_params,
            type_: type_expr,
            value: value_expr,
            is_reducible: false,
        };

        self.env
            .add_decl(decl)
            .map_err(|e| SpecError::TypeError(format!("add_decl: {e}")))?;

        self.definitions.insert(def.name.clone(), def);
        Ok(())
    }
}
