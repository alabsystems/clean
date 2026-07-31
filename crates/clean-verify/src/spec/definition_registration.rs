// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definition registration helpers for specification declarations.

use clean_kernel::{Declaration, Name, TypeChecker};

use super::{SpecDefinition, SpecError, Specification};

/// How to elaborate a definition's value relative to its declared type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ValueElab {
    /// Pure inference (the default for concrete-typed values).
    Infer,
    /// Independent inference followed by a checked universe alignment with the
    /// declared type (needed for universe-polymorphic values).
    AlignAgainstType,
}

impl Specification {
    pub(super) fn prepare_definition_decl(
        &mut self,
        def: SpecDefinition,
    ) -> Result<(SpecDefinition, Declaration), SpecError> {
        self.prepare_definition_decl_impl(def, ValueElab::Infer)
    }

    fn prepare_definition_decl_impl(
        &mut self,
        mut def: SpecDefinition,
        value_elab: ValueElab,
    ) -> Result<(SpecDefinition, Declaration), SpecError> {
        let type_expr = self.elaborate_source(&def.type_src, &format!("type of {}", def.name))?;
        def.elaborated_type = Some(type_expr.clone());

        let value_expr = if let Some(value_expr) = def.elaborated_value.clone() {
            Some(value_expr)
        } else if let Some(ref value_src) = def.value_src {
            let label = format!("value of {}", def.name);
            Some(match value_elab {
                ValueElab::Infer => self.elaborate_source(value_src, &label)?,
                // Universe-polymorphic values: preserve independently inferred
                // universes, then align them bijectively with the declared type.
                ValueElab::AlignAgainstType => {
                    self.elaborate_source_checked(value_src, &type_expr, &label)?
                }
            })
        } else {
            None
        };

        def.elaborated_value = value_expr.clone();

        // Determine if the type lives in Prop (Sort 0). Theorems must have
        // Prop type per add_decl enforcement (#1276).
        let is_prop = {
            let tc = TypeChecker::with_mode(&self.env, self.env.mode());
            tc.infer_type(&type_expr)
                .ok()
                .is_some_and(|sort| sort.is_prop())
        };

        // Collect universe level params from the elaborated type (and value if
        // present) so the declaration includes all referenced params. Without
        // this, elaborated types referencing Eq's universe param `u_0` would
        // fail add_decl's level param validation. Part of #1385.
        let level_params = {
            let mut params = Vec::new();
            Self::collect_level_params_expr(&type_expr, &mut params);
            if let Some(ref val) = value_expr {
                Self::collect_level_params_expr(val, &mut params);
            }
            params
        };

        let decl = match value_expr {
            Some(val) if is_prop => Declaration::Theorem {
                name: Name::from_string(&def.name),
                level_params: level_params.clone(),
                type_: type_expr.clone(),
                value: val,
            },
            // Non-Prop valued definitions use Opaque to prevent WHNF unfolding
            // during subsequent type checking. Before #1385, all valued defs
            // were registered as Theorem (also opaque). Using Definition here
            // would make them semireducible, causing the type checker to attempt
            // expensive or infinite reductions when later definitions reference
            // these constants. Part of #1385.
            Some(val) => Declaration::Opaque {
                name: Name::from_string(&def.name),
                level_params: level_params.clone(),
                type_: type_expr.clone(),
                value: val,
            },
            None => Declaration::Axiom {
                name: Name::from_string(&def.name),
                level_params: level_params.clone(),
                type_: type_expr.clone(),
            },
        };

        Ok((def, decl))
    }

    /// Add a definition.
    pub fn add_definition(&mut self, def: SpecDefinition) -> Result<(), SpecError> {
        let (def, decl) = self.prepare_definition_decl(def)?;

        // Full kernel type checking via add_decl. Part of #1386.
        self.env
            .add_decl(decl)
            .map_err(|e| SpecError::TypeError(format!("add_decl: {e}")))?;

        self.definitions.insert(def.name.clone(), def);
        Ok(())
    }

    /// Add a definition whose value's inferred universes are aligned with its
    /// declared type before kernel registration.
    ///
    /// Use this for universe-POLYMORPHIC valued definitions (the `Eq.*` lemmas
    /// proved from `Eq.rec`): value inference freshens binder universes
    /// independently of the type, so they need a one-to-one rename before raw
    /// kernel registration. The alignment rejects collapsed/ambiguous universe
    /// mappings, and `add_decl` remains the final type-checking authority. For
    /// monomorphic definitions this is a no-op, so the helper stays opt-in.
    pub fn add_definition_checked(&mut self, def: SpecDefinition) -> Result<(), SpecError> {
        let (def, decl) = self.prepare_definition_decl_impl(def, ValueElab::AlignAgainstType)?;

        self.env
            .add_decl(decl)
            .map_err(|e| SpecError::TypeError(format!("add_decl: {e}")))?;

        self.definitions.insert(def.name.clone(), def);
        Ok(())
    }

    /// Register a definition ONLY if that name is not already registered.
    ///
    /// For declarations that legitimately appear in more than one module. The
    /// kernel rejects a second `add_decl` for the same name, so a module that
    /// re-registers a shared lemma cannot be wired into the live bundle
    /// alongside the module that already supplies it.
    ///
    /// SOUNDNESS CONDITION, and it is not automatic: this silently keeps the
    /// FIRST registration, so it is only correct when the two definitions agree.
    /// Every current caller was checked pairwise before adoption (byte-identical
    /// or alpha-equivalent). Do NOT reach for this to paper over a genuine
    /// disagreement — there the right fix is a rename, because skipping would
    /// silently change which statement the spec means.
    pub(crate) fn add_definition_if_absent(
        &mut self,
        def: SpecDefinition,
    ) -> Result<(), SpecError> {
        if self.definitions.contains_key(&def.name) {
            return Ok(());
        }
        self.add_definition(def)
    }

    /// `add_definition_structural`, skipped when the name is already registered.
    /// Same soundness condition as [`Self::add_definition_if_absent`].
    pub(crate) fn add_definition_structural_if_absent(
        &mut self,
        def: SpecDefinition,
    ) -> Result<(), SpecError> {
        if self.definitions.contains_key(&def.name) {
            return Ok(());
        }
        self.add_definition_structural(def)
    }

    /// Register a spec definition for a declaration that already exists in the
    /// environment.
    ///
    /// Use this when kernel-level `init_*` methods have already registered the
    /// declaration via `add_decl`. The spec definition is stored in the
    /// definitions HashMap (so proof verification can look it up) but no
    /// duplicate `add_decl` call is made.
    ///
    /// The elaborated_type is populated from the existing environment declaration.
    ///
    /// Part of #3333: Audit and fix placeholder DerivedProved proofs.
    pub(crate) fn register_existing_definition(
        &mut self,
        mut def: SpecDefinition,
    ) -> Result<(), SpecError> {
        let name = Name::from_string(&def.name);
        let type_expr = self
            .env
            .get_const(&name)
            .map(|d| d.type_.clone())
            .ok_or_else(|| {
                SpecError::ParseError(format!(
                    "register_existing_definition: '{}' not found in environment",
                    def.name
                ))
            })?;
        def.elaborated_type = Some(type_expr);
        self.definitions.insert(def.name.clone(), def);
        Ok(())
    }

    /// Add a definition through the checked registration path.
    ///
    /// This compatibility helper keeps older spec registration modules source
    /// stable while preserving the fail-closed behavior of `add_definition`.
    /// Uncheckable definitions must be fixed at the caller instead of falling
    /// back to structural insertion.
    pub(crate) fn add_definition_structural(
        &mut self,
        def: SpecDefinition,
    ) -> Result<(), SpecError> {
        self.add_definition(def)
    }
}
