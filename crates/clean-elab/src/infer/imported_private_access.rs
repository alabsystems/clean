// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.8.0's refusals of another module's `private` structure from an
//! importer (G21 B3, `designs/2026-10-08-private-name-mangling.md`).
//!
//! A `private structure S` of module `M` is `_private.M.0.S`, and so are its
//! constructor and projections. Its plain name reaches nothing from an
//! importer (Lean's private step builds only the CURRENT module's prefix),
//! but a public term of type `S` still reaches the structure through its
//! TYPE: field notation, `⟨...⟩` and `{...}` read the structure off the
//! expected or inferred type. Lean refuses each of those when the projection
//! or constructor is private to another module
//! (`isPrivateNameFromImportedModule`), with the messages reproduced here
//! (measured on Lean 4.8.0, 2026-10-09, probes `Pkg/S2`, `S3`, `S5`).
//!
//! Lean does NOT refuse a method reached through dot notation, nor a
//! relative constructor `.c` (both accepted from an importer, `Pkg/S7`,
//! `S11`), so neither is checked here. Without a module name every private
//! name is plain, and nothing is refused (`docs/DECISIONS.md` R42).

use clean_kernel::Name;

use super::ElabCtx;
use crate::ElabError;

/// Which notation reached a structure's constructor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CtorNotation {
    /// `⟨...⟩` (Lean's `elabAnonymousConstructor`).
    Anonymous,
    /// `{ x := ... }` (Lean's `elabStructInst`).
    StructInstance,
}

impl ElabCtx<'_> {
    /// Refuse the field `field` of `struct_name` when its projection is
    /// private to another module (Lean's `resolveLValAux`: "field 'x' from
    /// structure '…' is private").
    pub(super) fn check_imported_private_field(
        &self,
        struct_name: &Name,
        field: &Name,
    ) -> Result<(), ElabError> {
        let projection = crate::namespace::append_names(struct_name, field);
        if self.is_imported_private_name(&projection) {
            return Err(ElabError::PrivateFromImportedModule {
                message: format!("field '{field}' from structure '{struct_name}' is private"),
            });
        }
        Ok(())
    }

    /// [`Self::check_imported_private_field`] for the numeric projection
    /// `.idx` (1-based) of the `structure` `struct_name`: Lean's
    /// `resolveLValAux` maps `.idx` to the field's projection function and
    /// refuses it with the FIELD's name ("field 'x' from structure '…' is
    /// private", measured on Lean 4.8.0 for `Foo.pubS.1`, G21 B3 review). A
    /// plain one-constructor `inductive` is projected with `Expr.proj` and
    /// never checked, so callers pass only a registered structure.
    pub(super) fn check_imported_private_field_index(
        &self,
        struct_name: &Name,
        idx: u32,
    ) -> Result<(), ElabError> {
        let field = usize::try_from(idx)
            .ok()
            .and_then(|idx| idx.checked_sub(1))
            .and_then(|pos| {
                self.env
                    .get_structure_field_names(struct_name)
                    .and_then(|fields| fields.get(pos).cloned())
            });
        match field {
            Some(field) => self.check_imported_private_field(struct_name, &field),
            None => Ok(()),
        }
    }

    /// Refuse an anonymous-constructor PATTERN `⟨...⟩` (the parser's
    /// `Prod.mk` placeholder, `written`) that destructures a value of the
    /// inductive `type_name` whose sole constructor is private to another
    /// module. Lean elaborates a pattern as a term, so `match s with | ⟨a, _⟩`,
    /// `fun ⟨a, _⟩ => …`, `let ⟨a, _⟩ := s` and an equation `| ⟨a, _⟩ => …`
    /// all reach `elabAnonymousConstructor` and its refusal (measured on Lean
    /// 4.8.0, G21 B3 review probes G3/G4/G5/G16/G17). A named constructor
    /// pattern `.mk a _` and the `cases`/`obtain` tactics are not refused
    /// (Lean accepts them), so only the placeholder is checked.
    pub(in crate::infer) fn check_imported_private_anon_pattern(
        &self,
        type_name: &Name,
        written: &clean_parser::SurfaceName,
    ) -> Result<(), ElabError> {
        if !written.same_syntax(&clean_parser::SurfaceName::generated_path("Prod.mk")) {
            return Ok(());
        }
        let Some(ind) = self.env.get_inductive(type_name) else {
            return Ok(());
        };
        let [sole_ctor] = ind.constructor_names.as_slice() else {
            return Ok(());
        };
        self.check_imported_private_ctor(type_name, sole_ctor, CtorNotation::Anonymous)
    }

    /// Refuse `⟨...⟩` / `{...}` notation whose constructor `ctor` (of the
    /// inductive `type_name`) is private to another module.
    pub(super) fn check_imported_private_ctor(
        &self,
        type_name: &Name,
        ctor: &Name,
        notation: CtorNotation,
    ) -> Result<(), ElabError> {
        if !self.is_imported_private_name(ctor) {
            return Ok(());
        }
        let form = match notation {
            CtorNotation::Anonymous => "⟨...⟩",
            CtorNotation::StructInstance => "{...}",
        };
        Err(ElabError::PrivateFromImportedModule {
            message: format!(
                "invalid {form} notation, constructor for `{type_name}` is marked as private"
            ),
        })
    }
}
