// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Translation scope and stdlib mapping support.

use super::super::stdlib::{
    CoqStdlibInductiveMapping, COQ_STDLIB_INDUCTIVE_MAPPINGS,
    COQ_STDLIB_PROPOSITION_INDUCTIVE_MAPPINGS, COQ_STDLIB_PROPOSITION_MAPPINGS,
    COQ_STDLIB_PROPOSITION_TERM_MAPPINGS, COQ_STDLIB_TERM_MAPPINGS, COQ_STDLIB_TYPE_MAPPINGS,
};
use crate::{coq_import::CoqName, Name};
use hashbrown::HashMap;

/// Mapping for one Coq inductive family into Lean names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InductiveMapping {
    pub inductive: Name,
    pub cases_on: Name,
    pub constructors: Vec<Name>,
    pub projections: Vec<Name>,
}

impl InductiveMapping {
    #[must_use]
    pub fn new(inductive: Name) -> Self {
        let cases_on = Name::from_string(&format!("{inductive}.casesOn"));
        Self {
            inductive,
            cases_on,
            constructors: Vec::new(),
            projections: Vec::new(),
        }
    }

    #[must_use]
    pub fn with_cases_on(mut self, cases_on: Name) -> Self {
        self.cases_on = cases_on;
        self
    }

    #[must_use]
    pub fn with_constructors(mut self, constructors: impl Into<Vec<Name>>) -> Self {
        self.constructors = constructors.into();
        self
    }

    #[must_use]
    pub fn with_projections(mut self, projections: impl Into<Vec<Name>>) -> Self {
        self.projections = projections.into();
        self
    }
}

/// Translation environment for Coq terms.
#[derive(Debug, Clone)]
pub struct TranslationContext {
    locals: Vec<Option<String>>,
    globals: HashMap<CoqName, Name>,
    inductives: HashMap<CoqName, InductiveMapping>,
    pub(super) fix_skeleton: Name,
    pub(super) cofix_skeleton: Name,
    pub(super) fix_body_skeleton: Name,
}

impl Default for TranslationContext {
    fn default() -> Self {
        let mut ctx = Self::empty();
        ctx.install_default_mappings();
        ctx
    }
}

impl TranslationContext {
    #[must_use]
    pub fn empty() -> Self {
        Self {
            locals: Vec::new(),
            globals: HashMap::new(),
            inductives: HashMap::new(),
            fix_skeleton: Name::from_string("CoqImport.fix"),
            cofix_skeleton: Name::from_string("CoqImport.cofix"),
            fix_body_skeleton: Name::from_string("CoqImport.fixBody"),
        }
    }

    #[must_use]
    pub fn with_locals(locals: impl IntoIterator<Item = Option<String>>) -> Self {
        Self {
            locals: locals.into_iter().collect(),
            ..Self::default()
        }
    }

    #[must_use]
    pub fn locals(&self) -> &[Option<String>] {
        &self.locals
    }

    pub fn insert_global_mapping(&mut self, coq: CoqName, lean: Name) -> Option<Name> {
        self.globals.insert(coq, lean)
    }

    pub fn insert_inductive_mapping(
        &mut self,
        coq: CoqName,
        mapping: InductiveMapping,
    ) -> Option<InductiveMapping> {
        self.inductives.insert(coq, mapping)
    }

    #[must_use]
    pub fn lookup_global(&self, name: &CoqName) -> Option<&Name> {
        self.globals.get(name)
    }

    #[must_use]
    pub fn lookup_inductive(&self, name: &CoqName) -> Option<&InductiveMapping> {
        self.inductives.get(name)
    }

    pub fn import_stdlib_type_mappings(&mut self) {
        for mapping in COQ_STDLIB_TYPE_MAPPINGS {
            self.insert_global_aliases(mapping.coq_aliases, mapping.lean_name);
        }
        for mapping in COQ_STDLIB_TERM_MAPPINGS {
            self.insert_global_aliases(mapping.coq_aliases, mapping.lean_name);
        }
        self.insert_stdlib_inductive_mappings(COQ_STDLIB_INDUCTIVE_MAPPINGS);
    }

    pub fn import_stdlib_propositions(&mut self) {
        for mapping in COQ_STDLIB_PROPOSITION_MAPPINGS {
            self.insert_global_aliases(mapping.coq_aliases, mapping.lean_name);
        }
        for mapping in COQ_STDLIB_PROPOSITION_TERM_MAPPINGS {
            self.insert_global_aliases(mapping.coq_aliases, mapping.lean_name);
        }
        self.insert_stdlib_inductive_mappings(COQ_STDLIB_PROPOSITION_INDUCTIVE_MAPPINGS);
    }

    fn install_default_mappings(&mut self) {
        self.import_stdlib_type_mappings();
        self.import_stdlib_propositions();
    }

    fn insert_global_aliases(&mut self, aliases: &[&str], lean: &str) {
        let lean = Name::from_string(lean);
        for alias in aliases {
            self.globals
                .insert(CoqName::from_dotted(alias), lean.clone());
        }
    }

    fn insert_inductive_aliases(&mut self, aliases: &[&str], mapping: InductiveMapping) {
        for alias in aliases {
            self.inductives
                .insert(CoqName::from_dotted(alias), mapping.clone());
        }
    }

    fn insert_stdlib_inductive_mappings(&mut self, mappings: &[CoqStdlibInductiveMapping]) {
        for mapping in mappings {
            self.insert_inductive_aliases(mapping.coq_aliases, build_inductive_mapping(mapping));
        }
    }
}

fn build_inductive_mapping(mapping: &CoqStdlibInductiveMapping) -> InductiveMapping {
    let mut out = InductiveMapping::new(Name::from_string(mapping.lean_name));
    if !mapping.constructors.is_empty() {
        out = out.with_constructors(
            mapping
                .constructors
                .iter()
                .map(|name| Name::from_string(name))
                .collect::<Vec<_>>(),
        );
    }
    if !mapping.projections.is_empty() {
        out = out.with_projections(
            mapping
                .projections
                .iter()
                .map(|name| Name::from_string(name))
                .collect::<Vec<_>>(),
        );
    }
    out
}
