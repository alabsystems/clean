// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which constants a module's inductive families need resident before the
//! demand walk registers them (decision R147).
//!
//! Registering a family regenerates its recursors from the stored inductive
//! and constructors and compares them with the stored ones
//! (`clean-kernel` `env/imported_family.rs`). Regeneration reduces the type
//! former to find the family's result sort, and infers its fields' sorts to
//! decide large elimination, so every constant those types name must be
//! resident first, as it is in Lean's import, where every imported
//! declaration is present before a module's families are added. The demand
//! walk loads one constant at a time and used to register a family the moment
//! it met one of its names, before the definitions its types name: an honest,
//! Lean-checked `inductive HSD : HSDSort` with `HSDSort := Type` imported had
//! its recursor refused ("Invalid recursor HSD.rec"), and every declaration
//! using the family with it (fixture `ReplayHonestSortDef`).

use std::collections::HashSet;
use std::path::Path;

use clean_kernel::Name;
use clean_olean::ConstantKind as OleanKind;

use super::{collect_parsed_consts, Walker};

impl Walker<'_> {
    /// Whether `olean`'s inductive families are registered.
    pub(super) fn families_loaded(&self, olean: &Path) -> bool {
        self.inductive_loaded.contains(olean)
    }

    /// The constants the types of `olean`'s inductives and constructors name,
    /// other than the module's own family members (registered together with
    /// the family), in sorted order so the walk stays deterministic (see
    /// `push_refs`). Empty when the module cannot be parsed, which
    /// `load_inductive_families` then handles as before.
    pub(super) fn family_type_deps(&mut self, olean: &Path) -> Vec<Name> {
        if let Some(deps) = self.family_deps.get(olean) {
            return deps.clone();
        }
        if !self.ensure_parsed(olean, true) {
            return Vec::new();
        }
        let Some(module) = self.parsed.get(olean) else {
            return Vec::new();
        };
        let is_family =
            |kind: &OleanKind| matches!(kind, OleanKind::Inductive | OleanKind::Constructor);
        let own: HashSet<Name> = module
            .constants
            .iter()
            .filter(|c| is_family(&c.kind) || matches!(c.kind, OleanKind::Recursor))
            .map(|c| Name::from_string(&c.name))
            .collect();
        let mut refs = HashSet::new();
        for c in module.constants.iter().filter(|c| is_family(&c.kind)) {
            if let Some(ty) = &c.type_ {
                collect_parsed_consts(ty, &mut refs);
            }
        }
        let mut deps: Vec<Name> = refs.into_iter().filter(|n| !own.contains(n)).collect();
        deps.sort_unstable();
        self.family_deps.insert(olean.to_path_buf(), deps.clone());
        deps
    }
}
