// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The recursor-by-family index the cone walk and the replay share.

use clean_kernel::env::{ConstantKind, Environment};
use clean_kernel::inductive::{RecursorArgOrder, RecursorVal};
use clean_kernel::name::{Name, NameInner};
use std::collections::{BTreeMap, BTreeSet};

/// Recursor names grouped by the inductive family they eliminate, built once so
/// the cone walk does not rescan every recursor per family.
pub(super) struct FamilyIndex {
    recursors_by_family: BTreeMap<Name, Vec<Name>>,
    source_wrappers_by_family: BTreeMap<Name, Vec<Name>>,
}

impl FamilyIndex {
    pub(super) fn build(env: &Environment) -> Self {
        Self::with_source_wrappers(env, &BTreeSet::new())
    }

    pub(super) fn with_source_wrappers(env: &Environment, source_owned: &BTreeSet<Name>) -> Self {
        let mut recursors_by_family: BTreeMap<Name, Vec<Name>> = BTreeMap::new();
        let mut source_wrappers_by_family: BTreeMap<Name, Vec<Name>> = BTreeMap::new();
        for rec in env.recursors() {
            let by_family = if is_source_wrapper(env, source_owned, rec) {
                &mut source_wrappers_by_family
            } else {
                &mut recursors_by_family
            };
            by_family
                .entry(rec.inductive_name.clone())
                .or_default()
                .push(rec.name.clone());
        }
        for names in recursors_by_family
            .values_mut()
            .chain(source_wrappers_by_family.values_mut())
        {
            names.sort();
        }
        Self {
            recursors_by_family,
            source_wrappers_by_family,
        }
    }

    pub(super) fn is_source_wrapper(&self, name: &Name) -> bool {
        let NameInner::Str(parent, _) = name.inner() else {
            return false;
        };
        self.source_wrappers(parent).contains(name)
    }

    pub(super) fn source_wrappers(&self, family: &Name) -> &[Name] {
        self.source_wrappers_by_family
            .get(family)
            .map_or(&[][..], Vec::as_slice)
    }

    pub(super) fn recursors(&self, family: &Name) -> &[Name] {
        self.recursors_by_family
            .get(family)
            .map_or(&[][..], Vec::as_slice)
    }
}

/// These source-generated wrappers compute through their values in Lean's
/// theory. The suffix selects the wrapper only when the source owns the
/// matching family and headers. Only the defining term enters replay, through
/// ordinary admission, and the dependency fingerprint includes that term.
fn is_source_wrapper(env: &Environment, source_owned: &BTreeSet<Name>, rec: &RecursorVal) -> bool {
    if !source_owned.contains(&rec.name)
        || !source_owned.contains(&rec.inductive_name)
        || rec.arg_order != RecursorArgOrder::MajorAfterMotive
    {
        return false;
    }
    let NameInner::Str(parent, suffix) = rec.name.inner() else {
        return false;
    };
    parent.as_ref() == &rec.inductive_name
        && matches!(suffix.as_ref(), "casesOn" | "recOn")
        && env
            .get_inductive(&rec.inductive_name)
            .is_some_and(|ind| ind.name == rec.inductive_name)
        && env.get_const(&rec.name).is_some_and(|info| {
            info.name == rec.name
                && info.kind == ConstantKind::Definition
                && info.level_params == rec.level_params
                && info.type_ == rec.type_
                && info.value.is_some()
        })
}
