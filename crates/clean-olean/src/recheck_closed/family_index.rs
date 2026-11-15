// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The recursor-by-family index the cone walk and the replay share.

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use std::collections::BTreeMap;

/// Recursor names grouped by the inductive family they eliminate, built once so
/// the cone walk does not rescan every recursor per family.
pub(super) struct FamilyIndex {
    recursors_by_family: BTreeMap<Name, Vec<Name>>,
}

impl FamilyIndex {
    pub(super) fn build(env: &Environment) -> Self {
        let mut recursors_by_family: BTreeMap<Name, Vec<Name>> = BTreeMap::new();
        for rec in env.recursors() {
            recursors_by_family
                .entry(rec.inductive_name.clone())
                .or_default()
                .push(rec.name.clone());
        }
        for names in recursors_by_family.values_mut() {
            names.sort();
        }
        Self {
            recursors_by_family,
        }
    }

    pub(super) fn recursors(&self, family: &Name) -> &[Name] {
        self.recursors_by_family
            .get(family)
            .map_or(&[][..], Vec::as_slice)
    }
}
