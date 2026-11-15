// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A module's inductive-family members as its `.olean` stores them, for the
//! re-check lanes that compare them with the kernel's regeneration.

use super::convert::{
    convert_constructor_val, convert_inductive_val, convert_recursor_val_partial,
};
use super::ExprInternCache;
use crate::module::ConstantKind;
use clean_kernel::inductive::{ConstructorVal, InductiveVal, RecursorVal};

/// A module's inductive-family members as its `.olean` STORES them, converted
/// exactly as the loader converts them for registration (a recursor rule's
/// `recursive_fields` is left empty: Clean derives it from the environment,
/// and Lean's replay comparison has no such field), plus every member that did
/// not convert, with the reason.
#[derive(Debug, Default)]
pub struct StoredFamilyMembers {
    /// Stored inductive types.
    pub inductives: Vec<InductiveVal>,
    /// Stored constructors.
    pub constructors: Vec<ConstructorVal>,
    /// Stored recursors.
    pub recursors: Vec<RecursorVal>,
    /// Members that did not convert (name, reason).
    pub unconvertible: Vec<(String, String)>,
}

/// Read the stored inductive-family members of `module` (see
/// [`StoredFamilyMembers`]), for a re-check lane that has the kernel regenerate
/// each block and must compare the STORED members with the generated ones, as
/// Lean's replay does (`checkPostponedConstructors` /
/// `checkPostponedRecursors`).
#[must_use]
pub fn stored_family_members(module: &crate::module::ParsedModule) -> StoredFamilyMembers {
    let mut out = StoredFamilyMembers::default();
    let mut intern = ExprInternCache::with_capacity(1024);
    for constant in &module.constants {
        match constant.kind {
            ConstantKind::Inductive => match convert_inductive_val(constant, &mut intern).0 {
                Ok(val) => out.inductives.push(val),
                Err(e) => out
                    .unconvertible
                    .push((constant.name.clone(), e.to_string())),
            },
            ConstantKind::Constructor => match convert_constructor_val(constant, &mut intern).0 {
                Ok(val) => out.constructors.push(val),
                Err(e) => out
                    .unconvertible
                    .push((constant.name.clone(), e.to_string())),
            },
            ConstantKind::Recursor => match convert_recursor_val_partial(constant, &mut intern).0 {
                Ok((val, _, _)) => out.recursors.push(val),
                Err(e) => out
                    .unconvertible
                    .push((constant.name.clone(), e.to_string())),
            },
            _ => {}
        }
    }
    out
}
