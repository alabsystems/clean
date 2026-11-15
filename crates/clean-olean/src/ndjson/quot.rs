// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The quotient: `quot` records in, `Environment::add_quot` the only way the
//! primitives enter.

use std::collections::BTreeMap;

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_kernel::quot::init_quot_vals;

use super::decl::ExportHeader;
use super::load::{rename_level_params, same_modulo_binder_info};
use crate::module::ParsedQuotKind;

/// Install the quotient for an export that has `quot` records, refusing (into
/// `refused`) every record that cannot be the kernel's own.
///
/// 1. Each record's stored type must be the type `add_quot` builds for its
///    name, up to binder information and universe-parameter names.
/// 2. An `axiom Quot.sound` of the export (`declared_sound`; Lean declares it
///    in `Init.Core`) must have the type the kernel's quotient gives it, since
///    `add_quot` installs that one under its name; the export's own record is
///    never registered.
/// 3. `add_quot` must accept the resident `Eq` (Lean's `check_eq_type`); if
///    it does not, nothing is installed and every record (and the export's
///    `Quot.sound`) is refused.
pub(crate) fn admit_quotient(
    env: &mut Environment,
    quots: &[(ExportHeader, ParsedQuotKind)],
    declared_sound: Option<&ExportHeader>,
    refused: &mut BTreeMap<Name, String>,
) {
    let canonical = init_quot_vals();
    for (header, _kind) in quots {
        let Some(built) = canonical.iter().find(|c| c.name == header.name) else {
            refused.insert(
                header.name.clone(),
                "not a declaration of Lean's quotient".to_owned(),
            );
            continue;
        };
        if header.level_params.len() != built.level_params.len() {
            refused.insert(
                header.name.clone(),
                format!(
                    "the stored quotient declaration has {} universe parameter(s), the kernel's \
                     has {}",
                    header.level_params.len(),
                    built.level_params.len()
                ),
            );
            continue;
        }
        let stored = rename_level_params(&header.type_, &header.level_params, &built.level_params);
        if !same_modulo_binder_info(&stored, &built.type_) {
            refused.insert(
                header.name.clone(),
                "the stored type is not the type Lean's `quotDecl` gives it".to_owned(),
            );
        }
    }

    let sound = Name::from_string("Quot.sound");
    if let Some(declared) = declared_sound {
        let agrees = canonical
            .iter()
            .find(|c| c.name == sound)
            .is_some_and(|built| {
                declared.level_params.len() == built.level_params.len()
                    && same_modulo_binder_info(
                        &rename_level_params(
                            &declared.type_,
                            &declared.level_params,
                            &built.level_params,
                        ),
                        &built.type_,
                    )
            });
        if !agrees {
            refused.insert(
                sound.clone(),
                "the export's `Quot.sound` is not the axiom the kernel's quotient states, and \
                 `add_quot` installs that one under its name"
                    .to_owned(),
            );
        }
    }

    if let Err(reason) = env.add_quot() {
        let names = quots
            .iter()
            .map(|(header, _)| &header.name)
            .chain(declared_sound.map(|h| &h.name));
        for name in names {
            refused.entry(name.clone()).or_insert_with(|| {
                format!("Lean's add_quot refuses to install the quotient: {reason}")
            });
        }
    }
}
