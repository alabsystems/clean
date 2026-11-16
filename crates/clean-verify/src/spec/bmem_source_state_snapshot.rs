// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact captured-data comparison without expanding shared expression trees.
//! This observes the existing JSON projection plus the explicitly named state
//! below. Skipped runtime registries, caches and authority are not covered.

use super::super::{AxiomCategory, ProofStatus};
use super::{DeclarationVerification, Expr, Name, SpecDefinition, Specification};
use clean_kernel::env::{CheckerSettings, JsonEnvironment};
use std::{collections::HashSet, time::Instant};

#[derive(Debug, PartialEq)]
struct DefinitionSnapshot {
    name: String,
    type_src: String,
    value_src: Option<String>,
    is_axiom: bool,
    category: AxiomCategory,
    proof_status: ProofStatus,
    description: String,
    elaborated_type: Option<Expr>,
    elaborated_value: Option<Expr>,
    dependencies: Option<HashSet<String>>,
    axiom_deps: HashSet<String>,
}

impl From<&SpecDefinition> for DefinitionSnapshot {
    fn from(def: &SpecDefinition) -> Self {
        // No rest pattern: newly added definition fields must be classified.
        let SpecDefinition {
            name,
            type_src,
            value_src,
            is_axiom,
            category,
            proof_status,
            description,
            elaborated_type,
            elaborated_value,
            dependencies,
            axiom_deps,
        } = def;
        Self {
            name: name.clone(),
            type_src: type_src.clone(),
            value_src: value_src.clone(),
            is_axiom: *is_axiom,
            category: *category,
            proof_status: *proof_status,
            description: description.clone(),
            elaborated_type: elaborated_type.clone(),
            elaborated_value: elaborated_value.clone(),
            dependencies: dependencies.clone(),
            axiom_deps: axiom_deps.clone(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub(super) struct StateSnapshot {
    pub(super) serialized: JsonEnvironment,
    pub(super) checker_settings: CheckerSettings,
    pub(super) generation: u64,
    definitions: Vec<(String, DefinitionSnapshot)>,
    provenance: Vec<(
        Name,
        Option<DeclarationVerification>,
        Option<clean_kernel::ConstantOrigin>,
    )>,
}

pub(super) fn snapshot(spec: &Specification) -> StateSnapshot {
    let started = Instant::now();
    eprintln!("bmem-source-snapshot stage=definitions-before");
    let mut definitions: Vec<_> = spec
        .definitions()
        .iter()
        .map(|(key, def)| (key.clone(), DefinitionSnapshot::from(def)))
        .collect();
    definitions.sort_by(|a, b| a.0.cmp(&b.0));
    eprintln!(
        "bmem-source-snapshot stage=definitions-after count={} seconds={:.6}",
        definitions.len(),
        started.elapsed().as_secs_f64()
    );
    eprintln!("bmem-source-snapshot stage=environment-before");
    // Preserve the existing projection's vector order and every typed field.
    let serialized = spec.env().json_observation();
    eprintln!(
        "bmem-source-snapshot stage=environment-after seconds={:.6}",
        started.elapsed().as_secs_f64()
    );
    eprintln!("bmem-source-snapshot stage=provenance-before");
    let mut provenance: Vec<_> = spec
        .env()
        .constants()
        .map(|c| {
            (
                c.name.clone(),
                spec.env().declaration_verification(&c.name),
                spec.env().get_constant_origin(&c.name).cloned(),
            )
        })
        .collect();
    provenance.sort_by_key(|entry| entry.0.to_unambiguous_string());
    eprintln!(
        "bmem-source-snapshot stage=provenance-after count={} seconds={:.6}",
        provenance.len(),
        started.elapsed().as_secs_f64()
    );
    let result = StateSnapshot {
        serialized,
        checker_settings: spec.env().checker_settings(),
        generation: spec.env().generation(),
        definitions,
        provenance,
    };
    eprintln!(
        "bmem-source-snapshot stage=complete seconds={:.6}",
        started.elapsed().as_secs_f64()
    );
    result
}
