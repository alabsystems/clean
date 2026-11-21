// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Untrusted comparison of one mounted environment with independently minted
//! semantic pins. The caller supplies the ownership inventory from the same
//! checked source graph as `environment` and the expected inventory from the
//! pinned Lean artifacts. This comparison does not establish that custody.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::{ConstantKind, Environment, Name};
use sha2::{Digest, Sha256};

use super::{MeaningDigests, MeaningError, Package};

mod checked_terms;
use checked_terms::compare_term_closure;

#[cfg(test)]
mod tests;

/// Module ownership, after accounting for reference-only compiler copies and
/// repeated artifact records during minting.
pub type ModuleOwnership = BTreeMap<Name, BTreeSet<Name>>;

/// An independently minted pin for a theorem statement or definition body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResidentPin {
    pub kind: ConstantKind,
    pub digest: String,
    pub meaning_closure: BTreeSet<Name>,
    pub axiom_closure: BTreeSet<Name>,
}

/// One refusal in structural module and declaration order.
#[derive(Debug, Eq, PartialEq, thiserror::Error)]
pub enum ResidentPinError {
    #[error("resident comparison has no expected modules or pins")]
    EmptyScope,
    #[error("mounted module inventory differs from pinned Lean")]
    Modules,
    #[error("mounted declaration owners differ from pinned Lean for {0}")]
    Ownership(Name),
    #[error("mounted module {module} contains {name}, outside the pinned package")]
    OutsidePackage { module: Name, name: Name },
    #[error("pinned declaration {0} has no mounted owner")]
    UnownedPin(Name),
    #[error("pinned declaration {0} is missing its checked definition or proof")]
    MissingValue(Name),
    #[error("pinned declaration {0} changed kind")]
    Kind(Name),
    #[error("pinned declaration {0} reaches axioms outside Ax0: {1:?}")]
    OutsideAx0(Name, BTreeSet<Name>),
    #[error("pinned declaration {0} changed its axiom closure")]
    AxiomClosure(Name),
    #[error("pinned declaration {0} changed its meaning closure")]
    MeaningClosure(Name),
    #[error("pinned declaration {0} changed its meaning digest")]
    Digest(Name),
    #[error("captured source inventory differs from the pinned modules")]
    SourceInventory,
    #[error("captured source bytes differ from the pin for {0}")]
    SourceDigest(Name),
    #[error("checked source and pinned reference use different theories")]
    Theory,
    #[error("independent reference did not reproduce the pins: {0}")]
    Reference(Box<ResidentPinError>),
    #[error("checked term differs from pinned Lean for {0}")]
    Term(Name),
    #[error(transparent)]
    Canonical(#[from] MeaningError),
}

/// Checked environments and input identities for comparing a changed digest.
///
/// The source caller supplies these captured bytes from the same source graph
/// that produced the fenced environment and its ownership inventory. The
/// expected digests are those minted for the independent pinned Lean run.
pub struct ResidentTermInputs<'a> {
    pub source: &'a clean_kernel::ReferenceKernel,
    pub reference: &'a clean_kernel::ReferenceKernel,
    pub reference_source_sha256: &'a BTreeMap<Name, [u8; 32]>,
    pub captured_sources: &'a BTreeMap<Name, &'a [u8]>,
}

/// Compare exact pinned meaning and Ax0 for the selected roots. A different
/// digest reports a mismatch so an ensuing comparison can use the separately
/// pinned kernel term. The lookup alone grants no authority or proof status.
pub fn compare_resident_pins(
    environment: &Environment,
    package: &Package,
    expected_ownership: &ModuleOwnership,
    actual_ownership: &ModuleOwnership,
    pins: &BTreeMap<Name, ResidentPin>,
) -> Result<(), ResidentPinError> {
    compare_resident(
        environment,
        package,
        expected_ownership,
        actual_ownership,
        pins,
        |name, _| Err(ResidentPinError::Digest(name.clone())),
    )
}

/// Compare the same captured source with independently checked pinned terms
/// when exact canonical meaning differs. Every root still requires exact
/// module ownership, the pinned closure names and the recorded Ax0 closure.
///
/// The original source manifest and the captured graph must be supplied
/// by the same build that produced the compared source environment.
///
/// # Errors
///
/// Reports the first source, ownership, theory, axiom or kernel term mismatch.
pub fn compare_resident_pins_with_terms(
    inputs: &ResidentTermInputs<'_>,
    package: &Package,
    expected_ownership: &ModuleOwnership,
    actual_ownership: &ModuleOwnership,
    pins: &BTreeMap<Name, ResidentPin>,
) -> Result<(), ResidentPinError> {
    if inputs.source.theory_id() != inputs.reference.theory_id() {
        return Err(ResidentPinError::Theory);
    }
    if !inputs
        .reference_source_sha256
        .keys()
        .eq(expected_ownership.keys())
        || !inputs.captured_sources.keys().eq(expected_ownership.keys())
    {
        return Err(ResidentPinError::SourceInventory);
    }
    for (module, actual) in inputs.captured_sources {
        let observed: [u8; 32] = Sha256::digest(actual).into();
        if observed != inputs.reference_source_sha256[module] {
            return Err(ResidentPinError::SourceDigest(module.clone()));
        }
    }

    let source = inputs.source.environment();
    let reference = inputs.reference.environment();
    compare_resident_pins(
        reference,
        package,
        expected_ownership,
        expected_ownership,
        pins,
    )
    .map_err(|error| ResidentPinError::Reference(Box::new(error)))?;
    let mut compared = BTreeSet::new();
    compare_resident(
        source,
        package,
        expected_ownership,
        actual_ownership,
        pins,
        |_, pin| compare_term_closure(source, reference, &pin.meaning_closure, &mut compared),
    )
}

fn compare_resident(
    environment: &Environment,
    package: &Package,
    expected_ownership: &ModuleOwnership,
    actual_ownership: &ModuleOwnership,
    pins: &BTreeMap<Name, ResidentPin>,
    mut compare_mismatch: impl FnMut(&Name, &ResidentPin) -> Result<(), ResidentPinError>,
) -> Result<(), ResidentPinError> {
    if expected_ownership.is_empty() || pins.is_empty() {
        return Err(ResidentPinError::EmptyScope);
    }
    if !expected_ownership.keys().eq(actual_ownership.keys()) {
        return Err(ResidentPinError::Modules);
    }
    let mut owned = BTreeSet::new();
    for (module, declarations) in actual_ownership {
        if declarations != &expected_ownership[module] {
            return Err(ResidentPinError::Ownership(module.clone()));
        }
        if let Some(name) = declarations.difference(package.names()).next() {
            return Err(ResidentPinError::OutsidePackage {
                module: module.clone(),
                name: name.clone(),
            });
        }
        owned.extend(declarations);
    }
    let ax0: BTreeSet<_> = [
        "propext",
        "Quot.sound",
        "Quot",
        "Quot.mk",
        "Quot.lift",
        "Quot.ind",
    ]
    .into_iter()
    .map(Name::from_string)
    .collect();
    let observed = MeaningDigests::new(environment, package);
    for (name, pin) in pins {
        if !owned.contains(name) {
            return Err(ResidentPinError::UnownedPin(name.clone()));
        }
        let info = environment
            .get_const(name)
            .filter(|info| info.value.is_some())
            .ok_or_else(|| ResidentPinError::MissingValue(name.clone()))?;
        if info.kind != pin.kind
            || !matches!(pin.kind, ConstantKind::Definition | ConstantKind::Theorem)
        {
            return Err(ResidentPinError::Kind(name.clone()));
        }
        let domain_axioms = environment
            .axiom_deps(name)
            .ok_or_else(|| ResidentPinError::MissingValue(name.clone()))?;
        let foundational_axioms: BTreeSet<_> = environment
            .foundational_axiom_deps(name)
            .ok_or_else(|| ResidentPinError::MissingValue(name.clone()))?
            .into_iter()
            .collect();
        let forbidden: BTreeSet<_> = domain_axioms
            .into_iter()
            .chain(foundational_axioms.difference(&ax0).cloned())
            .collect();
        if !forbidden.is_empty() {
            return Err(ResidentPinError::OutsideAx0(name.clone(), forbidden));
        }
        if foundational_axioms != pin.axiom_closure {
            return Err(ResidentPinError::AxiomClosure(name.clone()));
        }
        if observed.closure(name)? != pin.meaning_closure {
            return Err(ResidentPinError::MeaningClosure(name.clone()));
        }
        if observed.digest(name)? != pin.digest {
            compare_mismatch(name, pin)?;
        }
    }
    Ok(())
}
