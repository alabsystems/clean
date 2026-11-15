// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only ownership audit for the exact pinned Init recursors.

use clean_kernel::env::Environment;
use clean_kernel::inductive::RecursorVal;
use clean_kernel::name::Name;
use std::collections::BTreeMap;

pub(super) type PinnedAuxiliaries = BTreeMap<Name, (Name, Name)>;

pub(super) fn pinned_auxiliaries() -> PinnedAuxiliaries {
    BTreeMap::from([
        (
            Name::from_string("Lean.Syntax.rec_1"),
            (Name::from_string("Lean.Syntax"), Name::from_string("Array")),
        ),
        (
            Name::from_string("Lean.Syntax.rec_2"),
            (Name::from_string("Lean.Syntax"), Name::from_string("List")),
        ),
    ])
}

#[derive(Debug, PartialEq, Eq)]
pub(super) enum Owner {
    Ordinary,
    PinnedAuxiliary,
}

#[derive(Debug, PartialEq, Eq)]
pub(super) enum OwnershipProblem {
    Ordinary(&'static str),
    Auxiliary(&'static str),
}

pub(super) fn audit_owner(
    env: &Environment,
    rec: &RecursorVal,
    pinned: &PinnedAuxiliaries,
) -> Result<Owner, OwnershipProblem> {
    // Classify exact pinned names first: their registered family root is
    // deliberately different from the container eliminated by their major.
    let auxiliary = pinned.get(&rec.name);
    let problem = |reason| match auxiliary {
        Some(_) => OwnershipProblem::Auxiliary(reason),
        None => OwnershipProblem::Ordinary(reason),
    };
    let major = rec
        .major_induct()
        .ok_or_else(|| problem("missing major type head"))?;
    if env.get_inductive(major).is_none() {
        return Err(problem("major inductive is not resident"));
    }
    if let Some((family, expected_major)) = auxiliary {
        let root = env
            .get_inductive(family)
            .ok_or_else(|| problem("family root is not resident"))?;
        if !root.is_nested || rec.inductive_name != *family || major != expected_major {
            return Err(problem("pinned nested family or container major disagrees"));
        }
        Ok(Owner::PinnedAuxiliary)
    } else {
        let family = &rec.inductive_name;
        let canonical_name =
            rec.name == family.clone().str("rec") || rec.name == family.clone().str("casesOn");
        if env.get_inductive(family).is_none() || family != major || !canonical_name {
            return Err(problem(
                "ordinary name, resident family and major must agree",
            ));
        }
        Ok(Owner::Ordinary)
    }
}

/// Exercise the same audit against cheap copies of the actual imported
/// records. No environment is cloned or mutated, and no rule check is skipped.
pub(super) fn assert_forged_owners_rejected(
    env: &Environment,
    pinned: &PinnedAuxiliaries,
) -> usize {
    let array = Name::from_string("Array");
    let list = Name::from_string("List");
    let source = env
        .get_recursor(&Name::from_string("Lean.Syntax.rec_1"))
        .expect("pinned Array auxiliary");
    let list_source = env
        .get_recursor(&Name::from_string("Lean.Syntax.rec_2"))
        .expect("pinned List auxiliary");
    assert_eq!(source.major_induct(), Some(&array));
    assert_eq!(list_source.major_induct(), Some(&list));
    assert_eq!(audit_owner(env, source, pinned), Ok(Owner::PinnedAuxiliary));
    assert_eq!(
        audit_owner(env, list_source, pinned),
        Ok(Owner::PinnedAuxiliary)
    );

    let mut forgeries = Vec::new();
    for (label, family) in [
        ("major relabeled as family", array.clone()),
        ("wrong resident family", list.clone()),
        ("missing family", Name::from_string("Ac1.MissingFamily")),
        ("legacy auxiliary self-label", source.name.clone()),
    ] {
        let mut forged = source.clone();
        forged.inductive_name = family;
        forgeries.push((label, forged));
    }
    // These have family == major. Only the exact ordinary-name binding can
    // prevent them from bypassing the frozen auxiliary inventory.
    for name in [
        "Lean.Syntax.rec_999",
        "Lean.Syntax.rec_0",
        "Lean.Syntax.rec_01",
        "Lean.Syntax.rec_x",
        "Lean.Syntax.rec_",
    ] {
        let mut forged = source.clone();
        forged.name = Name::from_string(name);
        forged.inductive_name = array.clone();
        assert_eq!(forged.major_induct(), Some(&forged.inductive_name));
        forgeries.push((name, forged));
    }
    let mut swapped = list_source.clone();
    swapped.name = source.name.clone();
    assert_eq!(swapped.major_induct(), Some(&list));
    forgeries.push(("swapped complete container recursor", swapped));
    let mut missing_major = source.clone();
    missing_major.type_ = clean_kernel::expr::Expr::prop();
    assert_eq!(missing_major.major_induct(), None);
    forgeries.push(("missing major binder", missing_major));
    for (label, forged) in &forgeries {
        assert!(
            audit_owner(env, forged, pinned).is_err(),
            "accepted forged ownership: {label}"
        );
    }

    // A pinned-table entry cannot excuse an absent or ordinary family root.
    for (family, expected_nested) in [("Ac1.MissingFamily", None), ("Nat", Some(false))] {
        let family = Name::from_string(family);
        assert_eq!(
            env.get_inductive(&family).map(|root| root.is_nested),
            expected_nested
        );
        let mut forged = source.clone();
        forged.inductive_name = family.clone();
        let mut wrong_roots = pinned.clone();
        wrong_roots.insert(forged.name.clone(), (family, array.clone()));
        assert!(
            audit_owner(env, &forged, &wrong_roots).is_err(),
            "accepted absent/non-nested root"
        );
    }
    forgeries.len() + 2
}
