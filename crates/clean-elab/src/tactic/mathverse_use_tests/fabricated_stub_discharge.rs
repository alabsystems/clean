// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Test code by its own head: the source gates read a file-level #![cfg(test)]
// as proof (headed_cfg_test in scripts/check_add_decl_ratchet.py).
#![cfg(test)]

use super::super::mathverse_use::{
    discharge_fabricated_stubs_for, restore_unreplaced_stubs, TrustGate,
};
use super::*;
use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_kernel::name::Name;
use clean_kernel::Declaration;
use clean_mathverse::library::MathverseLibrary;
use clean_mathverse::premise_select::{MatchReason, PremiseCandidate};
use clean_mathverse::shard::{ShardReader, ShardWriter};
use clean_mathverse::trust::policy::TrustPolicy;
use clean_mathverse::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    TrustLevel, NO_VALUE,
};

type Row<'a> = (&'a str, ImportConfidence, DeclKind, bool);

/// A shard where constant 0 is the cited theorem and every later constant is
/// one of its dependencies.
fn shard_with_deps(rows: &[Row<'_>]) -> MathverseLibrary {
    shard_with_closure_and_extras(rows, &[])
}

/// As [`shard_with_deps`], plus `extras`: rows the shard declares that are
/// NOT in the cited theorem's dependency closure (a family's constructor
/// that the closure never names, as `Fact.mk` is for `Fact.out`).
fn shard_with_closure_and_extras(closure: &[Row<'_>], extras: &[Row<'_>]) -> MathverseLibrary {
    let mut writer = ShardWriter::new();
    let l0 = writer.add_level(FlatLevel::zero());
    let sort0 = writer.add_expr(FlatExpr::sort(l0));
    for &(name, confidence, decl_kind, has_value) in closure.iter().chain(extras) {
        let name_idx = writer.add_string(name);
        writer.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx: sort0,
            value_idx: if has_value { sort0 } else { NO_VALUE },
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: confidence as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: decl_kind as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
    }
    let mut buf = Vec::new();
    writer.write(&mut buf).expect("shard must serialize");
    let reader = ShardReader::from_bytes(&buf).expect("shard must parse");
    let mut lib = MathverseLibrary::new(TrustPolicy::permissive());
    lib.load_shard(&reader).expect("shard must load");
    for dep in 1..closure.len() as u32 {
        lib.add_dependency(0, dep);
    }
    lib
}

/// `Fact.out`'s closure (`Fact`), with `Fact.mk` declared beside it.
fn fact_closure_with_constructor_row() -> MathverseLibrary {
    shard_with_closure_and_extras(
        &[
            (
                "Fact.out",
                ImportConfidence::KernelVerified,
                DeclKind::Theorem,
                true,
            ),
            (
                "Fact",
                ImportConfidence::SourceVerified,
                DeclKind::Inductive,
                true,
            ),
        ],
        &[(
            "Fact.mk",
            ImportConfidence::SourceVerified,
            DeclKind::Constructor,
            false,
        )],
    )
}

fn candidate(lib: &MathverseLibrary) -> PremiseCandidate {
    let header = *lib.get_constant(0).expect("root header");
    PremiseCandidate {
        name: lib.get_name(0).expect("root name").to_string(),
        constant_idx: 0,
        score: 1.0,
        source_system: SourceSystem::Lean4,
        trust_level: TrustLevel::KernelVerified,
        match_reason: MatchReason::TypeUnification,
        header,
    }
}

/// A value-free `Axiom` of type `Prop` — the shape every prelude carrier
/// stub has.
fn seed_axiom_stub(env: &mut Environment, name: &str) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    })
    .expect("axiom stub must register");
}

fn seed_definition(env: &mut Environment, name: &str) {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        // `Sort 1 := Prop` — a value-bearing declaration, the shape
        // `Finset` actually has in the prelude.
        type_: Expr::sort(Level::succ(Level::zero())),
        value: Expr::sort(Level::zero()),
        is_reducible: true,
    })
    .expect("definition must register");
}

fn resident(env: &Environment, name: &str) -> bool {
    env.get_const(&Name::from_string(name)).is_some()
}

#[test]
fn test_discharge_retires_axiom_stub_shadowing_an_inductive_row() {
    let lib = shard_with_deps(&[
        (
            "thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "Fact",
            ImportConfidence::SourceVerified,
            DeclKind::Inductive,
            true,
        ),
    ]);
    let mut env = Environment::default();
    seed_axiom_stub(&mut env, "Fact");

    let taken = discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

    assert_eq!(taken.len(), 1, "the shadowing stub must be retired");
    assert!(
        !resident(&env, "Fact"),
        "`Fact` must be absent so the checked family replay can install the genuine structure"
    );
}

#[test]
fn test_discharge_sweeps_family_members_outside_the_closure() {
    // THE MEASURED REGRESSION. `Fact.out`'s closure names `Fact` but NOT
    // `Fact.mk`, so a closure-only discharge left `Fact.mk`'s stub in place
    // and `add_inductive` aborted with `Duplicate declaration: Fact.mk` —
    // which the trust gate then misreported as `Fact ... below Strict`.
    // The shard declares `Fact.mk` outside the closure, so the member
    // authenticates against its own row before it is removed.
    let lib = fact_closure_with_constructor_row();
    let mut env = Environment::default();
    seed_axiom_stub(&mut env, "Fact");
    seed_axiom_stub(&mut env, "Fact.mk");

    let taken = discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

    assert_eq!(taken.len(), 2, "head and its namespace member must both go");
    assert!(!resident(&env, "Fact"));
    assert!(
        !resident(&env, "Fact.mk"),
        "a constructor stub the closure never mentions still collides with add_inductive"
    );
}

#[test]
fn test_discharge_keeps_a_member_stub_the_shard_does_not_declare() {
    // AUTHENTICATE BEFORE REMOVAL: a carrier with no shard row of its own
    // name has nothing to be checked against, so it stays resident and the
    // residency rule refuses the citation on its own diagnostic.
    let lib = shard_with_deps(&[
        (
            "Fact.out",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "Fact",
            ImportConfidence::SourceVerified,
            DeclKind::Inductive,
            true,
        ),
    ]);
    let mut env = Environment::default();
    seed_axiom_stub(&mut env, "Fact");
    seed_axiom_stub(&mut env, "Fact.mk");

    let taken = discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

    assert_eq!(
        taken.len(),
        1,
        "only the head, which has a row, is discharged"
    );
    assert!(!resident(&env, "Fact"));
    assert!(
        resident(&env, "Fact.mk"),
        "a member the shard never declares must not be removed"
    );
}

#[test]
fn test_discharge_keeps_a_carrier_whose_type_disagrees_with_its_row() {
    // The row exists, but its type (`Prop`) is not the carrier's (`Type`):
    // everything checked against the carrier would describe a different
    // constant after the swap, so the carrier stays.
    let lib = shard_with_deps(&[
        (
            "thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "Fact",
            ImportConfidence::SourceVerified,
            DeclKind::Inductive,
            true,
        ),
    ]);
    let mut env = Environment::default();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Fact"),
        level_params: vec![],
        type_: Expr::sort(Level::succ(Level::zero())),
    })
    .expect("axiom stub must register");

    let taken = discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

    assert!(taken.is_empty(), "a disagreeing type is never discharged");
    assert!(resident(&env, "Fact"));
}

#[test]
fn test_discharge_never_touches_a_genuine_value_free_axiom_row() {
    // `propext` is a real axiom on BOTH sides. Removing it would delete a
    // foundational assumption the citation legitimately depends on.
    let lib = shard_with_deps(&[
        (
            "thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "propext",
            ImportConfidence::SourceVerified,
            DeclKind::Axiom,
            false,
        ),
    ]);
    let mut env = Environment::default();
    seed_axiom_stub(&mut env, "propext");

    let taken = discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

    assert!(
        taken.is_empty(),
        "an Axiom shard row is never a fabrication"
    );
    assert!(resident(&env, "propext"));
}

#[test]
fn test_discharge_never_touches_quotient_primitives() {
    // `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` are kernel primitives whose
    // prelude axioms ARE the correct representation; the shard's `Quot` rows
    // must not displace them.
    let lib = shard_with_deps(&[
        (
            "thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "Quot",
            ImportConfidence::KernelVerified,
            DeclKind::Quot,
            true,
        ),
        (
            "Quot.mk",
            ImportConfidence::KernelVerified,
            DeclKind::Quot,
            true,
        ),
    ]);
    let mut env = Environment::default();
    seed_axiom_stub(&mut env, "Quot");
    seed_axiom_stub(&mut env, "Quot.mk");

    let taken = discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

    assert!(taken.is_empty(), "Quot rows are excluded by kind");
    assert!(resident(&env, "Quot"));
    assert!(resident(&env, "Quot.mk"));
}

#[test]
fn test_discharge_requires_kernel_verified_for_value_bearing_rows() {
    // A value-bearing row that the gate would REJECT must not displace the
    // resident carrier: doing so turns a citation that passes today into a
    // failure without putting anything checked in its place.
    let lib = shard_with_deps(&[
        (
            "thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "Helper",
            ImportConfidence::SourceVerified,
            DeclKind::Definition,
            true,
        ),
    ]);
    let mut env = Environment::default();
    seed_axiom_stub(&mut env, "Helper");

    let taken = discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

    assert!(taken.is_empty());
    assert!(resident(&env, "Helper"));
}

#[test]
fn test_discharge_retires_axiom_stub_shadowing_a_proved_theorem_row() {
    // The SILENT half: kinds do not clash, so the residency rule admits the
    // stub by design and the loader never installs the real proof. Without
    // this arm a by-name citation of `Fact.out` closes against Clean's own
    // assumption.
    let lib = shard_with_deps(&[
        (
            "thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "Fact.out",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
    ]);
    let mut env = Environment::default();
    seed_axiom_stub(&mut env, "Fact.out");

    let taken = discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

    assert_eq!(taken.len(), 1);
    assert!(!resident(&env, "Fact.out"));
}

#[test]
fn test_discharge_never_touches_a_value_bearing_resident() {
    // `Finset` is seeded as a reducible DEFINITION, not an axiom. Removing a
    // value-bearing declaration would strand every prelude constant typed in
    // terms of it, so the predicate must refuse it.
    let lib = shard_with_deps(&[
        (
            "thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "Finset",
            ImportConfidence::SourceVerified,
            DeclKind::Inductive,
            true,
        ),
    ]);
    let mut env = Environment::default();
    seed_definition(&mut env, "Finset");

    let taken = discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);

    assert!(taken.is_empty(), "a value-bearing resident is not a stub");
    assert!(resident(&env, "Finset"));
}

#[test]
fn test_discharge_is_inert_under_the_relaxed_gate() {
    // `Relaxed` is the explicitly weaker bang-variant gate and keeps its
    // previous behavior, exactly as the residency rule does.
    let lib = shard_with_deps(&[
        (
            "thm",
            ImportConfidence::KernelVerified,
            DeclKind::Theorem,
            true,
        ),
        (
            "Fact",
            ImportConfidence::SourceVerified,
            DeclKind::Inductive,
            true,
        ),
    ]);
    let mut env = Environment::default();
    seed_axiom_stub(&mut env, "Fact");

    let taken =
        discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Relaxed);

    assert!(taken.is_empty());
    assert!(resident(&env, "Fact"));
}

#[test]
fn test_restore_puts_the_stub_back_and_flags_the_closure_member() {
    // Nothing installed the genuine declaration, so the session must be left
    // exactly as it was found AND the caller must be told, so it can refuse
    // to report a citation that would rest on the restored fabrication.
    let lib = fact_closure_with_constructor_row();
    let mut env = Environment::default();
    seed_axiom_stub(&mut env, "Fact");
    seed_axiom_stub(&mut env, "Fact.mk");
    let before = env.get_const(&Name::from_string("Fact")).map(|c| {
        (
            c.level_params.clone(),
            c.type_.clone(),
            c.kind,
            c.value.clone(),
        )
    });

    let taken = discharge_fabricated_stubs_for(&mut env, &candidate(&lib), &lib, TrustGate::Strict);
    assert_eq!(taken.len(), 2);

    let restored = restore_unreplaced_stubs(&mut env, taken);

    assert_eq!(
        restored.iter().map(ToString::to_string).collect::<Vec<_>>(),
        vec!["Fact".to_string()],
        "only the CLOSURE member is reported; the namespace sweep is routine"
    );
    assert!(resident(&env, "Fact"));
    assert!(resident(&env, "Fact.mk"));
    assert_eq!(
        env.get_const(&Name::from_string("Fact")).map(|c| (
            c.level_params.clone(),
            c.type_.clone(),
            c.kind,
            c.value.clone()
        )),
        before,
        "the restored carrier must be identical to the one that was retired"
    );
}
