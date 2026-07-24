// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::{
    coq_import::{BatchImportSource, CoqBatchImporter, CoqName, ImportStats},
    Name,
};

#[test]
fn coq_batch_importer_registers_requested_stdlib_type_mappings() {
    let mut importer = CoqBatchImporter::new();
    assert!(importer
        .context()
        .lookup_global(&CoqName::from_dotted("option"))
        .is_none());

    importer.import_stdlib_types();

    for (coq_name, lean_name) in [
        ("nat", "Nat"),
        ("bool", "Bool"),
        ("list", "List"),
        ("option", "Option"),
        ("prod", "Prod"),
        ("sum", "Sum"),
        ("unit", "Unit"),
        ("sig", "Subtype"),
        ("eq", "Eq"),
        ("Z", "Int"),
        ("positive", "Nat"),
        ("le", "Nat.le"),
        ("lt", "Nat.lt"),
        ("plus", "Nat.add"),
        ("mult", "Nat.mul"),
    ] {
        let expected = Name::from_string(lean_name);
        let coq_name = CoqName::from_dotted(coq_name);
        assert!(
            matches!(importer.context().lookup_global(&coq_name), Some(name) if *name == expected)
        );
    }

    for (coq_name, lean_name) in [
        ("nat", "Nat"),
        ("bool", "Bool"),
        ("list", "List"),
        ("option", "Option"),
        ("prod", "Prod"),
        ("sum", "Sum"),
        ("unit", "Unit"),
        ("sig", "Subtype"),
        ("eq", "Eq"),
        ("Z", "Int"),
        ("positive", "Nat"),
    ] {
        let expected = Name::from_string(lean_name);
        let coq_name = CoqName::from_dotted(coq_name);
        assert!(matches!(
            importer.context().lookup_inductive(&coq_name),
            Some(mapping) if mapping.inductive == expected
        ));
    }
}

#[test]
fn coq_batch_importer_registers_requested_stdlib_propositions() {
    let mut importer = CoqBatchImporter::new();
    assert!(importer
        .context()
        .lookup_global(&CoqName::from_dotted("and"))
        .is_none());

    importer.import_stdlib_propositions();

    for (coq_name, lean_name) in [
        ("True", "True"),
        ("False", "False"),
        ("and", "And"),
        ("or", "Or"),
        ("not", "Not"),
        ("iff", "Iff"),
        ("ex", "Exists"),
        ("I", "True.intro"),
        ("conj", "And.intro"),
        ("or_introl", "Or.inl"),
        ("or_intror", "Or.inr"),
        ("ex_intro", "Exists.intro"),
    ] {
        let expected = Name::from_string(lean_name);
        let coq_name = CoqName::from_dotted(coq_name);
        assert!(
            matches!(importer.context().lookup_global(&coq_name), Some(name) if *name == expected)
        );
    }

    for (coq_name, lean_name) in [
        ("True", "True"),
        ("False", "False"),
        ("and", "And"),
        ("or", "Or"),
        ("ex", "Exists"),
    ] {
        let expected = Name::from_string(lean_name);
        let coq_name = CoqName::from_dotted(coq_name);
        assert!(matches!(
            importer.context().lookup_inductive(&coq_name),
            Some(mapping) if mapping.inductive == expected
        ));
    }
}

#[test]
fn coq_batch_importer_tracks_success_failure_and_skipped_sources() {
    let mut importer = CoqBatchImporter::new();
    importer.import_stdlib_types();

    let stats = importer.import_sources(vec![
        BatchImportSource::new(
            "good.v",
            r#"(axiom (name "Coq.Tests.good") (type (sort prop)))"#,
        ),
        BatchImportSource::new("bad.v", "not-a-declaration"),
        BatchImportSource::new(
            "notes.txt",
            r#"(axiom (name "Coq.Tests.skipped") (type (sort prop)))"#,
        ),
    ]);

    assert_eq!(
        stats,
        ImportStats {
            successes: 1,
            failures: 1,
            skipped: 1,
        }
    );
    assert_eq!(importer.stats(), stats);
}
