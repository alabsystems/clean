// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What the writer refuses, each with the control that is written, and the
//! names the export reader stores escaped (R118).

use super::*;

#[test]
fn test_writer_refuses_a_constant_no_earlier_record_declares() {
    let prop = Expr::sort(Level::zero());
    let uses_later = definition(
        "A",
        prop.clone(),
        Expr::const_(Name::from_string("B"), vec![]),
    );
    let later = definition("B", Expr::sort(Level::succ(Level::zero())), prop);
    let refusal = write_declarations(
        &meta(),
        [uses_later.clone(), later.clone()].map(Ok),
        Spelling::new(),
        std::io::sink(),
    );
    assert!(
        matches!(
            &refusal,
            Err(ExportWriteError::UndeclaredReference { declaration, constant })
                if declaration == "A" && constant == "B"
        ),
        "{refusal:?}"
    );
    // The control: the same two records in dependency order are written.
    write_declarations(
        &meta(),
        [later, uses_later].map(Ok),
        Spelling::new(),
        std::io::sink(),
    )
    .expect("dependency order");
}

#[test]
fn test_writer_refuses_what_lean_has_no_record_for() {
    let prop = Expr::sort(Level::zero());
    let linear = Expr::from_kind(ExprKind::Lam(
        BinderData::new(BinderInfo::Default, Multiplicity::One),
        std::sync::Arc::new(prop.clone()),
        std::sync::Arc::new(Expr::bvar(0)),
    ));
    for (bad, expected) in [
        (linear, "multiplicity"),
        (Expr::from_kind(ExprKind::SProp), "outside Lean's"),
    ] {
        let refusal = write_declarations(
            &meta(),
            [Ok(definition("A", prop.clone(), bad))],
            Spelling::new(),
            std::io::sink(),
        );
        assert!(
            matches!(&refusal, Err(ExportWriteError::Unexportable { what, .. }) if what.contains(expected)),
            "{refusal:?}"
        );
    }
    let twice = definition("A", prop.clone(), prop.clone());
    let refusal = write_declarations(
        &meta(),
        [twice.clone(), twice].map(Ok),
        Spelling::new(),
        std::io::sink(),
    );
    assert!(
        matches!(&refusal, Err(ExportWriteError::DuplicateDeclaration { name }) if name == "A"),
        "{refusal:?}"
    );
}

/// The string components of an export's name records.
fn name_components(bytes: &[u8]) -> BTreeSet<String> {
    let mut components = BTreeSet::new();
    for line in bytes.split(|b| *b == b'\n').filter(|l| !l.is_empty()) {
        let value: serde_json::Value = serde_json::from_slice(line).expect("a JSON line");
        if let Some(component) = value.get("str").and_then(|s| s.get("str")) {
            components.insert(component.as_str().expect("a string").to_owned());
        }
    }
    components
}

#[test]
fn test_writer_names_the_reader_escaped_are_written_as_lean_wrote_them() {
    let minted = fixture("init_dotted_names.ndjson.gz");
    let from_lean = name_components(&minted);
    let dotted: Vec<&String> = from_lean.iter().filter(|c| c.contains('.')).collect();
    assert!(!dotted.is_empty(), "the fixture has dotted components");
    let loaded = load_export(NdjsonSource::new(minted.as_slice()).expect("a header"))
        .expect("the fixture loads");
    let targets: BTreeSet<Name> = loaded.declared.iter().map(|d| d.name.clone()).collect();

    // With the reader's record, the names are Lean's.
    let mut written = Vec::new();
    write_cone(
        &loaded.env,
        &targets,
        &meta(),
        loaded.written_names.clone(),
        &mut written,
    )
    .expect("the cone is written");
    // Every component written is one Lean wrote (Lean's export also names
    // binders, which Clean's terms do not carry), the dotted ones included.
    let from_clean = name_components(&written);
    let invented: Vec<&String> = from_clean.difference(&from_lean).collect();
    assert!(
        invented.is_empty(),
        "components Lean did not write: {invented:?}"
    );
    for component in &dotted {
        assert!(from_clean.contains(*component), "missing {component}");
    }

    // Without it the stored form would be written as if it were Lean's name:
    // refused.
    let refusal = write_export(&loaded.env, &targets, &meta(), std::io::sink());
    assert!(
        matches!(&refusal, Err(ExportWriteError::Unexportable { what, .. }) if what.contains("U+2024")),
        "{refusal:?}"
    );
}

#[test]
fn test_writer_cone_refuses_unsafe_and_absent_constants() {
    let minted = fixture("nat_add_literal.ndjson");
    let mut loaded =
        load_export(NdjsonSource::new(minted.as_slice()).expect("a header")).expect("loads");
    let targets: BTreeSet<Name> = loaded.declared.iter().map(|d| d.name.clone()).collect();
    let absent: BTreeSet<Name> = [Name::from_string("No.Such.Constant")].into();
    let refusal = write_export(&loaded.env, &absent, &meta(), std::io::sink());
    assert!(
        matches!(&refusal, Err(ExportWriteError::AbsentConstant { name }) if name == "No.Such.Constant"),
        "{refusal:?}"
    );
    let victim = Name::from_string("Nat.add");
    assert!(targets.contains(&victim));
    loaded.env.mark_unsafe(victim);
    let refusal = write_export(&loaded.env, &targets, &meta(), std::io::sink());
    assert!(
        matches!(
            &refusal,
            Err(ExportWriteError::OutsideSafeFragment { name, marker: "unsafe" }) if name == "Nat.add"
        ),
        "{refusal:?}"
    );
}

#[test]
fn test_round_trip_refuses_bytes_that_are_not_what_was_written() {
    let (written, summary) = write(&read(&fixture("nested_reflexive.ndjson")), Spelling::new());
    check_export_round_trip(written.as_slice(), &summary).expect("the control");

    // One binder's information changed: still a well-formed export.
    let text = String::from_utf8(written.clone()).expect("UTF-8");
    let tampered = text.replacen(
        "\"binderInfo\":\"default\"",
        "\"binderInfo\":\"implicit\"",
        1,
    );
    assert_ne!(text, tampered);
    let refusal = check_export_round_trip(tampered.as_bytes(), &summary);
    assert!(
        matches!(&refusal, Err(ExportWriteError::RoundTrip { .. })),
        "{refusal:?}"
    );

    // The last record cut off at a line boundary.
    let cut = &written[..written[..written.len() - 1]
        .iter()
        .rposition(|b| *b == b'\n')
        .expect("more than one line")
        + 1];
    let refusal = check_export_round_trip(cut, &summary);
    assert!(
        matches!(&refusal, Err(ExportWriteError::RoundTrip { .. })),
        "{refusal:?}"
    );

    // Not an export at all.
    let refusal = check_export_round_trip(&b"{\"in\":1}\n"[..], &summary);
    assert!(
        matches!(&refusal, Err(ExportWriteError::ReadBack { .. })),
        "{refusal:?}"
    );
}
