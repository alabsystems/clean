// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

const DEFS: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/fixtures/olean/v4.36.0/module-ir/StableFixture/Defs.olean"
));

#[test]
fn exported_parser_executes_its_actual_descriptor_ir() {
    let name = Name::anon()
        .str("StableFixture")
        .str("termStable_witness%_");
    let run = |bytes: &[u8]| {
        let header = OleanHeader::parse(bytes).unwrap();
        let region = CompactedRegion::new(bytes, header.base_addr);
        evaluate_exported_numeral_parser_in_region(&region, region.root_ptr().unwrap(), &name)
    };
    assert_eq!(
        run(DEFS).unwrap(),
        Some((name.clone(), 1022, Arc::from("stable_witness% ")))
    );

    // Keep the node declaration and its operands, changing only the stored
    // constructor index. A recognized descriptor with bad layout is an error.
    let mut malformed = DEFS.to_vec();
    let index = &mut malformed[0x43f8..0x4400];
    assert_eq!(&*index, 7_u64.to_le_bytes().as_slice());
    index.copy_from_slice(&5_u64.to_le_bytes());
    let error = run(&malformed).unwrap_err().to_string();
    assert!(
        error.contains("invalid Lean.ParserDescr.node layout"),
        "{error}"
    );
}

fn expected_literal(literal: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [
            Expr::const_str("Nat"),
            literal.clone(),
            Expr::app(Expr::const_str("instOfNatNat"), literal),
        ],
    )
}

#[test]
fn exported_handler_runs_genuine_stable_lean_ir() {
    let registrations = read_exported_term_syntax(DEFS).expect("genuine term registrations");
    let [entry] = registrations.term_elaborators.as_slice() else {
        panic!("the fixture has one exported term elaborator");
    };
    let handler = &entry.entry.declaration;
    let run = |bytes, numeral| {
        evaluate_exported_term_elaborator(
            bytes,
            handler,
            ExportedNumeralSyntax {
                kind: &entry.entry.kind,
                token: "stable_witness%",
                numeral,
            },
        )
    };
    assert_eq!(
        run(DEFS, "17").unwrap(),
        expected_literal(Expr::nat_lit(73))
    );
    assert_eq!(
        run(DEFS, "0x12").unwrap(),
        expected_literal(Expr::nat_lit(74))
    );
    assert_eq!(
        run(DEFS, "18_446_744_073_709_551_616").unwrap(),
        expected_literal(Expr::nat_lit_u128((1_u128 << 64) + 56))
    );

    // The genuine IR operand of Nat.add at this fixture offset is the
    // boxed numeral 56. Change only that operand and require a new result.
    let mut altered = DEFS.to_vec();
    let literal = &mut altered[0x3060..0x3068];
    assert_eq!(&*literal, 113_u64.to_le_bytes().as_slice());
    literal.copy_from_slice(&115_u64.to_le_bytes());
    assert_eq!(
        run(&altered, "17").unwrap(),
        expected_literal(Expr::nat_lit(74))
    );
}

#[test]
fn exported_handler_requires_its_exact_kind_and_name() {
    let registrations = read_exported_term_syntax(DEFS).expect("genuine term registrations");
    let entry = &registrations.term_elaborators[0].entry;
    let alien = Name::anon().str("StableFixture.termStable_witness%_");
    assert_ne!(alien, entry.kind);
    let syntax = ExportedNumeralSyntax {
        kind: &alien,
        token: "stable_witness%",
        numeral: "17",
    };
    let detail = evaluate_exported_term_elaborator(DEFS, &entry.declaration, syntax)
        .unwrap_err()
        .to_string();
    assert!(
        detail.contains("global handler for the exact syntax kind"),
        "{detail}"
    );
    let syntax = ExportedNumeralSyntax {
        kind: &entry.kind,
        ..syntax
    };
    assert!(evaluate_exported_term_elaborator(DEFS, &entry.kind, syntax).is_err());
}

#[test]
fn pure_host_calls_refuse_state_and_unknown_callees() {
    let read_state = Name::from_string("Lean.Elab.Term.getExpectedType");
    let refusal = host_call(&read_state, &[Value::Unavailable])
        .err()
        .expect("state error")
        .to_string();
    assert!(
        refusal.contains("Lean.Elab.Term.getExpectedType"),
        "{refusal}"
    );
    assert!(
        refusal.contains("unavailable elaborator state"),
        "{refusal}"
    );
    let unimplemented = Name::from_string("Lean.Meta.inferType");
    let refusal = host_call(&unimplemented, &[])
        .err()
        .expect("unknown call error")
        .to_string();
    assert!(refusal.contains("Lean.Meta.inferType"), "{refusal}");
    assert!(refusal.contains("unsupported host call"), "{refusal}");
}
