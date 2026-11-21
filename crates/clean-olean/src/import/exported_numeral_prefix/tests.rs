// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

const DEFS: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/fixtures/olean/v4.36.0/module-ir/StableFixture/Defs.olean"
));

#[test]
fn reads_exact_syntax_kind_precedence_and_handler_from_stable_base() {
    let namespace = Name::anon().str("StableFixture");
    let kind = namespace.clone().str("termStable_witness%_");
    let base = parse_load_module(DEFS.to_vec()).expect("official base");
    let declaration = base
        .constants
        .iter()
        .find(|constant| constant.kernel_name == kind)
        .expect("registered parser declaration");
    assert_eq!(declaration.kind, ConstantKind::Axiom);
    assert_eq!(declaration.value_ptr, 0);

    let prefixes = read_exported_numeral_prefixes(DEFS).expect("official Lean base artifact");
    assert_eq!(
        prefixes,
        [ExportedNumeralPrefix {
            kind,
            priority: 1000,
            precedence: 1022,
            literal: Arc::from("stable_witness% "),
            handler: namespace
                .str("_aux_StableFixture_Defs___elabRules_StableFixture_termStable_witness%__1"),
        }],
    );
}

#[test]
fn rejects_competing_handlers_for_the_same_supported_kind() {
    let mut registrations = read_exported_term_syntax(DEFS).expect("official extension entries");
    let mut competitor = registrations.term_elaborators[0].clone();
    competitor.entry.declaration = Name::anon().str("competingHandler");
    registrations.term_elaborators.push(competitor);
    let base = parse_load_module(DEFS.to_vec()).expect("official base");
    let error = decode_prefixes(&base, &registrations).expect_err("handler must be unique");
    assert!(error.to_string().contains("competing term elaborators"));
}

#[test]
fn checks_both_occurrences_of_the_precedence_numeral() {
    let precedence = |index, instance| {
        Expr::apps(
            Expr::const_str_levels("OfNat.ofNat", vec![Level::zero()]),
            [
                Expr::const_str("Nat"),
                Expr::nat_lit(index),
                Expr::app(Expr::const_str("instOfNatNat"), Expr::nat_lit(instance)),
            ],
        )
    };
    let declaration = Name::anon().str("testParser");
    assert_eq!(
        numeral_precedence(&precedence(1022, 1022), &declaration).unwrap(),
        Some(1022)
    );
    let error = numeral_precedence(&precedence(1022, 1021), &declaration)
        .expect_err("the instance must carry the same numeral");
    assert!(error
        .to_string()
        .contains("inconsistent numeral precedence"));
    assert_eq!(
        numeral_precedence(&Expr::nat_lit(1022), &declaration).unwrap(),
        None,
        "other representation remains unhandled"
    );
}
