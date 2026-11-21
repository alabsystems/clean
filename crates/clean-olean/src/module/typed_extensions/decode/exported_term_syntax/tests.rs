// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

const DEFS: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/fixtures/olean/v4.36.0/module-ir/StableFixture/Defs.olean"
));

#[test]
fn exported_term_syntax_follows_persisted_registration_order() {
    let syntax = read_exported_term_syntax(DEFS).expect("genuine stable base artifact");
    let namespace = Name::anon().str("StableFixture");
    let kind = namespace.clone().str("termStable_witness%_");
    assert_eq!(syntax.parser.len(), 12);
    assert!(syntax.parser.iter().all(|row| row.scope.is_none()));
    let tokens: Vec<_> = syntax
        .parser
        .iter()
        .filter_map(|row| match &row.entry {
            ParserRegistration::Token(token) => Some(token.as_ref()),
            _ => None,
        })
        .collect();
    assert_eq!(tokens, ["stable_witness%", "$", "$", "_", "(", ")", ":"]);
    assert_eq!(
        syntax.parser[7].entry,
        ParserRegistration::Kind(kind.clone())
    );
    assert_eq!(
        syntax.parser[11].entry,
        ParserRegistration::Parser {
            category: Name::anon().str("term"),
            declaration: kind.clone(),
            priority: 1000,
        }
    );
    assert_eq!(
        syntax.term_elaborators,
        [ScopedSyntaxEntry {
            scope: None,
            entry: TermElaboratorRegistration {
                kind,
                declaration: namespace.str(
                    "_aux_StableFixture_Defs___elabRules_StableFixture_termStable_witness%__1"
                ),
            },
        }]
    );
}

#[test]
fn exported_term_syntax_refuses_wrong_world_and_inconsistent_version() {
    let mut foreign = DEFS.to_vec();
    foreign[40] = if foreign[40] == b'0' { b'1' } else { b'0' };
    let mut mislabeled = DEFS.to_vec();
    mislabeled[7] = b'5';
    for bytes in [foreign, mislabeled] {
        let error = read_exported_term_syntax(&bytes).expect_err("unadmitted artifact");
        assert!(error.to_string().contains("registered Lean 4.36.0"));
    }
}

#[test]
fn exported_term_syntax_refuses_an_unterminated_token() {
    let mut bytes = DEFS.to_vec();
    let token = b"stable_witness%\0";
    let start = bytes
        .windows(token.len())
        .position(|candidate| candidate == token)
        .expect("genuine token storage");
    // The preceding String length includes one mandatory NUL byte. Keeping
    // the same object extent while removing the terminator must be refused.
    bytes[start + token.len() - 1] = b'!';
    let error = read_exported_term_syntax(&bytes).expect_err("malformed parser token");
    assert!(error.to_string().contains("has no terminator"));
}
