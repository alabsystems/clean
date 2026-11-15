// Copyright 2026 Andrew Yates | License: Apache-2.0
use trust_ir_contract::{Formula, Sort, escape_smtlib_symbol};

#[test]
fn leading_digits_are_quoted_independently_of_integer_parsing() {
    for name in [
        "1x",
        "0abc",
        "1.5",
        "12345678901234567890123456789012345678901234567890",
    ] {
        assert_eq!(escape_smtlib_symbol(name), format!("|{name}|"));
    }
}

#[test]
fn reserved_tokens_are_identifiers_only_when_quoted() {
    for name in [
        "_",
        "!",
        "as",
        "let",
        "exists",
        "forall",
        "match",
        "par",
        "BINARY",
        "DECIMAL",
        "HEXADECIMAL",
        "NUMERAL",
        "STRING",
        "assert",
        "check-sat",
        "declare-datatype",
        "define-funs-rec",
        "reset-assertions",
        "get-value",
        "set-logic",
    ] {
        assert_eq!(escape_smtlib_symbol(name), format!("|{name}|"));
        assert_eq!(
            Formula::Var(name.into(), Sort::Int).to_smtlib(),
            format!("|{name}|")
        );
        assert_eq!(
            Sort::Datatype {
                name: name.into(),
                constructors: vec![]
            }
            .to_smtlib(),
            format!("|{name}|")
        );
    }
}

#[test]
fn ordinary_names_and_predefined_nonreserved_symbols_keep_their_spelling() {
    for name in [
        "x123", "a-b", "forallX", "Let", "true", "false", "Bool", "Int", "dag!0_1",
    ] {
        assert_eq!(escape_smtlib_symbol(name), name);
    }
}
