// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Parse the unchanged TrustCG proof unit through Trust's strict parser API.
//! This tests syntax admission, not elaboration or theorem validity.

use clean_parser::{
    parse_file_with_tactics_located, LocatedParseError, SurfaceDecl, TacticPatterns,
};

// TrustCG caef982ce, proofs/sentinel_decide_spec.lean, byte-identical SHA-256:
// 611ffa696abcc9580cf49fa6d625c3a364f9ab7a3de066f0c44c5365e8bb28b7.
const SENTINEL: &str = include_str!("fixtures/trust_cg_sentinel_decide_caef982.lean");

// TrustCG 68fca4550d244fd96a6f892fdab2e4667725748e, same production unit:
// SHA-256 1d52fa63b5fc789e36d5eafb778b1baa31b2c301a1e61e0fd5217f6c9770f712.
const CURRENT_SENTINEL: &str = include_str!("fixtures/trust_cg_sentinel_decide_68fca455.lean");

// Exact notation() output of trust-temporal-prelude at Trust add81bfd24.
// The fixture preserves MODULES order and the owner's line-selection algorithm.
const NOTATION: &str = include_str!("fixtures/trust_temporal_notation_add81bfd.lean");

/// Match rustc_parse::parser::item::trust_clean_decls_from_text: empty tactic
/// patterns, then the served-notation fallback, and the original error on failure.
fn parse_like_trust(source: &str) -> Result<Vec<SurfaceDecl>, LocatedParseError> {
    let patterns = TacticPatterns::new();
    match parse_file_with_tactics_located(source, &patterns) {
        Ok(declarations) => Ok(declarations),
        Err(original) => {
            let mut combined = NOTATION.to_owned();
            let base = combined.len();
            combined.push_str(source);
            match parse_file_with_tactics_located(&combined, &patterns) {
                Ok(declarations) => Ok(declarations
                    .into_iter()
                    .filter(|declaration| declaration.span().start >= base)
                    .collect()),
                Err(_) => Err(original),
            }
        }
    }
}

#[test]
fn unchanged_trust_cg_sentinel_is_accepted_without_tactic_patterns_or_recovery() {
    let declarations = parse_like_trust(SENTINEL)
        .unwrap_or_else(|error| panic!("unchanged TrustCG sentinel refused: {error}"));
    let mut names = Vec::new();
    collect_theorems(&declarations, &mut names);
    assert!(
        names.iter().any(|name| name == "multiply_split"),
        "the unit's final theorem must survive parsing: {names:?}"
    );
}

#[test]
fn current_trust_cg_sentinel_retains_complete_source_and_final_xor_theorems() {
    let declarations = parse_like_trust(CURRENT_SENTINEL)
        .unwrap_or_else(|error| panic!("current unchanged TrustCG sentinel refused: {error}"));
    let mut names = Vec::new();
    collect_theorems(&declarations, &mut names);
    for required in [
        "div_lt_product",
        "multiply_split",
        "or_disjoint_limbs",
        "limbs_or_source_value",
        "uint64_xor_value",
        "xor_state_partition",
        "full_step_source_value",
    ] {
        assert!(
            names.iter().any(|name| name == required),
            "current production theorem {required} was lost: {names:?}"
        );
    }
}

#[test]
fn current_trust_cg_sentinel_malformed_suffix_is_not_hidden_by_notation_fallback() {
    let source = format!("{CURRENT_SENTINEL}\ntheorem malformed : True := (\n");
    assert!(parse_like_trust(&source).is_err());
}

fn collect_theorems(declarations: &[SurfaceDecl], names: &mut Vec<String>) {
    for declaration in declarations {
        match declaration {
            SurfaceDecl::Theorem { name, .. } => names.push(name.to_string()),
            SurfaceDecl::Namespace { decls, .. } | SurfaceDecl::Section { decls, .. } => {
                collect_theorems(decls, names);
            }
            SurfaceDecl::RawDecl { .. } => panic!("strict parser returned a recovery declaration"),
            _ => {}
        }
    }
}

#[test]
fn served_notation_fallback_does_not_turn_bad_source_into_an_accepted_unit() {
    let source = format!("{SENTINEL}\ntheorem malformed : True := (\n");
    assert!(parse_like_trust(&source).is_err());
}

#[test]
fn unknown_command_remains_an_explicit_error_declaration() {
    // Unknown command names are retained as RawDecl for the elaborator's
    // diagnostic; they are distinct from syntax-recovery placeholders. Trust
    // carries this declaration kind forward and never treats it as a theorem.
    let source = format!("{SENTINEL}\nthis is an invalid command\n");
    let declarations =
        parse_like_trust(&source).expect("unknown command is represented explicitly");
    assert!(declarations.iter().any(|declaration| matches!(
        declaration,
        SurfaceDecl::RawDecl { content, .. } if content.starts_with("unknown command `this`")
    )));
}

#[test]
fn served_notation_is_available_only_through_the_existing_fallback() {
    let source = "def sum := left ⊞ right\n";
    assert!(parse_file_with_tactics_located(source, &TacticPatterns::new()).is_err());
    let declarations = parse_like_trust(source).expect("served notation should parse on retry");
    assert!(matches!(
        declarations.as_slice(),
        [SurfaceDecl::Def { name, .. }] if name.to_string() == "sum"
    ));
}
