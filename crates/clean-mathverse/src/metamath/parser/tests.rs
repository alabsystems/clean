// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the Metamath `.mm` parser.

use super::*;

#[test]
fn test_tokenize_strips_comments() {
    let input = "$c wff $. $( This is a comment $) $c class $.";
    let tokens = tokenize(input).expect("tokenize");
    assert_eq!(tokens, vec!["$c", "wff", "$.", "$c", "class", "$."]);
}

#[test]
fn test_tokenize_nested_comments() {
    let input = "$( outer $( inner $) still outer $) $c wff $.";
    let tokens = tokenize(input).expect("tokenize");
    assert_eq!(tokens, vec!["$c", "wff", "$."]);
}

#[test]
fn test_tokenize_unclosed_comment_error() {
    let input = "$( no closing";
    let result = tokenize(input);
    assert!(result.is_err());
}

#[test]
fn test_parse_constant_declaration() {
    let input = "$c ( ) -> wff $.";
    let db = parse_mm(input).expect("parse");
    assert_eq!(db.constants, vec!["(", ")", "->", "wff"]);
}

#[test]
fn test_parse_variable_declaration() {
    let input = "$v ph ps $.";
    let db = parse_mm(input).expect("parse");
    assert_eq!(db.variables, vec!["ph", "ps"]);
}

#[test]
fn test_parse_floating_hypothesis() {
    let input = "$c wff $. $v ph $. wph $f wff ph $.";
    let db = parse_mm(input).expect("parse");
    assert_eq!(db.statements.len(), 1);
    let stmt = &db.statements[0];
    assert_eq!(stmt.label, "wph");
    assert_eq!(stmt.kind, MmStatementKind::FloatingHyp);
    assert_eq!(stmt.expression.typecode(), Some("wff"));
    assert_eq!(stmt.expression.body(), &["ph".to_string()]);
}

#[test]
fn test_parse_essential_hypothesis() {
    let input = "$c wff |- $. $v ph $. wph $f wff ph $. maj $e |- ph $.";
    let db = parse_mm(input).expect("parse");
    assert_eq!(db.statements.len(), 2);
    let stmt = &db.statements[1];
    assert_eq!(stmt.label, "maj");
    assert_eq!(stmt.kind, MmStatementKind::EssentialHyp);
    assert_eq!(stmt.expression.tokens, vec!["|-", "ph"]);
    assert!(stmt.hypotheses.contains(&"wph".to_string()));
}

#[test]
fn test_parse_axiom() {
    let input = "$c wff |- ( ) -> $.
$v ph ps $.
wph $f wff ph $.
wps $f wff ps $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.";
    let db = parse_mm(input).expect("parse");
    assert_eq!(db.axiom_count(), 1);
    let ax = db
        .statements
        .iter()
        .find(|s| s.label == "ax-1")
        .expect("ax-1");
    assert_eq!(ax.kind, MmStatementKind::Axiom);
    assert_eq!(ax.expression.typecode(), Some("|-"));
    assert!(ax.hypotheses.contains(&"wph".to_string()));
    assert!(ax.hypotheses.contains(&"wps".to_string()));
}

#[test]
fn test_parse_theorem_with_normal_proof() {
    let input = "$c wff |- ( ) -> $.
$v ph ps $.
wph $f wff ph $.
wps $f wff ps $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
mp $e |- ph $.
a1i $p |- ( ps -> ph ) $= wph wps ax-1 mp $.";
    let db = parse_mm(input).expect("parse");
    assert_eq!(db.theorem_count(), 1);
    let thm = db
        .statements
        .iter()
        .find(|s| s.label == "a1i")
        .expect("a1i");
    assert_eq!(thm.kind, MmStatementKind::Theorem);
    let proof = thm.proof.as_ref().expect("proof");
    assert_eq!(proof.format, MmProofFormat::Normal);
    assert_eq!(proof.steps, vec!["wph", "wps", "ax-1", "mp"]);
}

#[test]
fn test_parse_theorem_with_compressed_proof() {
    let input = "$c wff |- ( ) -> $.
$v ph ps $.
wph $f wff ph $.
wps $f wff ps $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
mp $e |- ph $.
a1i $p |- ( ps -> ph ) $= ( ax-1 ) AB $.";
    let db = parse_mm(input).expect("parse");
    let thm = db
        .statements
        .iter()
        .find(|s| s.label == "a1i")
        .expect("a1i");
    let proof = thm.proof.as_ref().expect("proof");
    assert_eq!(proof.format, MmProofFormat::Compressed);
    assert!(proof.steps.contains(&"ax-1".to_string()));
    assert!(proof.steps.last().map(|s| s.as_str()) == Some("AB"));
}

#[test]
fn test_parse_scope_block() {
    let input = "$c wff $. $v ph $. wph $f wff ph $.
${ $v ps $. wps $f wff ps $. $}
$( ps and wps are now out of scope $)";
    let db = parse_mm(input).expect("parse");
    assert_eq!(db.statements.len(), 2);
    let wps = db
        .statements
        .iter()
        .find(|s| s.label == "wps")
        .expect("wps");
    assert!(wps.hypotheses.contains(&"wph".to_string()));
}

#[test]
fn test_parse_empty_input() {
    let db = parse_mm("").expect("parse empty");
    assert!(db.is_empty());
}

#[test]
fn test_parse_comment_only() {
    let db = parse_mm("$( just a comment $)").expect("parse comment");
    assert!(db.is_empty());
}

#[test]
fn test_parse_unterminated_constant_error() {
    let result = parse_mm("$c wff class");
    assert!(result.is_err());
}

#[test]
fn test_parse_unmatched_scope_close_error() {
    let result = parse_mm("$}");
    assert!(result.is_err());
}

#[test]
fn test_parse_theorem_missing_proof_error() {
    let input = "$c wff |- $.
$v ph $.
wph $f wff ph $.
thm $p |- ph $.";
    let result = parse_mm(input);
    assert!(result.is_err());
}
