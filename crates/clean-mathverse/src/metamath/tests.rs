// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the Metamath importer.
//!
//! Tests the full pipeline: `.mm` text -> parsed database -> shard writer.

use super::parser::parse_mm;
use super::shard_writer::{write_mm_to_writer, zfc_axiom_profile};
use super::types::{MmProofFormat, MmStatementKind};
use crate::shard::ShardWriter;
use crate::types::AxiomProfile;

/// A small but realistic `.mm` snippet modeled on set.mm's propositional logic.
const MINI_SET_MM: &str = r#"
$( Mini set.mm fragment for testing $)

$c ( ) -> -. wff |- $.
$v ph ps ch $.

$( Floating hypotheses: declare variable types $)
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.

$( Syntax axioms: define well-formed formulas $)
wi $a wff ( ph -> ps ) $.
wn $a wff -. ph $.

$( Logical axioms $)
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.

$( Modus ponens $)
${
    min $e |- ph $.
    maj $e |- ( ph -> ps ) $.
    ax-mp $a |- ps $.
$}

$( A simple theorem $)
a1i $p |- ( ps -> ph ) $= wph wps wi min ax-1 ax-mp $.
"#;

#[test]
fn test_mini_set_mm_parse() {
    let db = parse_mm(MINI_SET_MM).expect("parse mini set.mm");

    // Constants and variables
    assert_eq!(db.constants, vec!["(", ")", "->", "-.", "wff", "|-"]);
    assert_eq!(db.variables, vec!["ph", "ps", "ch"]);

    // Statement counts
    assert_eq!(db.float_hyp_count(), 3); // wph, wps, wch
    assert_eq!(db.essential_hyp_count(), 2); // min, maj
    assert_eq!(db.axiom_count(), 6); // wi, wn, ax-1, ax-2, ax-3, ax-mp
                                     // ax-mp is inside a scope block but it's still an axiom ($a)
    let ax_mp = db.statements.iter().find(|s| s.label == "ax-mp");
    assert!(ax_mp.is_some());
    assert_eq!(ax_mp.unwrap().kind, MmStatementKind::Axiom);

    // Total: 3 float + 2 essential + 6 axioms + 1 theorem = 12
    assert_eq!(db.total_statements(), 12);
    assert_eq!(db.theorem_count(), 1);
}

#[test]
fn test_mini_set_mm_theorem_proof() {
    let db = parse_mm(MINI_SET_MM).expect("parse");
    let thm = db
        .statements
        .iter()
        .find(|s| s.label == "a1i")
        .expect("a1i");

    assert_eq!(thm.kind, MmStatementKind::Theorem);
    assert_eq!(thm.expression.typecode(), Some("|-"));

    let proof = thm.proof.as_ref().expect("proof");
    assert_eq!(proof.format, MmProofFormat::Normal);
    assert_eq!(
        proof.steps,
        vec!["wph", "wps", "wi", "min", "ax-1", "ax-mp"]
    );
}

#[test]
fn test_mini_set_mm_scope_hypotheses() {
    let db = parse_mm(MINI_SET_MM).expect("parse");

    // ax-mp is inside a scope with min and maj as essential hypotheses.
    // It should have wph, wps, wch (from outer scope) plus min, maj (from inner scope).
    let ax_mp = db
        .statements
        .iter()
        .find(|s| s.label == "ax-mp")
        .expect("ax-mp");
    assert!(ax_mp.hypotheses.contains(&"wph".to_string()));
    assert!(ax_mp.hypotheses.contains(&"wps".to_string()));
    assert!(ax_mp.hypotheses.contains(&"min".to_string()));
    assert!(ax_mp.hypotheses.contains(&"maj".to_string()));

    // a1i is outside the scope block, so it should NOT have min/maj.
    let a1i = db
        .statements
        .iter()
        .find(|s| s.label == "a1i")
        .expect("a1i");
    assert!(a1i.hypotheses.contains(&"wph".to_string()));
    assert!(!a1i.hypotheses.contains(&"min".to_string()));
    assert!(!a1i.hypotheses.contains(&"maj".to_string()));
}

#[test]
fn test_mini_set_mm_shard_roundtrip() {
    let db = parse_mm(MINI_SET_MM).expect("parse");
    let mut writer = ShardWriter::new();
    let stats = write_mm_to_writer(&db, &std::collections::HashSet::new(), &mut writer);

    // All statements should be written
    assert_eq!(stats.entries_written, db.total_statements());
    assert!(stats.axiom_count > 0);
    assert_eq!(stats.theorem_count, 1);
    assert_eq!(stats.float_hyp_count, 3);
    assert_eq!(stats.essential_hyp_count, 2);
}

#[test]
fn test_zfc_profile_is_classical() {
    let profile = zfc_axiom_profile();
    assert!(profile.has(AxiomProfile::CHOICE));
    assert!(profile.has(AxiomProfile::LEM));
    // ZFC should not have HOL or Mizar bits
    assert!(!profile.has(AxiomProfile::HOL_AXIOMS));
    assert!(!profile.has(AxiomProfile::MIZAR_TG));
    assert!(!profile.has(AxiomProfile::FLOAT_APPROX));
}

#[test]
fn test_compressed_proof_fragment() {
    let input = "$c wff |- ( ) -> $.
$v ph ps $.
wph $f wff ph $.
wps $f wff ps $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
thm1 $p |- ( ph -> ( ps -> ph ) ) $= ( ax-1 ) AA $.";

    let db = parse_mm(input).expect("parse");
    let thm = db
        .statements
        .iter()
        .find(|s| s.label == "thm1")
        .expect("thm1");
    let proof = thm.proof.as_ref().expect("proof");
    assert_eq!(proof.format, MmProofFormat::Compressed);
    // Compressed proof has labels then encoded block
    assert!(proof.steps.contains(&"ax-1".to_string()));
}

#[test]
fn test_multiple_scope_blocks() {
    let input = "$c wff |- $.
$v ph ps $.
wph $f wff ph $.
${ $v x $. wx $f wff x $. $}
${ $v y $. wy $f wff y $. $}
ax-1 $a |- ph $.";

    let db = parse_mm(input).expect("parse");

    // ax-1 should only see wph from outer scope, not wx or wy
    let ax1 = db
        .statements
        .iter()
        .find(|s| s.label == "ax-1")
        .expect("ax-1");
    assert!(ax1.hypotheses.contains(&"wph".to_string()));
    assert!(!ax1.hypotheses.contains(&"wx".to_string()));
    assert!(!ax1.hypotheses.contains(&"wy".to_string()));
}

#[test]
fn test_error_on_malformed_input() {
    // Missing $. terminator
    assert!(parse_mm("$c wff").is_err());

    // Unmatched scope close
    assert!(parse_mm("$}").is_err());

    // Unknown keyword after label
    assert!(parse_mm("foo $x bar $.").is_err());
}
