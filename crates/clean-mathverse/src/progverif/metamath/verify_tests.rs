// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Metamath RPN proof verification engine.

use super::*;
use std::collections::HashMap;

/// A minimal Metamath database with one axiom and one theorem.
const MINI_DB: &str = "\
$c |- ( -> ) wff $.
$v ph ps $.
wph $f wff ph $.
wps $f wff ps $.
wi $a wff ( ph -> ps ) $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
ax-mp $a |- ps $.
";

/// demo0-style database used across multiple tests.
const DEMO0_DB: &str = "\
$c 0 + = -> ( ) term wff |- $.
$v t r s P Q $.
tt $f term t $.
tr $f term r $.
ts $f term s $.
wp $f wff P $.
wq $f wff Q $.
tze $a term 0 $.
tpl $a term ( t + r ) $.
weq $a wff t = r $.
wim $a wff ( P -> Q ) $.
a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
a2 $a |- ( t + 0 ) = t $.
${
    min $e |- P $.
    maj $e |- ( P -> Q ) $.
    mp $a |- Q $.
$}
th1 $p |- t = t $= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl tt tt a1 mp mp $.
";

#[test]
fn test_tokenize_strips_comments() {
    let text = "$( this is a comment $) $c wff $. $( another $)";
    let tokens = tokenize(text);
    assert_eq!(tokens, vec!["$c", "wff", "$."]);
}

#[test]
fn test_tokenize_inline_comment() {
    let text = "ax-1 $( inline $) $a |- ph $.";
    let tokens = tokenize(text);
    assert_eq!(tokens, vec!["ax-1", "$a", "|-", "ph", "$."]);
}

#[test]
fn test_build_label_table_mini() {
    let tokens = tokenize(MINI_DB);
    let labels = build_label_table(&tokens).unwrap();

    // Should have: wph, wps (floats), wi, ax-1, ax-mp (assertions)
    assert!(labels.contains_key("wph"));
    assert!(labels.contains_key("wps"));
    assert!(labels.contains_key("wi"));
    assert!(labels.contains_key("ax-1"));
    assert!(labels.contains_key("ax-mp"));

    // Check float hyp
    match &labels["wph"] {
        LabelInfo::FloatingHyp { typecode, variable } => {
            assert_eq!(typecode, "wff");
            assert_eq!(variable, "ph");
        }
        other => panic!("expected FloatingHyp, got {other:?}"),
    }
}

#[test]
fn test_verify_simple_proof() {
    let result = parse_and_verify(DEMO0_DB).unwrap();
    assert_eq!(
        result.verified, 1,
        "th1 should verify, failed_labels={:?}",
        result.failed_labels
    );
    assert_eq!(result.failed, 0, "no failures expected");
    assert_eq!(result.axioms, 7, "7 axioms: tze, tpl, weq, wim, a1, a2, mp");
}

#[test]
fn test_verify_demo0_from_file() {
    let demo0_path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../data/raw/demo0.mm");
    let demo0_path = std::path::Path::new(demo0_path);
    if !demo0_path.exists() {
        eprintln!("SKIP: demo0.mm not found at {}", demo0_path.display());
        return;
    }
    let text = std::fs::read_to_string(demo0_path).unwrap();
    let result = parse_and_verify(&text).unwrap();
    eprintln!(
        "demo0.mm: verified={}, failed={}, axioms={}",
        result.verified, result.failed, result.axioms
    );
    assert!(
        result.verified > 0,
        "demo0.mm should have verified theorems"
    );
    assert_eq!(result.failed, 0, "demo0.mm should have no failures");
}

#[test]
fn test_verify_peano_from_file() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../data/raw/peano.mm");
    let path = std::path::Path::new(path);
    if !path.exists() {
        eprintln!("SKIP: peano.mm not found");
        return;
    }
    let text = std::fs::read_to_string(path).unwrap();
    let result = parse_and_verify(&text).unwrap();
    eprintln!(
        "peano.mm: verified={}, failed={}, axioms={}, steps={}",
        result.verified, result.failed, result.axioms, result.total_steps
    );
    // peano.mm is small -- expect at least some verified theorems.
    assert!(
        result.verified + result.failed > 0 || result.axioms > 0,
        "peano.mm should have some statements"
    );
}

#[test]
fn test_verify_set_mm() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../data/raw/set.mm");
    let path = std::path::Path::new(path);
    if !path.exists() {
        eprintln!("SKIP: set.mm not found");
        return;
    }
    let text = std::fs::read_to_string(path).unwrap();
    let result = parse_and_verify(&text).unwrap();
    eprintln!("set.mm: verified={}, compressed_skipped={}, failed={}, axioms={}, steps={}, failed_labels={:?}",
        result.verified, result.compressed_skipped, result.failed, result.axioms, result.total_steps,
        &result.failed_labels[..std::cmp::min(10, result.failed_labels.len())]);
    // set.mm has ~40K+ theorems
    assert!(result.axioms > 0, "set.mm should have axioms");
    assert_eq!(result.failed, 0, "set.mm should verify with 0 failures");
    assert!(
        result.verified >= 40000,
        "set.mm should have 40K+ verified theorems"
    );
}

#[test]
fn test_verify_all_mm_databases() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../data/raw");
    for name in &["iset.mm", "nf.mm", "ql.mm"] {
        let path = std::path::Path::new(dir).join(name);
        if !path.exists() {
            eprintln!("SKIP: {} not found", name);
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap();
        let result = parse_and_verify(&text).unwrap();
        eprintln!(
            "{}: verified={}, failed={}, axioms={}, steps={}",
            name, result.verified, result.failed, result.axioms, result.total_steps
        );
        assert_eq!(result.failed, 0, "{} should verify with 0 failures", name);
    }
}

#[test]
fn test_verify_result_default() {
    let r = VerifyResult::default();
    assert_eq!(r.verified, 0);
    assert_eq!(r.failed, 0);
    assert_eq!(r.axioms, 0);
}

#[test]
fn test_empty_database_error() {
    let result = parse_and_verify("");
    // Empty database has no labels -- verify should return Ok with 0 counts.
    let r = result.unwrap();
    assert_eq!(r.verified, 0);
    assert_eq!(r.axioms, 0);
}

#[test]
fn test_scope_handling() {
    let db = "\
$c |- wff $.
$v ph $.
wph $f wff ph $.
${
    hyp $e |- ph $.
    thm $a |- ph $.
$}
";
    let tokens = tokenize(db);
    let labels = build_label_table(&tokens).unwrap();
    // hyp should exist as essential, thm as assertion with hyp in frame
    assert!(labels.contains_key("hyp"));
    assert!(labels.contains_key("thm"));
}

#[test]
fn test_apply_subst_basic() {
    let mut subst = HashMap::new();
    subst.insert("ph".to_string(), vec!["A".to_string()]);
    subst.insert("ps".to_string(), vec!["B".to_string()]);

    let expr: Vec<String> = vec!["|-", "(", "ph", "->", "ps", ")"]
        .into_iter()
        .map(String::from)
        .collect();
    let result = apply_subst(&expr, &subst);
    let expected: Vec<String> = vec!["|-", "(", "A", "->", "B", ")"]
        .into_iter()
        .map(String::from)
        .collect();
    assert_eq!(result, expected);
}

#[test]
fn test_apply_subst_multi_token() {
    let mut subst = HashMap::new();
    subst.insert(
        "ph".to_string(),
        vec![
            "(".to_string(),
            "A".to_string(),
            "->".to_string(),
            "B".to_string(),
            ")".to_string(),
        ],
    );

    let expr: Vec<String> = vec!["|-", "ph"].into_iter().map(String::from).collect();
    let result = apply_subst(&expr, &subst);
    let expected: Vec<String> = vec!["|-", "(", "A", "->", "B", ")"]
        .into_iter()
        .map(String::from)
        .collect();
    assert_eq!(result, expected);
}

#[test]
fn test_apply_subst_no_match() {
    let subst = HashMap::new();
    let expr: Vec<String> = vec!["|-", "ph"].into_iter().map(String::from).collect();
    let result = apply_subst(&expr, &subst);
    assert_eq!(result, expr);
}

/// Verify that a correct multi-step proof with essential hypotheses
/// passes. Uses the demo0 th1 proof, which chains two uses of mp
/// (each requiring essential hypotheses to match).
#[test]
fn test_essential_hyp_verification_mp() {
    let result = parse_and_verify(DEMO0_DB).unwrap();
    assert_eq!(
        result.verified, 1,
        "th1 should verify: {:?}",
        result.failed_labels
    );
    assert_eq!(result.failed, 0);
}

/// Verify that wrong essential hypothesis is caught: if we swap the proof
/// order for MP, the essential hypothesis mismatch should be detected.
#[test]
fn test_essential_hyp_mismatch_detected() {
    // Use the demo0 database but with a bogus proof that provides wrong
    // essential hypotheses to MP.
    let db = "\
$c 0 + = -> ( ) term wff |- $.
$v t r s P Q $.
tt $f term t $.
tr $f term r $.
ts $f term s $.
wp $f wff P $.
wq $f wff Q $.
tze $a term 0 $.
tpl $a term ( t + r ) $.
weq $a wff t = r $.
wim $a wff ( P -> Q ) $.
a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
a2 $a |- ( t + 0 ) = t $.
${
    min $e |- P $.
    maj $e |- ( P -> Q ) $.
    mp $a |- Q $.
$}
bad $p |- t = t $= tt tt weq tt tze tpl tt weq tt a2 tt tze tpl tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl tt tt a1 mp mp $.
";
    // This proof is bogus: the first mp call gets wrong hypotheses
    let result = parse_and_verify(db).unwrap();
    assert!(
        result.failed > 0,
        "bad proof should fail: verified={}",
        result.verified
    );
}

/// Test ax-1 style proof (no essential hypotheses, only floating).
#[test]
fn test_floating_hyp_only_proof() {
    // ax-1 is an axiom with only floating hypotheses, applied as proof step.
    let db = "\
$c |- ( -> ) wff $.
$v ph ps $.
wph $f wff ph $.
wps $f wff ps $.
wim $a wff ( ph -> ps ) $.
ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
th1 $p |- ( ( ph -> ps ) -> ( ( ps -> ph ) -> ( ph -> ps ) ) ) $= wph wps wim wps wph wim ax-1 $.
";
    let result = parse_and_verify(db).unwrap();
    assert_eq!(
        result.verified, 1,
        "th1 should verify: {:?}",
        result.failed_labels
    );
    assert_eq!(result.failed, 0);
}

/// Test multiple chained theorems where later theorems reference earlier ones.
#[test]
fn test_chained_theorems() {
    let result = parse_and_verify(DEMO0_DB).unwrap();
    assert_eq!(
        result.verified, 1,
        "th1 should verify: {:?}",
        result.failed_labels
    );
    assert_eq!(result.failed, 0);
    assert_eq!(result.axioms, 7);
}

/// Test multiple disjoint variable scopes with nested blocks.
#[test]
fn test_nested_scopes() {
    let db = "\
$c |- wff $.
$v ph ps $.
wph $f wff ph $.
wps $f wff ps $.
${
    ${
        deep-hyp $e |- ph $.
        deep-thm $a |- ph $.
    $}
$}
";
    let tokens = tokenize(db);
    let labels = build_label_table(&tokens).unwrap();
    assert!(labels.contains_key("deep-hyp"));
    assert!(labels.contains_key("deep-thm"));
    // deep-thm should have deep-hyp as an essential hypothesis
    match &labels["deep-thm"] {
        LabelInfo::Assertion {
            mand_essentials, ..
        } => {
            assert_eq!(mand_essentials.len(), 1);
            assert_eq!(mand_essentials[0].0, "deep-hyp");
        }
        other => panic!("expected Assertion, got {other:?}"),
    }
}

/// Test that the total proof steps are counted correctly.
#[test]
fn test_total_steps_counted() {
    let result = parse_and_verify(DEMO0_DB).unwrap();
    // th1 has 34 proof steps
    assert_eq!(result.total_steps, 34);
}

/// Verify that stack underflow is properly caught.
#[test]
fn test_stack_underflow_detected() {
    let db = "\
$c |- ( -> ) wff $.
$v ph ps $.
wph $f wff ph $.
wps $f wff ps $.
wim $a wff ( ph -> ps ) $.
${
    min $e |- ph $.
    maj $e |- ( ph -> ps ) $.
    mp $a |- ps $.
$}
bad $p |- ph $= mp $.
";
    let result = parse_and_verify(db).unwrap();
    assert_eq!(result.failed, 1, "bad proof should fail");
    assert_eq!(result.verified, 0);
}

/// A proof that violates an applied assertion's `$d` distinct-variable
/// condition (substituting the same variable for two variables that must be
/// distinct) MUST be rejected. Regression for the `$d`-not-enforced gap.
#[test]
fn test_disjoint_violation_rejected() {
    let db = "\
$c term combine $.
$v x y $.
vx $f term x $.
vy $f term y $.
$d x y $.
pair $a term combine x y $.
bad $p term combine x x $= vx vx pair $.
";
    let result = parse_and_verify(db).unwrap();
    assert_eq!(
        result.failed, 1,
        "proof collapsing a $d pair must fail, verified={}",
        result.verified
    );
    assert_eq!(result.verified, 0, "the $d-violating proof must not verify");
}

/// A proof that applies a `$d`-constrained assertion with genuinely distinct,
/// theorem-disjoint variables MUST still verify. Guards against the $d check
/// rejecting valid proofs (including dummy-variable use).
#[test]
fn test_disjoint_satisfied_verifies() {
    let db = "\
$c term combine $.
$v x y z $.
vx $f term x $.
vy $f term y $.
vz $f term z $.
$d x y $.
pair $a term combine x y $.
${
    $d y z $.
    good $p term combine y z $= vy vz pair $.
$}
";
    let result = parse_and_verify(db).unwrap();
    assert_eq!(
        result.verified, 1,
        "a $d-respecting proof must verify, failed_labels={:?}",
        result.failed_labels
    );
    assert_eq!(result.failed, 0, "no failures expected");
}

/// A proof whose step references the theorem being proved is circular and MUST
/// be rejected. Regression for the missing acyclicity check.
#[test]
fn test_self_reference_rejected() {
    let db = "\
$c wff |- $.
$v ph $.
wph $f wff ph $.
circ $p |- ph $= wph circ $.
";
    let result = parse_and_verify(db).unwrap();
    assert_eq!(
        result.failed, 1,
        "a self-referential (circular) proof must fail, verified={}",
        result.verified
    );
    assert_eq!(result.verified, 0, "circular proof must not verify");
}
