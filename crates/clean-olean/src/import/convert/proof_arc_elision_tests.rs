// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    convert_parsed_constant, elides_value, olean_kind_to_kernel_proof, proof_value_or_placeholder,
    ConvertedConstant, ExprInternCache, ImportError,
};
use crate::expr::ParsedExpr;
use crate::level::ParsedLevel;
use crate::module::{ConstantKind, ParsedConstant};
use clean_kernel::env::{Declaration, ProofValueElision};
use clean_kernel::expr::Expr;
use clean_kernel::level::Level;

// SOUNDNESS-CRITICAL: the conversion-time skip-set must EXACTLY equal the set
// the post-hoc null produces, i.e. elides_value must mirror
// ProofValueElision::elides on the kernel-mapped kind, for every kind+policy.
// A divergence would either drop a value the null keeps (changing the env) or
// keep one it drops (defeating the memory win).
#[test]
fn test_elides_value_mirrors_post_hoc_predicate() {
    use ConstantKind::*;
    let kinds = [
        Axiom,
        Definition,
        Theorem,
        Opaque,
        Quot,
        Inductive,
        Constructor,
        Recursor,
    ];
    let policies = [
        ProofValueElision::None,
        ProofValueElision::OpaqueOnly,
        ProofValueElision::OpaqueAndTheorem,
    ];
    for pol in policies {
        for k in &kinds {
            let expected = olean_kind_to_kernel_proof(k).is_some_and(|kk| pol.elides(kk));
            assert_eq!(elides_value(pol, k), expected, "mismatch for {pol:?} {k:?}");
        }
    }
    // Concrete skip-set per policy (only the two proof kinds are ever elided).
    assert!(!elides_value(ProofValueElision::None, &Opaque));
    assert!(elides_value(ProofValueElision::OpaqueOnly, &Opaque));
    assert!(!elides_value(ProofValueElision::OpaqueOnly, &Theorem));
    assert!(elides_value(ProofValueElision::OpaqueAndTheorem, &Opaque));
    assert!(elides_value(ProofValueElision::OpaqueAndTheorem, &Theorem));
    assert!(!elides_value(
        ProofValueElision::OpaqueAndTheorem,
        &Definition
    ));
}

#[test]
fn test_proof_value_or_placeholder_cases() {
    let real = Expr::sort(Level::zero());
    // Value present -> returned as-is.
    assert!(proof_value_or_placeholder(Some(real.clone()), false, "x").is_ok());
    // Absent but elided -> Ok (trivial placeholder).
    assert!(proof_value_or_placeholder(None, true, "x").is_ok());
    // Absent and NOT elided -> hard MissingValue error (no silent placeholder).
    assert!(matches!(
        proof_value_or_placeholder(None, false, "x"),
        Err(ImportError::MissingValue(_))
    ));
}

fn opaque_with_value(name: &str) -> ParsedConstant {
    ParsedConstant {
        name: name.to_string(),
        kind: ConstantKind::Opaque,
        level_params: vec![],
        type_: Some(ParsedExpr::Sort(ParsedLevel::Zero)),
        // A value node so the non-elided path interns ≥1 extra expr.
        value: Some(ParsedExpr::Const("f".to_string(), vec![])),
        inductive_val: None,
        constructor_val: None,
        recursor_val: None,
        hints: None,
        definition_safety: None,
        mutual_declarations: None,
        quot_kind: None,
    }
}

// The memory win: under elision the proof VALUE DAG is never built/interned,
// so the elided conversion interns strictly FEWER expr nodes than the
// full-resident one — and the placeholder still yields a valid Opaque decl.
#[test]
fn test_convert_opaque_skips_value_interning_under_elision() {
    let mut keep = ExprInternCache::default();
    let kept = convert_parsed_constant(
        &opaque_with_value("Foo"),
        &mut keep,
        ProofValueElision::None,
    );
    assert!(matches!(
        kept,
        ConvertedConstant::Other(_, Ok((Declaration::Opaque { .. }, _)), _)
    ));

    let mut elide = ExprInternCache::default();
    let elided = convert_parsed_constant(
        &opaque_with_value("Foo"),
        &mut elide,
        ProofValueElision::OpaqueOnly,
    );
    assert!(matches!(
        elided,
        ConvertedConstant::Other(_, Ok((Declaration::Opaque { .. }, _)), _)
    ));

    assert!(
        elide.total_entries < keep.total_entries,
        "elision must intern fewer exprs: elided={} keep={}",
        elide.total_entries,
        keep.total_entries
    );
}

// VERDICT-PARITY (constant SET): a value-less proof kind must be SKIPPED
// (MissingValue) under elision exactly as without it — never newly registered
// via a placeholder. `should_elide` is gated on `value.is_some()`, so the
// placeholder is only ever substituted for a real value we deliberately skipped.
#[test]
fn test_valueless_proof_kind_skipped_not_placeholdered_under_elision() {
    let mut c = opaque_with_value("NoVal");
    c.value = None; // value-less Opaque (e.g. a stub awaiting .olean.private upgrade)
    for pol in [
        ProofValueElision::None,
        ProofValueElision::OpaqueOnly,
        ProofValueElision::OpaqueAndTheorem,
    ] {
        let mut intern = ExprInternCache::default();
        let result = convert_parsed_constant(&c, &mut intern, pol);
        assert!(
            matches!(
                result,
                ConvertedConstant::Other(_, Err(ImportError::MissingValue(_)), _)
            ),
            "value-less Opaque under {pol:?} must hit MissingValue (skipped), not a placeholder"
        );
    }
}

// The per-constant walk uses this to complete its closure: a value-less proof
// helper (types-only skipped its body) that the FULL converter rejects with
// MissingValue is recovered as a VALUE-LESS trusted stub from its TYPE — kind
// preserved (Theorem/Opaque, never Axiom, so the axiom set is untouched).
#[test]
fn type_stub_recovers_a_valueless_proof_the_full_converter_rejects() {
    use clean_kernel::env::ConstantKind as KKind;

    let mut c = opaque_with_value("Priv._proof_1");
    c.value = None; // value-less Opaque

    // The full converter rejects a non-elided proof kind with no value.
    assert!(matches!(
        super::convert_parsed_constant_to_const_info(&c),
        Err(ImportError::MissingValue(_))
    ));

    // The type-stub recovers a value-less trusted ConstantInfo from the type.
    let stub = super::convert_parsed_constant_to_type_stub(&c)
        .expect("no convert error")
        .expect("some stub");
    assert!(stub.value.is_none(), "stub carries no value");
    assert_eq!(stub.kind, KKind::Opaque, "Opaque kind preserved");
    assert_ne!(stub.kind, KKind::Axiom, "never stubbed as an axiom");

    // A value-less Theorem stubs as Theorem (not Axiom).
    let mut t = opaque_with_value("Priv._simp_1");
    t.value = None;
    t.kind = ConstantKind::Theorem;
    let tstub = super::convert_parsed_constant_to_type_stub(&t)
        .unwrap()
        .unwrap();
    assert_eq!(tstub.kind, KKind::Theorem);

    // A type-less constant yields no stub (nothing to register).
    let mut nt = opaque_with_value("Priv._proof_2");
    nt.type_ = None;
    assert!(super::convert_parsed_constant_to_type_stub(&nt)
        .unwrap()
        .is_none());

    // An inductive family is never a definitional stub.
    let mut ind = opaque_with_value("SomeInductive");
    ind.kind = ConstantKind::Inductive;
    assert!(super::convert_parsed_constant_to_type_stub(&ind)
        .unwrap()
        .is_none());
}
