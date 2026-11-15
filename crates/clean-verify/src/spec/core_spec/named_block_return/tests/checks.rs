// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::{SpecError, Specification};
use crate::test_utils::parse_check;
use clean_kernel::{ConstantKind, ExprKind, Name, TypeChecker};
use clean_parser::{parse_decl, parse_expr, Span, SurfaceDecl};

fn fragment(source: &str, span: Span) -> Vec<&str> {
    source[span.start..span.end].split_whitespace().collect()
}

pub(super) fn tuple_ast(name: &str, ty: &str, body: &str) {
    let source = format!("def {name} : {ty} := {body}");
    parse_check(&source).expect("tuple declaration parses");
    let SurfaceDecl::Def {
        name: parsed_name,
        binders,
        ty: Some(parsed_type),
        val,
        ..
    } = parse_decl(&source).expect("explicit tuple AST")
    else {
        panic!("{name}: expected definition");
    };
    assert_eq!(
        parsed_name,
        clean_parser::parse_name(name).expect("explicit tuple name")
    );
    assert!(
        binders.is_empty(),
        "{name}: binders are explicit in tuple fragments"
    );
    let type_ast = parse_expr(ty).expect("standalone type AST");
    let body_ast = parse_expr(body).expect("standalone value AST");
    assert_eq!(
        fragment(&source, parsed_type.span()),
        fragment(ty, type_ast.span())
    );
    assert_eq!(
        fragment(&source, val.span()),
        fragment(body, body_ast.span())
    );
    assert_ne!(name, body.trim(), "{name}: no self-constant proof");
}

fn empty_closures(spec: &Specification, name: &str) {
    let root = Name::from_string(name);
    assert!(
        spec.env()
            .axiom_deps(&root)
            .expect("actual root exists")
            .is_empty(),
        "{name}: domain closure"
    );
    assert!(
        spec.env()
            .foundational_axiom_deps(&root)
            .expect("actual root exists")
            .is_empty(),
        "{name}: foundational closure"
    );
    assert!(
        crate::spec_axiom_closure::computed_axiom_closure(spec, name).is_empty(),
        "{name}: computed closure"
    );
}

pub(super) fn record(
    spec: &Specification,
    name: &str,
    ty_source: &str,
    body_source: &str,
    proof_is_prop: Option<bool>,
) {
    let record = spec.definitions().get(name).expect("actual record");
    let root = Name::from_string(name);
    let constant = spec.env().get_const(&root).expect("actual kernel root");
    let ty = record.elaborated_type.as_ref().expect("checked type");
    let body = record.elaborated_value.as_ref().expect("checked body");
    assert!(!record.is_axiom, "{name}");
    assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
    assert_eq!(record.category, AxiomCategory::DerivedLemma, "{name}");
    if proof_is_prop.is_some() {
        assert_eq!(record.proof_status, ProofStatus::DerivedProved, "{name}");
        assert_eq!(record.type_src, ty_source, "{name}: exact tuple type");
        assert_eq!(
            record.value_src.as_deref(),
            Some(body_source),
            "{name}: exact tuple body"
        );
    } else {
        assert_eq!(
            record.proof_status,
            ProofStatus::DerivedPending,
            "{name}: data is not a theorem"
        );
        assert_eq!(
            constant.kind,
            ConstantKind::Definition,
            "{name}: transparent data"
        );
        let source = format!("def {name} : {ty_source} := {body_source}");
        assert_eq!(record.type_src, source, "{name}: data source");
        assert_eq!(record.value_src.as_deref(), Some(source.as_str()));
    }
    assert_eq!(&constant.type_, ty, "{name}: kernel/record type");
    assert_eq!(
        constant.value.as_ref(),
        Some(body),
        "{name}: kernel/record body"
    );
    assert!(!matches!(body.kind(), ExprKind::Const(n, _) if n == &root));
    let expected = spec
        .elaborate_source(ty_source, "named block return type")
        .expect("type elaborates");
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    assert!(
        checker.is_def_eq(ty, &expected),
        "{name}: actual statement contract"
    );
    if let Some(expected_prop) = proof_is_prop {
        let sort = checker.infer_type(ty).expect("actual statement sort");
        assert_eq!(
            sort.is_prop(),
            expected_prop,
            "{name}: actual Prop/Type partition"
        );
        assert_eq!(
            constant.kind,
            if expected_prop {
                ConstantKind::Theorem
            } else {
                ConstantKind::Opaque
            },
            "{name}: actual proof kind"
        );
    }
    spec.verify_definition(name)
        .expect("stored body rechecks against stored type");
    empty_closures(spec, name);
}

pub(super) fn caller(spec: &Specification, source: &str, expected_type: &str) {
    let value = spec
        .elaborate_source(source, "named block return caller")
        .expect("caller elaborates");
    let expected = spec
        .elaborate_source(expected_type, "named block return caller type")
        .expect("type elaborates");
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let actual = checker.infer_type(&value).expect("caller kernel-checks");
    assert!(
        checker.is_def_eq(&actual, &expected),
        "{source}: actual caller type"
    );
}

pub(super) fn computes(spec: &Specification, source: &str, expected_source: &str) {
    let value = spec
        .elaborate_source(source, "named block return computation")
        .expect("computation elaborates");
    let expected = spec
        .elaborate_source(expected_source, "named block return endpoint")
        .expect("endpoint elaborates");
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let actual_type = checker
        .infer_type(&value)
        .expect("computation kernel-checks");
    let expected_type = checker
        .infer_type(&expected)
        .expect("endpoint kernel-checks");
    assert!(
        checker.is_def_eq(&actual_type, &expected_type),
        "{source}: same value type"
    );
    assert!(
        checker.is_def_eq(&value, &expected),
        "{source}: actual computation"
    );
}

pub(super) fn not_def_eq(spec: &Specification, left: &str, right: &str) {
    let left_value = spec
        .elaborate_source(left, "named block return distinct left")
        .expect("left elaborates");
    let right_value = spec
        .elaborate_source(right, "named block return distinct right")
        .expect("right elaborates");
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let left_type = checker.infer_type(&left_value).expect("left kernel-checks");
    let right_type = checker
        .infer_type(&right_value)
        .expect("right kernel-checks");
    assert!(
        checker.is_def_eq(&left_type, &right_type),
        "same object type"
    );
    assert!(
        !checker.is_def_eq(&left_value, &right_value),
        "distinct endpoints: {left} / {right}"
    );
}

pub(super) fn type_mismatch(name: &str, error: SpecError) {
    let message = match error {
        SpecError::TypeError(message) | SpecError::ElabError(message) => message,
        other => panic!("{name}: parser, missing-name, budget or environment failure is not the control: {other:?}"),
    };
    let lower = message.to_ascii_lowercase();
    assert!(
        lower.contains("type mismatch"),
        "{name}: actual type refusal required: {message}"
    );
    for unrelated in [
        "unknown identifier",
        "unknown constant",
        "unknown definition",
        "unresolved metavariable",
    ] {
        assert!(
            !lower.contains(unrelated),
            "{name}: unrelated failure: {message}"
        );
    }
}
