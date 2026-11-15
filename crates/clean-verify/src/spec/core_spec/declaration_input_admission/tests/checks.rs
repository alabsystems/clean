// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;
use crate::test_utils::parse_check;
use clean_kernel::{ConstantKind, Expr, ExprKind, Level, Name, TypeChecker};
use clean_parser::{parse_decl, parse_expr, Span, SurfaceDecl};

fn fragment(source: &str, span: Span) -> Vec<&str> {
    source[span.start..span.end].split_whitespace().collect()
}

pub(super) fn tuple_ast(name: &str, ty: &str, body: &str) {
    let source = format!("def {name} : {ty} := {body}");
    parse_check(&source).expect("tuple declaration parses");
    let SurfaceDecl::Def {
        name: actual_name,
        binders,
        ty: Some(actual_type),
        val,
        ..
    } = parse_decl(&source).expect("tuple AST")
    else {
        panic!("{name}: expected definition")
    };
    assert_eq!(actual_name, clean_parser::parse_name(name).expect("name"));
    assert!(binders.is_empty(), "{name}: all binders in tuple type");
    assert_eq!(
        fragment(&source, actual_type.span()),
        fragment(ty, parse_expr(ty).expect("type AST").span())
    );
    assert_eq!(
        fragment(&source, val.span()),
        fragment(body, parse_expr(body).expect("body AST").span())
    );
    assert_ne!(name, body.trim(), "{name}: no self-constant proof");
}

pub(super) fn elaborate(spec: &Specification, source: &str) -> Expr {
    spec.elaborate_source(source, "declaration input admission test")
        .expect("source elaborates")
}

pub(super) fn assert_sort(spec: &Specification, ty: &Expr, level: Level) {
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let sort = checker.infer_type_full(ty).expect("full statement check");
    let ExprKind::Sort(actual) = sort.kind() else {
        panic!("not a sort: {sort:?}")
    };
    assert!(Level::is_def_eq(actual, &level), "actual sort: {sort:?}");
}

pub(super) fn empty_closures(spec: &Specification, name: &str) {
    let root = Name::from_string(name);
    assert!(
        spec.env()
            .axiom_deps(&root)
            .expect("actual root")
            .is_empty(),
        "{name}"
    );
    assert!(
        spec.env()
            .foundational_axiom_deps(&root)
            .expect("actual root")
            .is_empty(),
        "{name}"
    );
    assert!(
        crate::spec_axiom_closure::computed_axiom_closure(spec, name).is_empty(),
        "{name}"
    );
}

pub(super) fn caller(spec: &Specification, source: &str, expected: &str) {
    let value = elaborate(spec, source);
    let ty = elaborate(spec, expected);
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    assert!(matches!(
        checker
            .infer_type_full(&ty)
            .expect("target type checks")
            .kind(),
        ExprKind::Sort(_)
    ));
    let actual = checker
        .infer_type_full(&value)
        .expect("caller fully checks");
    assert!(
        checker.is_def_eq(&actual, &ty),
        "{source}: caller statement"
    );
}

pub(super) fn computes(spec: &Specification, source: &str, expected: &str) {
    let value = elaborate(spec, source);
    let target = elaborate(spec, expected);
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let actual_ty = checker.infer_type_full(&value).expect("computation checks");
    let target_ty = checker.infer_type_full(&target).expect("endpoint checks");
    assert!(checker.is_def_eq(&actual_ty, &target_ty), "same type");
    assert!(checker.is_def_eq(&value, &target), "{source}: computation");
}

pub(super) fn record(
    spec: &Specification,
    name: &str,
    ty_source: &str,
    body_source: &str,
    proof: bool,
) {
    let record = spec.definitions().get(name).expect("registered record");
    let root = Name::from_string(name);
    let constant = spec.env().get_const(&root).expect("registered constant");
    let ty = record.elaborated_type.as_ref().expect("checked type");
    let body = record.elaborated_value.as_ref().expect("checked body");
    assert!(!record.is_axiom, "{name}");
    assert_eq!(record.category, AxiomCategory::DerivedLemma, "{name}");
    if proof {
        assert_eq!(record.proof_status, ProofStatus::DerivedProved, "{name}");
        assert_eq!(constant.kind, ConstantKind::Opaque, "{name}: Type proof");
        assert_eq!(record.type_src, ty_source);
        assert_eq!(record.value_src.as_deref(), Some(body_source));
    } else {
        assert_eq!(
            record.proof_status,
            ProofStatus::DerivedPending,
            "{name}: data"
        );
        assert_eq!(constant.kind, ConstantKind::Definition, "{name}: data");
        let source = format!("def {name} : {ty_source} := {body_source}");
        assert_eq!(record.type_src, source);
        assert_eq!(record.value_src.as_deref(), Some(source.as_str()));
    }
    assert_eq!(&constant.type_, ty);
    assert_eq!(constant.value.as_ref(), Some(body));
    assert!(!matches!(body.kind(), ExprKind::Const(n, _) if n == &root));
    let expected = elaborate(spec, ty_source);
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    assert!(checker.is_def_eq(ty, &expected), "{name}: exact statement");
    let actual = checker
        .infer_type_full(body)
        .expect("stored body fully checks");
    assert!(
        checker.is_def_eq(&actual, ty),
        "{name}: body has declared type"
    );
    let one = Level::succ(Level::zero());
    assert_sort(
        spec,
        ty,
        if matches!(name, "dia_admission_at" | "dia_requests_admitted") {
            Level::succ(one)
        } else {
            one
        },
    );
    spec.verify_definition(name)
        .expect("stored record rechecks");
    empty_closures(spec, name);
}
