// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;
use crate::test_utils::parse_check;
use clean_kernel::{ConstantKind, ExprKind, Level, Name, TypeChecker};
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
    } = parse_decl(&source).expect("explicit definition AST")
    else {
        panic!("{name}: expected explicit definition")
    };
    assert_eq!(
        parsed_name,
        clean_parser::parse_name(name).expect("explicit tuple name")
    );
    assert!(binders.is_empty(), "{name}: all binders belong to tuple");
    let type_ast = parse_expr(ty).expect("standalone type AST");
    let body_ast = parse_expr(body).expect("standalone body AST");
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
    let kernel_name = Name::from_string(name);
    assert!(
        spec.env()
            .axiom_deps(&kernel_name)
            .expect("actual root exists")
            .is_empty(),
        "{name}: domain closure"
    );
    assert!(
        spec.env()
            .foundational_axiom_deps(&kernel_name)
            .expect("actual root exists")
            .is_empty(),
        "{name}: foundational closure"
    );
    assert!(
        crate::spec_axiom_closure::computed_axiom_closure(spec, name).is_empty(),
        "{name}: independent computed closure"
    );
}

pub(super) fn caller(spec: &Specification, source: &str, expected_type: &str) {
    let value = spec
        .elaborate_source(source, "projection typing caller")
        .expect("caller elaborates");
    let expected = spec
        .elaborate_source(expected_type, "projection typing caller type")
        .expect("type elaborates");
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let actual = checker.infer_type(&value).expect("actual caller checks");
    assert!(
        checker.is_def_eq(&actual, &expected),
        "{source}: exact caller type"
    );
}

pub(super) fn computes(spec: &Specification, source: &str, expected_source: &str) {
    let value = spec
        .elaborate_source(source, "projection typing computation")
        .expect("computation elaborates");
    let expected = spec
        .elaborate_source(expected_source, "projection typing result")
        .expect("result elaborates");
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let actual_ty = checker.infer_type(&value).expect("computation checks");
    let expected_ty = checker.infer_type(&expected).expect("result checks");
    assert!(
        checker.is_def_eq(&actual_ty, &expected_ty),
        "{source}: same value type"
    );
    assert!(
        checker.is_def_eq(&value, &expected),
        "{source}: actual computation"
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
    let kernel_name = Name::from_string(name);
    let constant = spec.env().get_const(&kernel_name).expect("actual root");
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
            "{name}: data is not a proved theorem"
        );
        assert_eq!(
            constant.kind,
            ConstantKind::Definition,
            "{name}: transparent data"
        );
        let source = format!("def {name} : {ty_source} := {body_source}");
        assert_eq!(record.type_src, source, "{name}: exact data source");
        assert_eq!(record.value_src.as_deref(), Some(source.as_str()));
    }
    assert_eq!(&constant.type_, ty, "{name}: kernel/record type agreement");
    assert_eq!(
        constant.value.as_ref(),
        Some(body),
        "{name}: kernel/record body agreement"
    );
    assert!(!matches!(body.kind(), ExprKind::Const(n, _) if n == &kernel_name));
    let expected = spec
        .elaborate_source(ty_source, "projection typing type")
        .expect("tuple type elaborates");
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    assert!(checker.is_def_eq(ty, &expected), "{name}: actual statement");
    if let Some(expected_prop) = proof_is_prop {
        let sort = checker.infer_type(ty).expect("actual statement sort");
        assert_eq!(
            sort.is_prop(),
            expected_prop,
            "{name}: fixed Prop/Type partition"
        );
        let expected_kind = if expected_prop {
            ConstantKind::Theorem
        } else {
            ConstantKind::Opaque
        };
        assert_eq!(constant.kind, expected_kind, "{name}: actual proof opacity");
    }
    spec.verify_definition(name)
        .expect("actual body rechecks against stored type");
    empty_closures(spec, name);
}

fn carrier_shape(name: &str) -> (u32, u32, &'static [&'static str]) {
    match name {
        "TypingCDPCtxConvIn" => (
            2,
            3,
            &[
                "var",
                "sort",
                "pi",
                "lam",
                "app",
                "const",
                "conv",
                "let_",
                "lit_nat",
                "lit_string",
            ],
        ),
        "SemanticTypingCDPAppReturn" | "SemanticTypingCDPPiReturn" => (6, 0, &["intro"]),
        "SemanticTypingCDPConstantReturn" => (5, 0, &["intro"]),
        "TypedRawPiSpineCDP" => (3, 3, &["nil", "cons"]),
        "SemanticTypedSpineCDPReturn" => (8, 0, &["intro"]),
        _ => panic!("unexpected projection typing carrier {name}"),
    }
}

// Recover a legacy record key only by matching an explicitly declared carrier.
// Never derive kernel identity by rendering a parsed structured name.
pub(super) fn carrier_name(name: &clean_parser::SurfaceName) -> String {
    super::COHORTS
        .iter()
        .flat_map(|cohort| cohort.carriers.iter().copied())
        .find(|expected| {
            name == &clean_parser::parse_name(expected).expect("explicit carrier name")
        })
        .expect("parsed carrier belongs to the reviewed cohort")
        .to_owned()
}

pub(super) fn carrier(spec: &Specification, source: &str) {
    let SurfaceDecl::Inductive { name, ctors, .. } = parse_decl(source).expect("carrier AST")
    else {
        panic!("expected real carrier declaration")
    };
    let name = carrier_name(&name);
    let (params, indices, ctor_names) = carrier_shape(&name);
    let names: Vec<_> = ctors.iter().map(|ctor| ctor.name.clone()).collect();
    assert_eq!(
        names,
        ctor_names
            .iter()
            .map(|ctor| clean_parser::parse_name(ctor).expect("explicit constructor name"))
            .collect::<Vec<_>>(),
        "{name}: actual arms and order"
    );
    let kernel_name = Name::from_string(&name);
    let constant = spec.env().get_const(&kernel_name).expect("type former");
    let metadata = spec
        .env()
        .get_inductive(&kernel_name)
        .expect("inductive metadata");
    let record = spec.definitions().get(&name).expect("carrier record");
    assert!(!record.is_axiom, "{name}");
    assert_eq!(record.category, AxiomCategory::FoundationalRule, "{name}");
    assert_eq!(
        record.proof_status,
        ProofStatus::DerivedPending,
        "{name}: no status promotion"
    );
    assert!(
        record.elaborated_value.is_none(),
        "{name}: real type former"
    );
    assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
    assert!(constant.value.is_none(), "{name}: genuine carrier");
    assert_eq!(metadata.num_params, params, "{name}: actual parameters");
    assert_eq!(metadata.num_indices, indices, "{name}: actual indices");
    assert!(
        metadata.level_params.is_empty(),
        "{name}: fixed Type universe"
    );
    assert_eq!(record.elaborated_type.as_ref(), Some(&constant.type_));
    assert_eq!(metadata.type_, constant.type_);
    let mut result = &metadata.type_;
    while let ExprKind::Pi(_, _, codomain) = result.kind() {
        result = codomain;
    }
    assert!(
        matches!(result.kind(), ExprKind::Sort(level) if level == &Level::succ(Level::zero())),
        "{name}: Type-valued, not Prop"
    );
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    assert!(matches!(
        checker
            .infer_type(&constant.type_)
            .expect("type checks")
            .kind(),
        ExprKind::Sort(_)
    ));
    empty_closures(spec, &name);
    let expected: Vec<_> = ctor_names
        .iter()
        .map(|ctor| Name::from_string(&format!("{name}.{ctor}")))
        .collect();
    assert_eq!(metadata.constructor_names, expected);
    for (index, ctor_name) in expected.iter().enumerate() {
        let ctor = spec
            .env()
            .get_constructor(ctor_name)
            .expect("constructor metadata");
        let constant = spec
            .env()
            .get_const(ctor_name)
            .expect("constructor constant");
        assert_eq!(ctor.inductive_name, kernel_name);
        assert_eq!(ctor.constructor_idx as usize, index);
        assert_eq!(ctor.num_params, params, "{name}: constructor parameters");
        assert_eq!(ctor.type_, constant.type_);
        assert_ne!(constant.kind, ConstantKind::Axiom);
        assert!(matches!(
            checker
                .infer_type(&constant.type_)
                .expect("constructor type checks")
                .kind(),
            ExprKind::Sort(_)
        ));
        empty_closures(spec, &ctor_name.to_string());
    }
    let rec_name = Name::from_string(&format!("{name}.rec"));
    let recursor = spec.env().get_recursor(&rec_name).expect("actual recursor");
    let constant = spec.env().get_const(&rec_name).expect("recursor constant");
    assert_eq!(recursor.type_, constant.type_);
    assert_eq!(recursor.num_params, params, "{name}: recursor parameters");
    assert_eq!(recursor.num_indices, indices, "{name}: recursor indices");
    assert_eq!(recursor.num_motives, 1, "{name}: one genuine motive");
    assert_eq!(
        recursor.num_minors as usize,
        ctor_names.len(),
        "{name}: one minor per arm"
    );
    assert_ne!(constant.kind, ConstantKind::Axiom);
    assert!(matches!(
        checker
            .infer_type(&constant.type_)
            .expect("recursor type checks")
            .kind(),
        ExprKind::Sort(_)
    ));
    empty_closures(spec, &rec_name.to_string());
}

/// Raw object syntax is distinct even when a separate model proof relates its levels.
pub(super) fn not_def_eq(spec: &Specification, left: &str, right: &str) {
    let left_value = spec
        .elaborate_source(left, "raw left")
        .expect("left elaborates");
    let right_value = spec
        .elaborate_source(right, "raw right")
        .expect("right elaborates");
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let left_type = checker.infer_type(&left_value).expect("left checks");
    let right_type = checker.infer_type(&right_value).expect("right checks");
    assert!(
        checker.is_def_eq(&left_type, &right_type),
        "same object type"
    );
    assert!(
        !checker.is_def_eq(&left_value, &right_value),
        "raw endpoints must differ: {left} / {right}"
    );
}
