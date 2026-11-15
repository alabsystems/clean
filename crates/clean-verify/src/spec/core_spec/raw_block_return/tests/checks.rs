// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::{SpecError, Specification};
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
    } = parse_decl(&source).expect("explicit tuple AST")
    else {
        panic!("{name}: expected definition")
    };
    assert_eq!(
        parsed_name,
        clean_parser::parse_name(name).expect("explicit tuple name")
    );
    assert!(binders.is_empty(), "{name}: binders belong to tuple type");
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
            .expect("actual root")
            .is_empty(),
        "{name}: domain closure"
    );
    assert!(
        spec.env()
            .foundational_axiom_deps(&root)
            .expect("actual root")
            .is_empty(),
        "{name}: foundational closure"
    );
    assert!(
        crate::spec_axiom_closure::computed_axiom_closure(spec, name).is_empty(),
        "{name}: computed closure"
    );
}

pub(super) fn statement_sort(spec: &Specification, source: &str, is_prop: bool) {
    let ty = spec
        .elaborate_source(source, "raw block statement")
        .expect("statement elaborates");
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let sort = checker.infer_type(&ty).expect("statement sort");
    assert!(
        matches!(sort.kind(), ExprKind::Sort(_)),
        "statement has a sort"
    );
    assert_eq!(sort.is_prop(), is_prop, "actual Prop/Type partition");
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
            "{name}: data is not proof"
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
        .elaborate_source(ty_source, "raw block record type")
        .expect("type elaborates");
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    assert!(
        checker.is_def_eq(ty, &expected),
        "{name}: actual statement contract"
    );
    if let Some(is_prop) = proof_is_prop {
        let sort = checker.infer_type(ty).expect("actual statement sort");
        assert!(
            matches!(sort.kind(), ExprKind::Sort(_)),
            "{name}: statement sort"
        );
        assert_eq!(
            sort.is_prop(),
            is_prop,
            "{name}: actual Prop/Type partition"
        );
        assert_eq!(
            constant.kind,
            if is_prop {
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
        panic!("expected real inductive carrier")
    };
    let name = carrier_name(&name);
    let (fields, ctor_type) = match name.as_str() {
        "NamedCtorSource" => (2, "Name -> KExpr -> NamedCtorSource"),
        "NamedMemberSource" => (
            3,
            "Name -> KExpr -> ListType NamedCtorSource -> NamedMemberSource",
        ),
        _ => panic!("unexpected raw source carrier {name}"),
    };
    assert_eq!(
        ctors.iter().map(|c| c.name.clone()).collect::<Vec<_>>(),
        [clean_parser::parse_name("mk").expect("explicit constructor name")]
    );
    let root = Name::from_string(&name);
    let constant = spec.env().get_const(&root).expect("type former");
    let metadata = spec.env().get_inductive(&root).expect("inductive metadata");
    let record = spec.definitions().get(&name).expect("carrier record");
    assert!(!record.is_axiom, "{name}");
    assert_eq!(record.category, AxiomCategory::FoundationalRule, "{name}");
    assert_eq!(
        record.proof_status,
        ProofStatus::DerivedPending,
        "{name}: no promotion"
    );
    assert_eq!(
        record.type_src, "Type",
        "{name}: carrier registration source"
    );
    assert!(record.value_src.is_none());
    assert!(record.elaborated_value.is_none(), "{name}: genuine carrier");
    assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
    assert!(constant.value.is_none(), "{name}: genuine type former");
    assert_eq!((metadata.num_params, metadata.num_indices), (0, 0));
    assert!(
        metadata.level_params.is_empty(),
        "{name}: fixed Type universe"
    );
    assert_eq!(record.elaborated_type.as_ref(), Some(&constant.type_));
    assert_eq!(metadata.type_, constant.type_);
    assert!(
        matches!(metadata.type_.kind(), ExprKind::Sort(level) if level == &Level::succ(Level::zero())),
        "{name}: exactly Type"
    );
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    assert!(matches!(
        checker
            .infer_type(&constant.type_)
            .expect("carrier type checks")
            .kind(),
        ExprKind::Sort(_)
    ));
    empty_closures(spec, &name);

    let ctor_name = Name::from_string(&format!("{name}.mk"));
    assert_eq!(
        metadata.constructor_names.as_slice(),
        std::slice::from_ref(&ctor_name)
    );
    let ctor = spec
        .env()
        .get_constructor(&ctor_name)
        .expect("constructor metadata");
    let constant = spec
        .env()
        .get_const(&ctor_name)
        .expect("constructor constant");
    assert_eq!(ctor.inductive_name, root);
    assert_eq!(ctor.constructor_idx, 0);
    assert_eq!(ctor.num_params, 0);
    assert_eq!(ctor.num_fields, fields, "{name}: actual field count");
    assert_eq!(ctor.type_, constant.type_);
    assert_ne!(constant.kind, ConstantKind::Axiom);
    let record = spec
        .definitions()
        .get(&ctor_name.to_string())
        .expect("constructor record");
    assert!(!record.is_axiom);
    assert_eq!(record.category, AxiomCategory::FoundationalRule);
    assert_eq!(record.proof_status, ProofStatus::DerivedPending);
    assert_eq!(record.type_src, format!("(constructor of {name})"));
    assert_eq!(record.elaborated_type.as_ref(), Some(&constant.type_));
    assert!(record.value_src.is_none() && record.elaborated_value.is_none());
    let expected = spec
        .elaborate_source(ctor_type, "raw source constructor type")
        .expect("constructor contract");
    assert!(
        checker.is_def_eq(&constant.type_, &expected),
        "{name}: exact constructor fields/order"
    );
    assert!(matches!(
        checker
            .infer_type(&constant.type_)
            .expect("constructor type checks")
            .kind(),
        ExprKind::Sort(_)
    ));
    empty_closures(spec, &ctor_name.to_string());

    let rec_name = Name::from_string(&format!("{name}.rec"));
    let recursor = spec.env().get_recursor(&rec_name).expect("actual recursor");
    let constant = spec.env().get_const(&rec_name).expect("recursor constant");
    assert_eq!(recursor.type_, constant.type_);
    assert_eq!((recursor.num_params, recursor.num_indices), (0, 0));
    assert_eq!((recursor.num_motives, recursor.num_minors), (1, 1));
    assert_ne!(constant.kind, ConstantKind::Axiom);
    let record = spec
        .definitions()
        .get(&rec_name.to_string())
        .expect("recursor record");
    assert!(!record.is_axiom);
    assert_eq!(record.category, AxiomCategory::FoundationalRule);
    assert_eq!(record.proof_status, ProofStatus::DerivedPending);
    assert_eq!(record.type_src, format!("(recursor of {name})"));
    assert_eq!(record.elaborated_type.as_ref(), Some(&constant.type_));
    assert!(record.value_src.is_none() && record.elaborated_value.is_none());
    assert!(matches!(
        checker
            .infer_type(&constant.type_)
            .expect("recursor type checks")
            .kind(),
        ExprKind::Sort(_)
    ));
    empty_closures(spec, &rec_name.to_string());
}

pub(super) fn caller(spec: &Specification, source: &str, expected_type: &str) {
    let value = spec
        .elaborate_source(source, "raw block caller")
        .expect("caller elaborates");
    let expected = spec
        .elaborate_source(expected_type, "raw block caller type")
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
        .elaborate_source(source, "raw block computation")
        .expect("computation elaborates");
    let expected = spec
        .elaborate_source(expected_source, "raw block endpoint")
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
        .elaborate_source(left, "raw block distinct left")
        .expect("left elaborates");
    let right_value = spec
        .elaborate_source(right, "raw block distinct right")
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
