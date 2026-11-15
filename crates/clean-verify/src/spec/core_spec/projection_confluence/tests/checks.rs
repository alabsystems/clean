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
        clean_parser::parse_name(name).expect("explicit source name")
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

// SpecDefinition/legacy closure APIs still use text keys. Encode only an
// exact representable component path; never recover kernel identity from it.
fn legacy_record_key(name: &Name) -> String {
    use clean_kernel::name::NameInner;
    let mut parts = Vec::new();
    let mut current = name;
    loop {
        match current.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, part) => {
                assert!(
                    !part.is_empty() && !part.contains('.') && part.parse::<u64>().is_err(),
                    "non-representable legacy record name: {name:?}"
                );
                parts.push(part.to_string());
                current = parent;
            }
            NameInner::Num(parent, index) => {
                parts.push(index.to_string());
                current = parent;
            }
        }
    }
    assert!(!parts.is_empty(), "anonymous legacy record name");
    parts.reverse();
    parts.join(".")
}

fn empty_closures(spec: &Specification, name: &str) {
    let kernel_name = clean_parser::parse_name(name)
        .expect("explicit source name")
        .qualify_under(&Default::default())
        .into_name();
    empty_closures_typed(spec, &kernel_name);
}

fn empty_closures_typed(spec: &Specification, kernel_name: &Name) {
    let name = legacy_record_key(kernel_name);
    assert!(
        spec.env()
            .axiom_deps(kernel_name)
            .expect("actual root exists")
            .is_empty(),
        "{name}: domain closure"
    );
    assert!(
        spec.env()
            .foundational_axiom_deps(kernel_name)
            .expect("actual root exists")
            .is_empty(),
        "{name}: foundational closure"
    );
    assert!(
        crate::spec_axiom_closure::computed_axiom_closure(spec, &name).is_empty(),
        "{name}: independent computed closure"
    );
}

pub(super) fn caller(spec: &Specification, source: &str, expected_type: &str) {
    let value = spec
        .elaborate_source(source, "confluence caller")
        .expect("caller elaborates");
    let expected = spec
        .elaborate_source(expected_type, "confluence caller type")
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
        .elaborate_source(source, "confluence computation")
        .expect("computation elaborates");
    let expected = spec
        .elaborate_source(expected_source, "confluence result")
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
    is_proof: bool,
) {
    let record = spec.definitions().get(name).expect("actual record");
    let kernel_name = Name::from_string(name);
    let constant = spec.env().get_const(&kernel_name).expect("actual root");
    let ty = record.elaborated_type.as_ref().expect("checked type");
    let body = record.elaborated_value.as_ref().expect("checked body");
    assert!(!record.is_axiom, "{name}");
    assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
    assert_eq!(record.category, AxiomCategory::DerivedLemma, "{name}");
    if is_proof {
        assert_eq!(record.proof_status, ProofStatus::DerivedProved, "{name}");
        assert_eq!(record.type_src, ty_source, "{name}: exact tuple type");
        assert_eq!(
            record.value_src.as_deref(),
            Some(body_source),
            "{name}: exact tuple body"
        );
    } else {
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
        .elaborate_source(ty_source, "confluence type")
        .expect("tuple type elaborates");
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    assert!(checker.is_def_eq(ty, &expected), "{name}: actual statement");
    if is_proof {
        let sort = checker.infer_type(ty).expect("actual statement sort");
        let expected_kind = if sort.is_prop() {
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

fn carrier_shape(name: &clean_parser::SurfaceName) -> (u32, u32, &'static [&'static str]) {
    match name.name() {
        n if n == &Name::from_string("RelationStar") => (2, 2, &["refl", "step"]),
        n if n == &Name::from_string("RelationJoin") => (5, 0, &["mk"]),
        n if n == &Name::from_string("RelationUnion") => (5, 0, &["left", "right"]),
        n if n == &Name::from_string("par_reduces_cdp_star") => (1, 2, &["refl", "step"]),
        n if n == &Name::from_string("projection_parallel") => (
            1,
            2,
            &[
                "refl",
                "app",
                "lam",
                "pi",
                "forall_",
                "let_cong",
                "proj",
                "projection_beta",
            ],
        ),
        n if n == &Name::from_string("projection_parallel_list") => (1, 2, &["nil", "cons"]),
        n if n == &Name::from_string("projection_parallel_star") => (1, 2, &["refl", "step"]),
        n if [
            "ProjectionConstSpineView",
            "ProjectionParallelJoin",
            "ProjectionParallelStrip",
            "ProjectionParallelStarJoin",
            "CDProjectionPeak",
        ]
        .iter()
        .any(|candidate| n == &Name::from_string(candidate)) =>
        {
            (3, 0, &["mk"])
        }
        _ => panic!("unexpected confluence carrier {name}"),
    }
}

pub(super) fn carrier(spec: &Specification, source: &str) {
    let SurfaceDecl::Inductive { name, ctors, .. } = parse_decl(source).expect("carrier AST")
    else {
        panic!("expected real carrier declaration")
    };
    let (params, indices, ctor_names) = carrier_shape(&name);
    let names: Vec<_> = ctors.iter().map(|ctor| ctor.name.clone()).collect();
    assert_eq!(
        names,
        ctor_names
            .iter()
            .map(|n| clean_parser::parse_name(n).expect("explicit source name"))
            .collect::<Vec<_>>(),
        "{name}: actual arms and order"
    );
    let kernel_name = name.qualify_under(&Default::default()).into_name();
    let constant = spec.env().get_const(&kernel_name).expect("type former");
    let metadata = spec
        .env()
        .get_inductive(&kernel_name)
        .expect("inductive metadata");
    let record = spec
        .definitions()
        .get(&legacy_record_key(&kernel_name))
        .expect("carrier record");
    assert!(!record.is_axiom, "{name}");
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
    empty_closures_typed(spec, &kernel_name);
    let expected: Vec<_> = ctor_names
        .iter()
        .map(|ctor| {
            clean_parser::parse_name(ctor)
                .expect("explicit constructor name")
                .qualify_under(&clean_parser::SurfaceName::from_name(kernel_name.clone()))
                .into_name()
        })
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
        assert_eq!(ctor.type_, constant.type_);
        assert_ne!(constant.kind, ConstantKind::Axiom);
        assert!(matches!(
            checker
                .infer_type(&constant.type_)
                .expect("constructor type checks")
                .kind(),
            ExprKind::Sort(_)
        ));
        empty_closures_typed(spec, ctor_name);
    }
    let rec_name = kernel_name.str("rec");
    let recursor = spec.env().get_recursor(&rec_name).expect("actual recursor");
    let constant = spec.env().get_const(&rec_name).expect("recursor constant");
    assert_eq!(recursor.type_, constant.type_);
    assert_eq!(recursor.num_params, params, "{name}: recursor parameters");
    assert_eq!(recursor.num_indices, indices, "{name}: recursor indices");
    assert_ne!(constant.kind, ConstantKind::Axiom);
    assert!(matches!(
        checker
            .infer_type(&constant.type_)
            .expect("recursor type checks")
            .kind(),
        ExprKind::Sort(_)
    ));
    empty_closures_typed(spec, &rec_name);
}
