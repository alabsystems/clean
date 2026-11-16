// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual registration checks for the frozen constructor-rigidity/spine unit.
//! These inspect the finite reflected model, not production Rust refinement or
//! projection beta. In particular, the collision environments are deliberately
//! conflicting model data, not declarations admitted by the source kernel.

use super::super::acceptance_in::theorem;
use super::{
    DeclarationInput, DATA_NAMES, DECLARATIONS, INDUCTIVE_NAMES, NEGATIVE_CONTROLS, PROOF_ROOTS,
};
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;
use crate::test_utils::{build_spec_with_stack, parse_check, run_with_stack};
use clean_kernel::{ConstantKind, ExprKind, Level, Name, TypeChecker};
use clean_parser::{parse_decl, parse_expr, Span, SurfaceDecl};
use std::collections::HashSet;

fn fragment(source: &str, span: Span) -> Vec<&str> {
    source[span.start..span.end].split_whitespace().collect()
}

fn check_tuple_ast(name: &str, ty: &str, body: &str) {
    let source = format!("def {name} : {ty} := {body}");
    parse_check(&source).expect("explicit declaration parses");
    let SurfaceDecl::Def {
        name: parsed_name,
        binders,
        ty: Some(parsed_type),
        val,
        ..
    } = parse_decl(&source).expect("explicit declaration AST")
    else {
        panic!("{name}: expected an explicitly typed definition")
    };
    assert_eq!(
        parsed_name,
        clean_parser::parse_name(name).expect("explicit source name")
    );
    assert!(
        binders.is_empty(),
        "{name}: binders belong inside the tuple"
    );
    let type_ast = parse_expr(ty).expect("standalone record type AST");
    let body_ast = parse_expr(body).expect("standalone record body AST");
    assert_eq!(
        fragment(&source, parsed_type.span()),
        fragment(ty, type_ast.span()),
        "{name}: exact type fragment"
    );
    assert_eq!(
        fragment(&source, val.span()),
        fragment(body, body_ast.span()),
        "{name}: exact body fragment"
    );
    assert_ne!(body.trim(), name, "{name}: no self-constant body");
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

fn assert_empty_closures(spec: &Specification, name: &str) {
    let kernel_name = clean_parser::parse_name(name)
        .expect("explicit source name")
        .qualify_under(&Default::default())
        .into_name();
    assert_empty_closures_typed(spec, &kernel_name);
}

fn assert_empty_closures_typed(spec: &Specification, kernel_name: &Name) {
    let name = legacy_record_key(kernel_name);
    assert!(
        spec.env()
            .axiom_deps(kernel_name)
            .expect("actual root exists for domain closure")
            .is_empty(),
        "{name}: domain closure"
    );
    assert!(
        spec.env()
            .foundational_axiom_deps(kernel_name)
            .expect("actual root exists for foundational closure")
            .is_empty(),
        "{name}: foundational closure"
    );
    assert!(
        crate::spec_axiom_closure::computed_axiom_closure(spec, &name).is_empty(),
        "{name}: computed closure"
    );
}

fn check_carrier(spec: &Specification, source: &str) {
    let SurfaceDecl::Inductive { name, ctors, .. } =
        parse_decl(source).expect("actual carrier source parses")
    else {
        panic!("expected an inductive carrier")
    };
    let kernel_name = name.qualify_under(&Default::default()).into_name();
    let constant = spec
        .env()
        .get_const(&kernel_name)
        .expect("actual type former");
    let metadata = spec
        .env()
        .get_inductive(&kernel_name)
        .expect("actual inductive metadata");
    let record = spec
        .definitions()
        .get(&legacy_record_key(&kernel_name))
        .expect("registered carrier record");
    assert!(!record.is_axiom, "{name}");
    assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
    assert_eq!(
        record.elaborated_type.as_ref(),
        Some(&constant.type_),
        "{name}"
    );
    assert_eq!(metadata.type_, constant.type_, "{name}: metadata type");
    assert!(
        constant.value.is_none(),
        "{name}: carrier is not a bodyful proof"
    );
    assert!(
        metadata.level_params.is_empty(),
        "{name}: fixed Type carrier"
    );
    let mut result = &metadata.type_;
    while let ExprKind::Pi(_, _, codomain) = result.kind() {
        result = codomain;
    }
    assert!(
        matches!(result.kind(), ExprKind::Sort(level) if level == &Level::succ(Level::zero())),
        "{name}: Type, not Prop; Type-valued continuation elimination is required"
    );
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let carrier_sort = checker
        .infer_type(&constant.type_)
        .expect("actual carrier type is well formed");
    assert!(matches!(carrier_sort.kind(), ExprKind::Sort(_)), "{name}");
    assert_empty_closures_typed(spec, &kernel_name);

    let expected_ctors: Vec<_> = ctors
        .iter()
        .map(|ctor| {
            ctor.name
                .qualify_under(&clean_parser::SurfaceName::from_name(kernel_name.clone()))
                .into_name()
        })
        .collect();
    assert_eq!(
        metadata.constructor_names, expected_ctors,
        "{name}: constructor order"
    );
    for (index, ctor_name) in expected_ctors.iter().enumerate() {
        let ctor = spec
            .env()
            .get_constructor(ctor_name)
            .expect("actual constructor metadata");
        let ctor_constant = spec
            .env()
            .get_const(ctor_name)
            .expect("actual constructor constant");
        assert_eq!(ctor.inductive_name, kernel_name, "{ctor_name}: parent");
        assert_eq!(ctor.constructor_idx as usize, index, "{ctor_name}: index");
        assert_eq!(ctor.type_, ctor_constant.type_, "{ctor_name}: signature");
        assert_ne!(ctor_constant.kind, ConstantKind::Axiom, "{ctor_name}");
        let constructor_sort = checker
            .infer_type(&ctor_constant.type_)
            .expect("actual constructor type rechecks");
        assert!(
            matches!(constructor_sort.kind(), ExprKind::Sort(_)),
            "{ctor_name}"
        );
        assert_empty_closures_typed(spec, ctor_name);
    }
    let rec_name = kernel_name.str("rec");
    let recursor = spec
        .env()
        .get_recursor(&rec_name)
        .expect("actual carrier recursor");
    let rec_constant = spec
        .env()
        .get_const(&rec_name)
        .expect("actual recursor constant");
    assert_eq!(recursor.type_, rec_constant.type_, "{rec_name}: signature");
    assert_ne!(rec_constant.kind, ConstantKind::Axiom, "{rec_name}");
    let recursor_sort = checker
        .infer_type(&rec_constant.type_)
        .expect("actual recursor type rechecks");
    assert!(
        matches!(recursor_sort.kind(), ExprKind::Sort(_)),
        "{rec_name}"
    );
    assert_empty_closures_typed(spec, &rec_name);
}

#[test]
fn constructor_projection_records_parse_with_exact_partitions() {
    assert_eq!(DECLARATIONS.len(), 44);
    assert_eq!(PROOF_ROOTS.len(), 36);
    assert_eq!(DATA_NAMES.len(), 5);
    assert_eq!(INDUCTIVE_NAMES.len(), 3);
    assert_eq!(NEGATIVE_CONTROLS.len(), 4);
    let mut names = HashSet::new();
    let mut proofs = Vec::new();
    let mut data = Vec::new();
    let mut carriers = Vec::new();
    for declaration in DECLARATIONS {
        match declaration {
            DeclarationInput::Inductive(source) => {
                parse_check(source).expect("exact carrier declaration parses");
                let SurfaceDecl::Inductive { name, ty, .. } =
                    parse_decl(source).expect("carrier AST")
                else {
                    panic!("expected an inductive declaration")
                };
                // The full type may include indices; the runtime test checks
                // its terminal sort rather than inferring Type from a name.
                assert!(!fragment(source, ty.span()).is_empty());
                assert!(
                    names.insert(name.qualify_under(&Default::default()).into_name()),
                    "duplicate carrier {name}"
                );
                carriers.push(name.qualify_under(&Default::default()).into_name());
            }
            DeclarationInput::Proof(name, ty, body) => {
                check_tuple_ast(name, ty, body);
                assert!(
                    names.insert(
                        clean_parser::parse_name(name)
                            .expect("explicit source name")
                            .qualify_under(&Default::default())
                            .into_name()
                    ),
                    "duplicate proof {name}"
                );
                proofs.push(*name);
            }
            DeclarationInput::Data(name, ty, body) => {
                check_tuple_ast(name, ty, body);
                assert!(
                    names.insert(
                        clean_parser::parse_name(name)
                            .expect("explicit source name")
                            .qualify_under(&Default::default())
                            .into_name()
                    ),
                    "duplicate data {name}"
                );
                data.push(*name);
            }
        }
    }
    assert_eq!(proofs, PROOF_ROOTS, "every proof root in original order");
    assert_eq!(data, DATA_NAMES, "transparent data is not a proof root");
    assert_eq!(
        carriers,
        INDUCTIVE_NAMES
            .iter()
            .map(|n| clean_parser::parse_name(n)
                .expect("explicit source name")
                .qualify_under(&Default::default())
                .into_name())
            .collect::<Vec<_>>(),
        "carrier order"
    );
    assert_eq!(names.len(), 44);
    for &(name, ty, body) in NEGATIVE_CONTROLS {
        check_tuple_ast(name, ty, body);
        assert!(
            names.insert(
                clean_parser::parse_name(name)
                    .expect("explicit source name")
                    .qualify_under(&Default::default())
                    .into_name()
            ),
            "refusal name collision: {name}"
        );
    }
}

#[test]
fn constructor_projection_actual_records_recheck_with_empty_closures() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        for declaration in DECLARATIONS {
            let (name, ty_source, body_source, is_proof) = match declaration {
                DeclarationInput::Inductive(source) => {
                    check_carrier(&spec, source);
                    continue;
                }
                DeclarationInput::Proof(name, ty, body) => (*name, *ty, *body, true),
                DeclarationInput::Data(name, ty, body) => (*name, *ty, *body, false),
            };
            let record = spec
                .definitions()
                .get(name)
                .expect("registered declaration");
            let kernel_name = Name::from_string(name);
            let constant = spec
                .env()
                .get_const(&kernel_name)
                .expect("actual kernel root");
            let ty = record
                .elaborated_type
                .as_ref()
                .expect("actual checked type");
            let body = record
                .elaborated_value
                .as_ref()
                .expect("actual checked body");
            assert!(!record.is_axiom, "{name}");
            assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
            assert_eq!(record.category, AxiomCategory::DerivedLemma, "{name}");
            if is_proof {
                assert_eq!(record.proof_status, ProofStatus::DerivedProved, "{name}");
                assert_eq!(record.type_src, ty_source, "{name}: exact explicit type");
                assert_eq!(
                    record.value_src.as_deref(),
                    Some(body_source),
                    "{name}: exact body"
                );
            } else {
                // These values participate in computation and cannot be opaque
                // theorem records merely because their source was Lean-checked.
                assert_eq!(
                    constant.kind,
                    ConstantKind::Definition,
                    "{name}: transparent data"
                );
                let source = format!("def {name} : {ty_source} := {body_source}");
                assert_eq!(record.type_src, source, "{name}: original data declaration");
                assert_eq!(record.value_src.as_deref(), Some(source.as_str()), "{name}");
            }
            assert_eq!(&constant.type_, ty, "{name}: kernel/record type agreement");
            assert_eq!(
                constant.value.as_ref(),
                Some(body),
                "{name}: kernel/record body agreement"
            );
            assert!(
                !matches!(body.kind(), ExprKind::Const(n, _) if n == &kernel_name),
                "{name}: no self-reference body"
            );
            let expected = spec
                .elaborate_source(ty_source, "constructor registration type")
                .expect("tuple type elaborates");
            let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
            assert!(
                checker.is_def_eq(ty, &expected),
                "{name}: tuple/actual type agreement"
            );
            spec.verify_definition(name)
                .expect("actual body checks against actual type");
            assert_empty_closures(&spec, name);
        }
    });
}

#[test]
fn constructor_projection_real_reflected_and_selected_callers_check() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        for (value_source, type_source) in [
            ("reflected_ctor_metadata_rigid", "CtorMetadataRigid the_red_env (red_ind_ctor the_red_env)"),
            ("reflected_prod_ctor_lookup", "@Eq (OptionType KCtorMeta) (kctor_for (red_ind_ctor the_red_env) kcre_prod_mk_name) (@OptionType.some KCtorMeta kcre_prod_ctor_meta)"),
            ("reflected_prod_ctor_no_def", "@Eq (OptionType KExpr) (defval_for (red_def the_red_env) kcre_prod_mk_name) (@OptionType.none KExpr)"),
            ("reflected_prod_ctor_no_rec", "@Eq (OptionType RecMeta) (recmeta_for (red_rec the_red_env) kcre_prod_mk_name) (@OptionType.none RecMeta)"),
            ("reflected_prod_value_delta_none", "@Eq (OptionType KExpr) (delta_reduct (red_def the_red_env) kcre_witness_prod_value) (@OptionType.none KExpr)"),
            ("reflected_prod_value_iota_none", "@Eq (OptionType KExpr) (iota_reduct (red_rec the_red_env) kcre_witness_prod_value) (@OptionType.none KExpr)"),
            ("ctor_spine_prod_step", "par_reduces_cd the_red_env ctor_spine_prod_before kcre_witness_prod_value"),
            ("ctor_spine_prod_head_preserved", "@Eq KExpr (kapp_fn kcre_witness_prod_value) (KExpr.const kcre_prod_mk_name (@ListType.nil Level))"),
            ("ctor_spine_prod_length_preserved", "@Eq Nat (list_length (kapp_args ctor_spine_prod_before)) (list_length (kapp_args kcre_witness_prod_value))"),
            ("ctor_spine_prod_selected_zero", "par_reduces_cd the_red_env ctor_spine_prod_redex rfnz_zero"),
            ("ctor_spine_prod_selected_one", "par_reduces_cd the_red_env (KExpr.app rfnz_succ rfnz_zero) (KExpr.app rfnz_succ rfnz_zero)"),
            ("ctor_metadata_def_collision_refused", "forall (h : CtorMetadataRigid ctor_rigid_def_collision_env (red_ind_ctor ctor_rigid_def_collision_env)) (C : Prop), C"),
            ("ctor_metadata_rec_collision_refused", "forall (h : CtorMetadataRigid ctor_rigid_rec_collision_env (red_ind_ctor ctor_rigid_rec_collision_env)) (C : Prop), C"),
        ] {
            let value = spec.elaborate_source(value_source, "actual constructor caller").expect("caller elaborates");
            let expected = spec.elaborate_source(type_source, "actual constructor caller type").expect("caller type elaborates");
            let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
            let actual = checker.infer_type(&value).expect("actual caller checks");
            assert!(checker.is_def_eq(&actual, &expected), "{value_source}: actual endpoint");
        }
    });
}

#[test]
fn constructor_projection_refuses_collisions_endpoint_and_universe_forgery() {
    run_with_stack(|| {
        // The shared FULL_SPEC builds once per process; rejection mutations
        // happen only in this owned clone, never in the shared environment.
        let mut spec = build_spec_with_stack();
        for &(name, ty, body) in NEGATIVE_CONTROLS {
            check_tuple_ast(name, ty, body);
            let kernel_name = Name::from_string(name);
            assert!(
                !spec.definitions().contains_key(name),
                "{name}: precondition"
            );
            assert!(
                spec.env().get_const(&kernel_name).is_none(),
                "{name}: precondition"
            );
            let error = theorem(
                &mut spec,
                name,
                ty,
                body,
                "Reject a conflicting constructor invariant or a forged selected endpoint/head universe.",
            ).expect_err("well-parsed forged evidence must fail actual type checking");
            assert!(
                format!("{error:?}").contains("Type mismatch"),
                "{name}: {error:?}"
            );
            assert!(
                !spec.definitions().contains_key(name),
                "{name}: no failed record"
            );
            assert!(
                spec.env().get_const(&kernel_name).is_none(),
                "{name}: no failed kernel root"
            );
        }
    });
}
