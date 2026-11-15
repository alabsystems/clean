// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual registration and computational checks for the raw projection unit.
//! These do not establish admission, dependent field typing, whole-relation
//! confluence, projection-aware WHNF, or correspondence with production Rust.

use super::super::acceptance_in::theorem;
use super::{
    declarations, DeclarationInput, DATA_NAMES, INDUCTIVE_NAMES, NEGATIVE_CONTROLS, PROOF_ROOTS,
};
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;
use crate::test_utils::{parse_check, run_with_stack, shared_spec};
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
    assert!(binders.is_empty(), "{name}: tuple owns all binders");
    let type_ast = parse_expr(ty).expect("standalone tuple type AST");
    let body_ast = parse_expr(body).expect("standalone tuple body AST");
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
        "{name}: independently computed closure"
    );
}

fn expected_constructors(name: &clean_parser::SurfaceName) -> &'static [&'static str] {
    match name.name() {
        n if n == &Name::from_string("par_reduces_cdp") => &[
            "refl",
            "beta",
            "app",
            "lam",
            "pi",
            "forall_",
            "let_",
            "iota",
            "delta",
            "let_cong",
            "proj",
            "projection_beta",
        ],
        n if n == &Name::from_string("par_reduces_cdp_list") => &["nil", "cons"],
        n if n == &Name::from_string("ParCDPCtorSpineView") => &["mk"],
        _ => panic!("unexpected projection carrier {name}"),
    }
}

fn check_carrier(spec: &Specification, source: &str) {
    let SurfaceDecl::Inductive { name, ctors, .. } =
        parse_decl(source).expect("actual carrier AST")
    else {
        panic!("expected an inductive carrier")
    };
    let names: Vec<_> = ctors.iter().map(|ctor| ctor.name.clone()).collect();
    assert_eq!(
        names,
        expected_constructors(&name)
            .iter()
            .map(|n| clean_parser::parse_name(n).expect("explicit source name"))
            .collect::<Vec<_>>(),
        "{name}: real arms"
    );
    let kernel_name = name.qualify_under(&Default::default()).into_name();
    let constant = spec.env().get_const(&kernel_name).expect("type former");
    let metadata = spec
        .env()
        .get_inductive(&kernel_name)
        .expect("actual inductive metadata");
    let record = spec
        .definitions()
        .get(&legacy_record_key(&kernel_name))
        .expect("carrier record");
    assert!(!record.is_axiom, "{name}");
    assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
    assert_eq!(record.elaborated_type.as_ref(), Some(&constant.type_));
    assert_eq!(metadata.type_, constant.type_, "{name}: metadata type");
    assert!(
        constant.value.is_none(),
        "{name}: actual carrier, not a proof"
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
        "{name}: actual Type-valued elimination, not Prop"
    );
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let sort = checker
        .infer_type(&constant.type_)
        .expect("carrier type rechecks");
    assert!(matches!(sort.kind(), ExprKind::Sort(_)), "{name}");
    assert_empty_closures_typed(spec, &kernel_name);

    let expected: Vec<_> = names
        .iter()
        .map(|ctor| {
            ctor.qualify_under(&clean_parser::SurfaceName::from_name(kernel_name.clone()))
                .into_name()
        })
        .collect();
    assert_eq!(
        metadata.constructor_names, expected,
        "{name}: constructor order"
    );
    for (index, ctor_name) in expected.iter().enumerate() {
        let ctor = spec
            .env()
            .get_constructor(ctor_name)
            .expect("constructor metadata");
        let constant = spec
            .env()
            .get_const(ctor_name)
            .expect("constructor constant");
        assert_eq!(ctor.inductive_name, kernel_name, "{ctor_name}: parent");
        assert_eq!(ctor.constructor_idx as usize, index, "{ctor_name}: index");
        assert_eq!(ctor.type_, constant.type_, "{ctor_name}: signature");
        assert_ne!(constant.kind, ConstantKind::Axiom, "{ctor_name}");
        let sort = checker
            .infer_type(&constant.type_)
            .expect("constructor type rechecks");
        assert!(matches!(sort.kind(), ExprKind::Sort(_)), "{ctor_name}");
        assert_empty_closures_typed(spec, ctor_name);
    }
    let rec_name = kernel_name.str("rec");
    let recursor = spec
        .env()
        .get_recursor(&rec_name)
        .expect("actual carrier recursor");
    let constant = spec.env().get_const(&rec_name).expect("recursor constant");
    assert_eq!(recursor.type_, constant.type_, "{rec_name}: signature");
    assert_ne!(constant.kind, ConstantKind::Axiom, "{rec_name}");
    let sort = checker
        .infer_type(&constant.type_)
        .expect("recursor type rechecks");
    assert!(matches!(sort.kind(), ExprKind::Sort(_)), "{rec_name}");
    assert_empty_closures_typed(spec, &rec_name);
}

fn assert_caller(spec: &Specification, value_source: &str, type_source: &str) {
    let value = spec
        .elaborate_source(value_source, "projection caller")
        .expect("caller elaborates");
    let expected = spec
        .elaborate_source(type_source, "projection caller type")
        .expect("caller type elaborates");
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let actual = checker.infer_type(&value).expect("actual caller checks");
    assert!(
        checker.is_def_eq(&actual, &expected),
        "{value_source}: actual endpoint"
    );
}

fn assert_computes(spec: &Specification, source: &str, expected_source: &str) {
    let value = spec
        .elaborate_source(source, "projection computation")
        .expect("computation elaborates");
    let expected = spec
        .elaborate_source(expected_source, "projection expected value")
        .expect("expected value elaborates");
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let value_type = checker.infer_type(&value).expect("computation type checks");
    let expected_type = checker
        .infer_type(&expected)
        .expect("expected value type checks");
    assert!(
        checker.is_def_eq(&value_type, &expected_type),
        "{source}: same value type"
    );
    assert!(
        checker.is_def_eq(&value, &expected),
        "{source}: actual transparent computation"
    );
}

#[test]
fn projection_reduction_records_parse_with_exact_partitions() {
    assert_eq!(PROOF_ROOTS.len(), 62);
    assert_eq!(DATA_NAMES.len(), 8);
    assert_eq!(INDUCTIVE_NAMES.len(), 3);
    assert_eq!(NEGATIVE_CONTROLS.len(), 10);
    let mut names = HashSet::new();
    let mut ordered = Vec::new();
    let mut proofs = Vec::new();
    let mut data = Vec::new();
    let mut carriers = Vec::new();
    for declaration in declarations() {
        let name = match declaration {
            DeclarationInput::Inductive(source) => {
                parse_check(source).expect("exact carrier declaration parses");
                let SurfaceDecl::Inductive {
                    name, ty, ctors, ..
                } = parse_decl(source).expect("carrier AST")
                else {
                    panic!("expected an inductive declaration")
                };
                assert!(!fragment(source, ty.span()).is_empty());
                let ctor_names: Vec<_> = ctors.iter().map(|ctor| ctor.name.clone()).collect();
                assert_eq!(
                    ctor_names,
                    expected_constructors(&name)
                        .iter()
                        .map(|n| clean_parser::parse_name(n).expect("explicit source name"))
                        .collect::<Vec<_>>()
                );
                carriers.push(name.qualify_under(&Default::default()).into_name());
                name.qualify_under(&Default::default()).into_name()
            }
            DeclarationInput::Proof(name, ty, body) => {
                check_tuple_ast(name, ty, body);
                proofs.push(*name);
                clean_parser::parse_name(name)
                    .expect("explicit source name")
                    .qualify_under(&Default::default())
                    .into_name()
            }
            DeclarationInput::Data(name, ty, body) => {
                check_tuple_ast(name, ty, body);
                data.push(*name);
                clean_parser::parse_name(name)
                    .expect("explicit source name")
                    .qualify_under(&Default::default())
                    .into_name()
            }
        };
        assert!(names.insert(name.clone()), "duplicate declaration {name}");
        ordered.push(name);
    }
    assert_eq!(ordered.len(), 73);
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
    for (index, name) in [
        (0, "projection_post_whnf_field"),
        (21, "projection_post_whnf_field_inv"),
        (34, "projection_post_whnf_universe_compat"),
        (42, "par_reduces_cdp"),
        (69, "projection_post_whnf_deterministic"),
    ] {
        assert_eq!(
            ordered[index],
            clean_parser::parse_name(name)
                .expect("explicit source name")
                .qualify_under(&Default::default())
                .into_name(),
            "five exact cohort boundaries"
        );
    }
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
fn projection_reduction_actual_records_recheck_with_empty_closures() {
    run_with_stack(|| {
        // Borrow the process-wide FULL_SPEC; this does not rebuild per test.
        let spec = shared_spec();
        for declaration in declarations() {
            let (name, ty_source, body_source, is_proof) = match declaration {
                DeclarationInput::Inductive(source) => {
                    check_carrier(spec, source);
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
                .elaborate_source(ty_source, "projection registration type")
                .expect("tuple type elaborates");
            let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
            assert!(
                checker.is_def_eq(ty, &expected),
                "{name}: tuple/actual type agreement"
            );
            spec.verify_definition(name)
                .expect("actual body checks against actual type");
            assert_empty_closures(spec, name);
        }
    });
}

#[test]
fn projection_reduction_computation_and_connected_callers_check() {
    run_with_stack(|| {
        let spec = shared_spec();
        // The raw selector requires constructor metadata and an existing
        // argument at num_params + index. These checks also pin the guards it
        // intentionally does NOT have; none is an admission claim.
        for (source, expected) in [
            ("projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_before)", "OptionType.some KExpr ctor_spine_prod_redex"),
            ("projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value)", "OptionType.some KExpr rfnz_zero"),
            ("projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name (Nat.succ Nat.zero) kcre_witness_prod_value)", "OptionType.some KExpr (KExpr.app rfnz_succ rfnz_zero)"),
            ("projection_post_whnf_reduct (RedEnv.mk RecEnv.empty DefEnv.empty IndCtorEnv.empty) (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value)", "OptionType.none KExpr"),
            ("projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name (Nat.succ (Nat.succ Nat.zero)) kcre_witness_prod_value)", "OptionType.none KExpr"),
            ("projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero ctor_spine_prod_redex)", "OptionType.none KExpr"),
            ("projection_post_whnf_reduct the_red_env (KExpr.proj Name.anonymous Nat.zero kcre_witness_prod_value)", "OptionType.some KExpr rfnz_zero"),
            ("projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero (apply_spine (kapp_args kcre_witness_prod_value) (KExpr.const kcre_prod_mk_name (ListType.cons Level Level.zero (ListType.nil Level)))))", "OptionType.some KExpr rfnz_zero"),
            ("projection_post_whnf_reduct projection_post_whnf_zero_fields_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value)", "OptionType.some KExpr rfnz_zero"),
            ("projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero projection_binding_subject)", "OptionType.some KExpr projection_binding_field"),
            ("instantiate_at projection_binding_field (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero", "KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))"),
            ("lift_at projection_binding_field Nat.zero (Nat.succ (Nat.succ Nat.zero))", "KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))"),
            ("projection_post_whnf_reduct the_red_env (instantiate_at (KExpr.proj kcre_prod_type_name Nat.zero projection_binding_subject) (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero)", "OptionType.some KExpr (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))"),
            ("projection_post_whnf_reduct the_red_env (lift_at (KExpr.proj kcre_prod_type_name Nat.zero projection_binding_subject) Nat.zero (Nat.succ (Nat.succ Nat.zero)))", "OptionType.some KExpr (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))"),
            ("projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero (projection_universe_subject (Level.imax (Level.succ (Level.param Name.anonymous)) Level.zero)))", "OptionType.some KExpr (KExpr.sort (Level.imax (Level.succ (Level.param Name.anonymous)) Level.zero))"),
            ("projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero (projection_universe_subject Level.zero))", "OptionType.some KExpr (KExpr.sort Level.zero)"),
            ("cdp_prod_inner_projection", "KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value"),
            ("projection_post_whnf_reduct the_red_env cdp_prod_inner_projection", "OptionType.some KExpr rfnz_zero"),
            ("projection_post_whnf_reduct the_red_env (KExpr.proj kcre_prod_type_name Nat.zero cdp_prod_outer_before)", "OptionType.some KExpr cdp_prod_inner_projection"),
        ] {
            assert_computes(spec, source, expected);
        }
        for subject in [
            "KExpr.sort Level.zero",
            "KExpr.bvar Nat.zero",
            "kcre_witness_prod_value",
            "KExpr.lam rfnz_nat (KExpr.bvar Nat.zero)",
            "KExpr.pi rfnz_nat rfnz_nat",
            "KExpr.const kcre_prod_mk_name (ListType.nil Level)",
            "KExpr.let_ rfnz_nat rfnz_zero (KExpr.bvar Nat.zero)",
            "KExpr.lit Nat.zero",
        ] {
            assert_computes(
                spec,
                &format!("projection_post_whnf_reduct the_red_env ({subject})"),
                "OptionType.none KExpr",
            );
        }
        for (value, ty) in [
            ("projection_post_whnf_prod_transport_zero", "par_reduces_cd the_red_env ctor_spine_prod_redex rfnz_zero"),
            ("projection_binding_substitution_caller", "Eq (OptionType KExpr) (projection_post_whnf_reduct the_red_env (instantiate_at (KExpr.proj kcre_prod_type_name Nat.zero projection_binding_subject) (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero)) (OptionType.some KExpr (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))))"),
            ("projection_binding_lifting_caller", "Eq (OptionType KExpr) (projection_post_whnf_reduct the_red_env (lift_at (KExpr.proj kcre_prod_type_name Nat.zero projection_binding_subject) Nat.zero (Nat.succ (Nat.succ Nat.zero)))) (OptionType.some KExpr (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))"),
            ("projection_universe_nonzero_caller", "KExprUniverseEq (KExpr.sort (Level.imax (Level.succ (Level.param Name.anonymous)) Level.zero)) (KExpr.sort Level.zero)"),
            ("projection_universe_not_syntactic (Level.succ (Level.param Name.anonymous))", "forall (same : Eq KExpr (KExpr.sort (Level.imax (Level.succ (Level.param Name.anonymous)) Level.zero)) (KExpr.sort Level.zero)), Empty"),
            ("cdp_prod_inner_step", "par_reduces_cdp the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) rfnz_zero"),
            ("cdp_prod_outer_step", "par_reduces_cdp the_red_env cdp_prod_outer_before kcre_witness_prod_value"),
            ("cdp_prod_selected_zero", "par_reduces_cdp the_red_env cdp_prod_inner_projection rfnz_zero"),
            ("cdp_prod_selector_transport", "par_reduces_cdp the_red_env cdp_prod_inner_projection rfnz_zero"),
            ("cdp_prod_head_preserved", "Eq KExpr (kapp_fn kcre_witness_prod_value) (kapp_fn cdp_prod_outer_before)"),
            ("cdp_prod_length_preserved", "Eq Nat (list_length (kapp_args cdp_prod_outer_before)) (list_length (kapp_args kcre_witness_prod_value))"),
            ("cdp_prod_old_beta_embedded", "par_reduces_cdp the_red_env ctor_spine_prod_redex rfnz_zero"),
            ("par_reduces_cd_to_cdp the_red_env ctor_spine_prod_before kcre_witness_prod_value ctor_spine_prod_step", "par_reduces_cdp the_red_env ctor_spine_prod_before kcre_witness_prod_value"),
            ("projection_post_whnf_deterministic the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) rfnz_zero rfnz_zero projection_post_whnf_prod_after_zero projection_post_whnf_prod_after_zero", "Eq KExpr rfnz_zero rfnz_zero"),
            ("par_cdp_projection_beta_beta the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) rfnz_zero rfnz_zero projection_post_whnf_prod_after_zero projection_post_whnf_prod_after_zero", "forall (C : Type) (next : forall (v : KExpr), par_reduces_cdp the_red_env rfnz_zero v -> par_reduces_cdp the_red_env rfnz_zero v -> C), C"),
            ("par_cdp_projection_beta_cong the_red_env reflected_ctor_metadata_rigid kcre_prod_type_name Nat.zero cdp_prod_outer_before kcre_witness_prod_value cdp_prod_outer_step cdp_prod_inner_projection cdp_prod_outer_extract", "forall (C : Type) (next : forall (b : KExpr), par_reduces_cdp the_red_env cdp_prod_inner_projection b -> par_reduces_cdp the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) b -> C), C"),
            ("par_cdp_prod_beta_projection_join", "forall (C : Type) (next : forall (b : KExpr), par_reduces_cdp the_red_env ctor_spine_prod_redex b -> par_reduces_cdp the_red_env (KExpr.proj kcre_prod_type_name Nat.zero kcre_witness_prod_value) b -> C), C"),
        ] {
            assert_caller(spec, value, ty);
        }
        let left = spec
            .elaborate_source(
                "KExpr.sort (Level.imax (Level.succ (Level.param Name.anonymous)) Level.zero)",
                "raw imax syntax",
            )
            .expect("raw imax fixture elaborates");
        let right = spec
            .elaborate_source("KExpr.sort Level.zero", "raw zero syntax")
            .expect("raw zero fixture elaborates");
        let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
        assert!(
            !checker.is_def_eq(&left, &right),
            "semantic universe compatibility must not erase raw Level constructors"
        );
    });
}

#[test]
fn projection_reduction_refuses_ten_forged_proofs_without_registration() {
    run_with_stack(|| {
        // Only this clone is mutated; every runtime test uses the same FULL_SPEC.
        let mut spec = shared_spec().clone();
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
                "Reject forged selection, binding, universe, new-step endpoint or join evidence.",
            )
            .expect_err("well-parsed forged evidence must fail actual type checking");
            let diagnostic = format!("{error:?}").to_ascii_lowercase();
            // The last forged continuation is an application type mismatch.
            // Parsing or missing-name errors do not count as proof refusal.
            assert!(diagnostic.contains("type mismatch"), "{name}: {error:?}");
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
