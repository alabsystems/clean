// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual registration and finite model-history callers, not Rust admission
//! refinement or strict-time/final-record correspondence.

use super::{
    declarations, DeclarationInput, DATA_NAMES, INDUCTIVE_NAMES, NEGATIVE_CONTROLS, PROOF_ROOTS,
    PROP_PROOF_ROOTS, TYPE_PROOF_ROOTS,
};
use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::{SpecError, Specification};
use crate::test_utils::{parse_check, run_with_stack, shared_spec};
use clean_kernel::{ConstantKind, Expr, ExprKind, Level, Name, TypeChecker};
use clean_parser::{parse_decl, parse_expr, Span, SurfaceDecl};
use std::collections::HashSet;

const EXPECTED_PROOFS: &[&str] = &[
    "sfa_const_entries",
    "sfa_inductive_entries",
    "sfa_extension_entries",
    "sfa_sound_entries",
    "sfa_entries_at",
    "sfa_stored_family_admission",
    "sfa_prior_family_caller",
    "sfa_constant_tail_caller",
];

const ADMISSION_TYPE: &str = r"forall (env : KEnv) (depth : Nat) (prior : KEnv)
 (family np : Nat) (ty : KExpr) (ctors : CtorDecls),
 EnvSound env -> @Eq (OptionType KEnv) (sfa_entry_at env depth)
  (@OptionType.some KEnv (KEnv.addInductive prior family np ty ctors)) ->
 InductiveExtension prior (KEnv.addInductive prior family np ty ctors)";

// Independent concrete applications of the generic theorem. Neither supplies an
// InductiveExtension result as an input; both traverse a genuine newer node.
const CALLERS: &[(&str, &str)] = &[
    (
        "sfa_prior_family_caller",
        r"sfa_stored_family_admission env_freshness_second env_freshness_one KEnv.empty Nat.zero Nat.zero
 env_freshness_type (env_freshness_ctors env_freshness_one) env_freshness_acceptance_preserves_sound
 (@Eq.refl (OptionType KEnv) (@OptionType.some KEnv env_freshness_first))",
    ),
    (
        "sfa_constant_tail_caller",
        r"sfa_stored_family_admission env_freshness_const_result env_freshness_one KEnv.empty Nat.zero Nat.zero
 env_freshness_type (env_freshness_ctors env_freshness_one) env_freshness_const_preserves_sound
 (@Eq.refl (OptionType KEnv) (@OptionType.some KEnv env_freshness_first))",
    ),
];

fn tuple(input: &DeclarationInput) -> (&str, &str, &str, bool) {
    match input {
        DeclarationInput::Data(name, ty, body) => (name, ty, body, false),
        DeclarationInput::Proof(name, ty, body) => (name, ty, body, true),
    }
}

fn fragment(source: &str, span: Span) -> Vec<&str> {
    source[span.start..span.end].split_whitespace().collect()
}

fn tuple_ast(name: &str, ty: &str, body: &str) {
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
    assert!(binders.is_empty(), "{name}: tuple owns its entire type");
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
    assert_ne!(name, body.trim(), "{name}: no self-constant body");
}

fn elaborate(spec: &Specification, source: &str) -> Expr {
    spec.elaborate_source(source, "stored family admission test")
        .expect("source elaborates independently")
}

fn assert_sort(spec: &Specification, ty: &Expr, expected_level: Level) {
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let sort = checker.infer_type_full(ty).expect("actual statement sort");
    let ExprKind::Sort(actual_level) = sort.kind() else {
        panic!("statement must have a sort")
    };
    assert!(
        Level::is_def_eq(actual_level, &expected_level),
        "actual universe level, not merely non-Prop: {sort:?}"
    );
}

fn empty_closures(spec: &Specification, name: &str) {
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

fn record(spec: &Specification, input: &DeclarationInput) {
    let (name, ty_source, body_source, is_proof) = tuple(input);
    let record = spec.definitions().get(name).expect("actual record");
    let root = Name::from_string(name);
    let constant = spec.env().get_const(&root).expect("actual kernel root");
    let ty = record.elaborated_type.as_ref().expect("checked type");
    let body = record.elaborated_value.as_ref().expect("checked body");
    assert!(!record.is_axiom, "{name}");
    assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
    assert_eq!(record.category, AxiomCategory::DerivedLemma, "{name}");
    if is_proof {
        assert_eq!(record.proof_status, ProofStatus::DerivedProved, "{name}");
        assert_eq!(
            constant.kind,
            ConstantKind::Opaque,
            "{name}: Type-valued proof"
        );
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
            "{name}: data"
        );
        assert_eq!(
            constant.kind,
            ConstantKind::Definition,
            "{name}: transparent data"
        );
        let source = format!("def {name} : {ty_source} := {body_source}");
        assert_eq!(
            record.type_src, source,
            "{name}: recursive registration source"
        );
        assert_eq!(record.value_src.as_deref(), Some(source.as_str()));
    }
    assert_eq!(&constant.type_, ty, "{name}: kernel/record type");
    assert_eq!(
        constant.value.as_ref(),
        Some(body),
        "{name}: kernel/record body"
    );
    assert!(!matches!(body.kind(), ExprKind::Const(n, _) if n == &root));
    let expected = elaborate(spec, ty_source);
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    assert!(
        checker.is_def_eq(ty, &expected),
        "{name}: exact statement contract"
    );
    let body_type = checker
        .infer_type_full(body)
        .expect("stored body fully kernel-checks");
    assert!(
        checker.is_def_eq(&body_type, ty),
        "{name}: actual body type"
    );
    let level_one = Level::succ(Level::zero());
    assert_sort(
        spec,
        ty,
        if name == "sfa_entries" {
            Level::succ(level_one)
        } else {
            level_one
        },
    );
    spec.verify_definition(name)
        .expect("stored body rechecks against stored type");
    empty_closures(spec, name);
}

fn caller(spec: &Specification, source: &str, expected_source: &str) {
    let value = elaborate(spec, source);
    let expected = elaborate(spec, expected_source);
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let expected_sort = checker
        .infer_type_full(&expected)
        .expect("caller type kernel-checks");
    assert!(matches!(expected_sort.kind(), ExprKind::Sort(_)));
    let actual = checker
        .infer_type_full(&value)
        .expect("caller arguments kernel-check");
    assert!(
        checker.is_def_eq(&actual, &expected),
        "{source}: actual caller type"
    );
}

fn computes(spec: &Specification, source: &str, expected_source: &str) {
    let value = elaborate(spec, source);
    let expected = elaborate(spec, expected_source);
    let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let actual_type = checker
        .infer_type_full(&value)
        .expect("computation kernel-checks");
    let expected_type = checker
        .infer_type_full(&expected)
        .expect("endpoint kernel-checks");
    assert!(
        checker.is_def_eq(&actual_type, &expected_type),
        "{source}: same object type"
    );
    assert!(
        checker.is_def_eq(&value, &expected),
        "{source}: actual computation"
    );
}

#[test]
fn stored_family_admission_exact_partitions_parse() {
    assert_eq!(PROOF_ROOTS, EXPECTED_PROOFS);
    assert_eq!(TYPE_PROOF_ROOTS, EXPECTED_PROOFS);
    assert_eq!(DATA_NAMES, &["sfa_entry_at", "sfa_entries"]);
    assert!(PROP_PROOF_ROOTS.is_empty());
    assert!(INDUCTIVE_NAMES.is_empty());
    let mut names = HashSet::new();
    let (mut data, mut proofs, mut ordered) = (Vec::new(), Vec::new(), Vec::new());
    for input in declarations() {
        let (name, ty, body, is_proof) = tuple(input);
        assert!(names.insert(name), "unique live name {name}");
        tuple_ast(name, ty, body);
        ordered.push(name);
        if is_proof {
            proofs.push(name);
        } else {
            data.push(name);
        }
    }
    assert_eq!(data, DATA_NAMES);
    assert_eq!(proofs, EXPECTED_PROOFS);
    assert_eq!(
        ordered,
        DATA_NAMES
            .iter()
            .chain(EXPECTED_PROOFS)
            .copied()
            .collect::<Vec<_>>()
    );
    let mut negatives = Vec::new();
    for &(name, ty, body) in NEGATIVE_CONTROLS {
        assert!(
            names.insert(name),
            "negative disjoint from all live/failed names"
        );
        tuple_ast(name, ty, body);
        negatives.push(name);
    }
    assert_eq!(
        negatives,
        [
            "sfa_false_changed_former",
            "sfa_false_changed_parameters",
            "sfa_false_shortened_constructors",
            "sfa_false_wrong_position",
        ]
    );
    assert_eq!(names.len(), 14);
}

#[test]
fn stored_family_admission_actual_records_recheck() {
    run_with_stack(|| {
        let spec = shared_spec();
        let mut count = 0;
        for input in declarations() {
            record(spec, input);
            count += 1;
        }
        assert_eq!(count, 10);
    });
}

#[test]
fn stored_family_admission_computed_history_slots() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (source, expected) in [
            ("sfa_entry_at env_freshness_second Nat.zero", "@OptionType.some KEnv env_freshness_second"),
            ("sfa_entry_at env_freshness_second env_freshness_one", "@OptionType.some KEnv env_freshness_first"),
            ("sfa_entry_at env_freshness_second env_freshness_two", "@OptionType.none KEnv"),
            ("sfa_entry_at env_freshness_const_result Nat.zero", "@OptionType.some KEnv env_freshness_const_result"),
            ("sfa_entry_at env_freshness_const_result env_freshness_one", "@OptionType.some KEnv env_freshness_first"),
            ("sfa_entry_at KEnv.empty Nat.zero", "@OptionType.none KEnv"),
            ("sfa_entry_at KEnv.empty env_freshness_one", "@OptionType.none KEnv"),
            ("sfa_entries KEnv.empty", "Nat"),
            ("sfa_entries env_freshness_first", "ProdType Nat (InductiveExtension KEnv.empty env_freshness_first)"),
            ("sfa_entries env_freshness_second", "ProdType (sfa_entries env_freshness_first) (InductiveExtension env_freshness_first env_freshness_second)"),
            ("sfa_entries env_freshness_const_result", "ProdType (sfa_entries env_freshness_first) (ConstantExtension env_freshness_first env_freshness_const_result)"),
        ] {
            computes(spec, source, expected);
        }
    });
}

#[test]
fn stored_family_admission_prior_and_constant_tail_callers() {
    run_with_stack(|| {
        let spec = shared_spec();
        caller(spec, "sfa_stored_family_admission", ADMISSION_TYPE);
        let expected_type = "InductiveExtension KEnv.empty env_freshness_first";
        for &(name, body) in CALLERS {
            let input = declarations()
                .find(|input| tuple(input).0 == name)
                .expect("frozen caller tuple");
            let (_, ty, actual_body, is_proof) = tuple(input);
            assert!(is_proof);
            assert_eq!(ty, expected_type);
            assert_eq!(actual_body, body, "{name}: exact independent application");
            caller(spec, body, expected_type);
            caller(spec, name, expected_type);
        }
    });
}

fn assert_absent(spec: &Specification, name: &str) {
    assert!(!spec.definitions().contains_key(name), "no record {name}");
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_none(),
        "no kernel root {name}"
    );
}

fn owned_type_mismatch(name: &str, error: SpecError) {
    // Each target and body was independently elaborated first. The owned kernel
    // add_decl mismatch, not a parser/elaborator/budget refusal, is the control.
    let SpecError::TypeError(message) = error else {
        panic!("{name}: expected owned kernel type mismatch, got {error:?}")
    };
    assert!(
        message.starts_with(&format!("add_decl {name}:")),
        "{message}"
    );
    let lower = message.to_ascii_lowercase();
    assert!(lower.contains("type mismatch"), "{name}: {message}");
    for unrelated in [
        "unknown identifier",
        "unknown constant",
        "unknown definition",
        "unresolved metavariable",
    ] {
        assert!(
            !lower.contains(unrelated),
            "{name}: unrelated refusal: {message}"
        );
    }
}

#[test]
fn stored_family_admission_four_forged_lookups_are_not_registered() {
    run_with_stack(|| {
        let mut spec = shared_spec().clone();
        let before = spec.definitions().len();
        let mut count = 0;
        for &(name, ty_source, body_source) in NEGATIVE_CONTROLS {
            assert_absent(&spec, name);
            let ty = elaborate(&spec, ty_source);
            assert_sort(&spec, &ty, Level::zero());
            let body = elaborate(&spec, body_source);
            {
                let checker = TypeChecker::with_mode(spec.env(), spec.env().mode());
                let inferred = checker
                    .infer_type_full(&body)
                    .expect("forged body itself kernel-checks");
                assert_sort(&spec, &inferred, Level::zero());
                assert!(
                    !checker.is_def_eq(&inferred, &ty),
                    "{name}: genuinely wrong target"
                );
            }
            let error = super::theorem(
                &mut spec,
                name,
                ty_source,
                body_source,
                "Forged exact-history lookup; actual owned body type mismatch required",
            )
            .expect_err("wrong proof body must be refused");
            owned_type_mismatch(name, error);
            assert_absent(&spec, name);
            assert_eq!(spec.definitions().len(), before);
            count += 1;
        }
        assert_eq!(count, 4);
    });
}

#[test]
fn stored_family_admission_original_extension_judgments_unchanged() {
    run_with_stack(|| {
        let spec = shared_spec();
        for (carrier, ctors) in [
            ("KEnv", &["empty", "addConst", "addInductive"][..]),
            ("ConstantExtension", &["mk"][..]),
            ("InductiveExtension", &["mk"][..]),
            (
                "KernelAddDeclAccepts",
                &["const_case", "inductive_case"][..],
            ),
            ("KernelAddDeclChain", &["refl", "step"][..]),
        ] {
            let root = Name::from_string(carrier);
            let metadata = spec
                .env()
                .get_inductive(&root)
                .expect("existing judgment metadata");
            let expected = ctors
                .iter()
                .map(|ctor| Name::from_string(&format!("{carrier}.{ctor}")))
                .collect::<Vec<_>>();
            assert_eq!(
                metadata.constructor_names, expected,
                "{carrier}: no reuse constructor or migration"
            );
            let family_type = if carrier == "KEnv" {
                "Type"
            } else {
                "KEnv -> KEnv -> Type"
            };
            caller(spec, carrier, family_type);
        }
    });
}
