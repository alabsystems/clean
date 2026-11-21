// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual Full-spec values and paired freshness claims; setup failure fails the test.

use super::PROOFS;
use crate::spec::Specification;
use crate::test_utils::{assert_type_mismatch_rejection, build_spec_with_stack, run_with_stack};
use clean_elab::ElabCtx;
use clean_kernel::{
    ConstantKind, DeclarationVerification, Expr, ExprKind, Name, TypeChecker, TypeError,
};
use std::collections::HashSet;

const CLOSEDNESS_IOTA_ROOTS: [&str; 15] = [
    "is_closed_at_lam_body",
    "is_closed_at_pi_body",
    "is_closed_at_let_ty",
    "is_closed_at_let_val",
    "is_closed_at_let_body",
    "instantiate_preserves_closed",
    "is_closed_at_proj_sub",
    "list_take_preserves_closed",
    "kapp_args_closed",
    "list_head_closed",
    "opt_bind_some_inv_T",
    "iota_reduct_some_inv_T",
    "delta_reduct_some_inv_T",
    "hdelta_generic",
    "infer_result_self_admissible",
];

struct CollisionPair {
    good_name: &'static str,
    bad_name: &'static str,
    good_source: &'static str,
    bad_source: &'static str,
    false_root: &'static str,
    claim_site: ClaimSite,
}

#[derive(Clone, Copy)]
enum ClaimSite {
    Target,
    // Exact written data/premise prefix in these fixed authored fixtures.
    // This is not application-arity or recursor-role inference.
    NextArgumentAfter(usize),
}

const PAIRS: [CollisionPair; 7] = [
    CollisionPair {
        good_name: "audit_collision_good_existing_ctor",
        bad_name: "audit_collision_bad_existing_ctor",
        good_source: include_str!("../../../spec/fixtures/env_freshness/existing_ctor_good.clean"),
        bad_source: include_str!("../../../spec/fixtures/env_freshness/existing_ctor_bad.clean"),
        false_root: "env_freshness_existing_ctor_refused",
        claim_site: ClaimSite::Target,
    },
    CollisionPair {
        good_name: "audit_collision_good_self_family",
        bad_name: "audit_collision_bad_self_family",
        good_source: include_str!("../../../spec/fixtures/env_freshness/self_family_good.clean"),
        bad_source: include_str!("../../../spec/fixtures/env_freshness/self_family_bad.clean"),
        false_root: "env_freshness_self_family_refused",
        claim_site: ClaimSite::Target,
    },
    CollisionPair {
        good_name: "audit_collision_good_duplicate",
        bad_name: "audit_collision_bad_duplicate",
        good_source: include_str!("../../../spec/fixtures/env_freshness/duplicate_good.clean"),
        bad_source: include_str!("../../../spec/fixtures/env_freshness/duplicate_bad.clean"),
        false_root: "env_freshness_intra_list_refused",
        claim_site: ClaimSite::Target,
    },
    CollisionPair {
        good_name: "audit_collision_good_family",
        bad_name: "audit_collision_bad_family",
        good_source: include_str!("../../../spec/fixtures/env_freshness/family_good.clean"),
        bad_source: include_str!("../../../spec/fixtures/env_freshness/family_bad.clean"),
        false_root: "env_freshness_stored_ctor_refused",
        claim_site: ClaimSite::Target,
    },
    CollisionPair {
        good_name: "audit_collision_good_inductive",
        bad_name: "audit_collision_bad_inductive",
        good_source: include_str!("../../../spec/fixtures/env_freshness/inductive_good.clean"),
        bad_source: include_str!("../../../spec/fixtures/env_freshness/inductive_bad.clean"),
        false_root: "env_freshness_existing_ctor_refused",
        claim_site: ClaimSite::NextArgumentAfter(4),
    },
    CollisionPair {
        good_name: "audit_collision_good_reducible",
        bad_name: "audit_collision_bad_reducible",
        good_source: include_str!("../../../spec/fixtures/env_freshness/reducible_good.clean"),
        bad_source: include_str!("../../../spec/fixtures/env_freshness/reducible_bad.clean"),
        false_root: "env_freshness_stored_ctor_refused",
        claim_site: ClaimSite::NextArgumentAfter(6),
    },
    CollisionPair {
        good_name: "audit_collision_good_opaque",
        bad_name: "audit_collision_bad_opaque",
        good_source: include_str!("../../../spec/fixtures/env_freshness/opaque_good.clean"),
        bad_source: include_str!("../../../spec/fixtures/env_freshness/opaque_bad.clean"),
        false_root: "env_freshness_stored_ctor_refused",
        claim_site: ClaimSite::NextArgumentAfter(6),
    },
];

fn require_sort(tc: &TypeChecker<'_>, type_: &Expr, name: &str) {
    let sort = tc
        .infer_type_full(type_)
        .unwrap_or_else(|error| panic!("{name}: declared type must fully check: {error:?}"));
    assert!(
        matches!(tc.whnf(&sort).kind(), ExprKind::Sort(_)),
        "{name}: declared type must inhabit a sort"
    );
    assert!(!tc.heartbeat_spent(), "{name}: type checking must finish");
}

fn checked_value<'a>(spec: &'a Specification, name: &str) -> (&'a Expr, &'a Expr) {
    let definition = spec
        .get_definition(name)
        .unwrap_or_else(|| panic!("{name}: actual source record is required"));
    let kernel_name = Name::from_string(name);
    let constant = spec
        .env()
        .get_const(&kernel_name)
        .unwrap_or_else(|| panic!("{name}: actual kernel root is required"));
    let type_ = definition
        .elaborated_type
        .as_ref()
        .unwrap_or_else(|| panic!("{name}: actual checked type is required"));
    let value = definition
        .elaborated_value
        .as_ref()
        .unwrap_or_else(|| panic!("{name}: actual checked value is required"));
    assert!(!definition.is_axiom, "{name}");
    assert!(
        definition.value_src.is_some(),
        "{name}: source value is required"
    );
    assert_ne!(constant.kind, ConstantKind::Axiom, "{name}");
    assert_eq!(&constant.type_, type_, "{name}");
    assert_eq!(constant.value.as_ref(), Some(value), "{name}");
    assert!(
        !matches!(value.kind(), ExprKind::Const(n, _) if n == &kernel_name),
        "{name}: the proof must not be its own constant"
    );
    assert_eq!(
        spec.env().declaration_verification(&kernel_name),
        Some(DeclarationVerification::FullKernelCheck),
        "{name}: actual checked provenance is required"
    );
    let tc = TypeChecker::with_mode(spec.env(), spec.env().mode());
    require_sort(&tc, type_, name);
    tc.check_type(value, type_)
        .unwrap_or_else(|error| panic!("{name}: actual value must fully check: {error:?}"));
    assert!(!tc.heartbeat_spent(), "{name}: value checking must finish");
    spec.verify_definition(name)
        .unwrap_or_else(|error| panic!("{name}: original replay must succeed: {error:?}"));
    assert!(
        spec.env()
            .axiom_deps(&kernel_name)
            .expect("domain closure")
            .is_empty(),
        "{name}"
    );
    assert!(
        spec.env()
            .foundational_axiom_deps(&kernel_name)
            .expect("foundational closure")
            .is_empty(),
        "{name}"
    );
    assert!(
        crate::spec_axiom_closure::computed_axiom_closure(spec, name).is_empty(),
        "{name}"
    );
    (type_, value)
}

fn parsed_name(source: &str, expected: &str) -> Name {
    let clean_parser::SurfaceDecl::Def { name, .. } =
        clean_parser::parse_decl(source).expect("paired source must parse")
    else {
        panic!("paired source must be a definition");
    };
    let name = name.qualify_under(&Default::default()).into_name();
    assert_eq!(
        name,
        Name::from_string(expected),
        "exact paired fixture name"
    );
    name
}

fn absent(spec: &Specification, name: &Name, record_name: &str) {
    assert!(
        spec.get_definition(record_name).is_none(),
        "{record_name}: record must be absent"
    );
    assert!(
        spec.env().get_const(name).is_none(),
        "{record_name}: kernel name must be absent"
    );
}

fn elaborate_closed(
    spec: &Specification,
    surface: &clean_parser::SurfaceExpr,
    label: &str,
) -> Expr {
    let mut context = ElabCtx::new(spec.env());
    let term = context
        .elaborate(surface)
        .unwrap_or_else(|error| panic!("{label}: independent setup must elaborate: {error:?}"));
    let term = context.metas().instantiate(&term);
    let term = context.metas().instantiate_levels(&term);
    assert!(!term.has_fvar_quick(), "{label}: unexpected free variable");
    assert!(
        !term.has_expr_mvar_quick(),
        "{label}: unresolved expression meta"
    );
    assert!(
        !term.has_level_mvar_quick(),
        "{label}: unresolved universe meta"
    );
    term
}

fn authored_bad_claim(spec: &Specification, pair: &CollisionPair) -> (Expr, Expr) {
    let clean_parser::SurfaceDecl::Def {
        ty, val, binders, ..
    } = clean_parser::parse_decl(pair.bad_source).expect("actual bad companion parses")
    else {
        panic!("bad companion must be a definition");
    };
    assert!(
        binders.is_empty(),
        "fixed companions have no local telescope"
    );
    let target = elaborate_closed(spec, ty.as_ref().expect("written target"), pair.bad_name);
    let tc = TypeChecker::with_mode(spec.env(), spec.env().mode());
    require_sort(&tc, &target, pair.bad_name);
    match pair.claim_site {
        ClaimSite::Target => (target, elaborate_closed(spec, &val, pair.bad_name)),
        ClaimSite::NextArgumentAfter(prefix_count) => {
            let clean_parser::SurfaceExpr::App(span, head, arguments) = val.as_ref() else {
                panic!(
                    "{}: actual constructor/helper application is required",
                    pair.bad_name
                );
            };
            assert!(
                arguments.len() > prefix_count,
                "{}: written premise",
                pair.bad_name
            );
            assert!(
                arguments.iter().all(|arg| arg.name.is_none()),
                "fixed positional fixture"
            );
            let prefix = clean_parser::SurfaceExpr::App(
                *span,
                head.clone(),
                arguments[..prefix_count].to_vec(),
            );
            let prefix = elaborate_closed(spec, &prefix, pair.bad_name);
            let prefix_type = tc.infer_type_full(&prefix).unwrap_or_else(|error| {
                panic!(
                    "{}: actual preceding fields must fully check: {error:?}",
                    pair.bad_name
                )
            });
            let prefix_type = tc.whnf(&prefix_type);
            let ExprKind::Pi(_, claim, _) = prefix_type.kind() else {
                panic!("{}: actual next premise must be a Pi domain", pair.bad_name);
            };
            let proof = elaborate_closed(spec, &arguments[prefix_count].expr, pair.bad_name);
            (claim.as_ref().clone(), proof)
        }
    }
}

fn require_type_mismatch(tc: &TypeChecker<'_>, proof: &Expr, claim: &Expr, name: &str) {
    require_sort(tc, claim, name);
    let _checked_candidate_type = tc
        .infer_type_full(proof)
        .unwrap_or_else(|error| panic!("{name}: candidate itself must fully check: {error:?}"));
    let error = tc
        .check_type(proof, claim)
        .expect_err("the actual changed claim must not check");
    assert!(
        matches!(error, TypeError::TypeMismatch { .. }),
        "{name}: {error:?}"
    );
    assert!(
        !tc.heartbeat_spent(),
        "{name}: refusal must not be a resource abort"
    );
}

fn reject_true_endpoint(spec: &Specification, pair: &CollisionPair) {
    let root = pair.false_root;
    let (false_type, false_proof) = checked_value(spec, root);
    assert!(
        matches!(false_type.get_app_fn().kind(), ExprKind::Const(n, _) if n == &Name::from_string("Eq")),
        "{root}: the actual false computation must be an Eq"
    );
    let arguments = false_type.get_app_args();
    assert_eq!(arguments.len(), 3, "{root}: actual Eq carrier/endpoints");
    assert_eq!(arguments[0], &Expr::const_str("Bool"), "{root}");
    assert_eq!(arguments[2], &Expr::const_str("Bool.false"), "{root}");
    // Preserve the actual predicate and Eq universe instance; change one claim.
    let true_type = Expr::apps(
        false_type.get_app_fn().clone(),
        [
            (*arguments[0]).clone(),
            (*arguments[1]).clone(),
            Expr::const_str("Bool.true"),
        ],
    );
    let tc = TypeChecker::with_mode(spec.env(), spec.env().mode());
    require_type_mismatch(&tc, false_proof, &true_type, root);
    let (actual_claim, candidate) = authored_bad_claim(spec, pair);
    assert!(
        tc.is_def_eq(&actual_claim, &true_type),
        "{}: actual written obligation must be the anchored false predicate claimed true",
        pair.bad_name
    );
    // Check the actual written argument against its actual inferred premise,
    // independently of the source-level refusal's diagnostic text.
    require_type_mismatch(&tc, &candidate, &actual_claim, pair.bad_name);
}

#[test]
fn selected_closedness_iota_values_recheck_strictly_without_axioms() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let mut checked = HashSet::new();
        for name in CLOSEDNESS_IOTA_ROOTS {
            assert!(
                checked.insert(name),
                "duplicate direct replay target: {name}"
            );
            checked_value(&spec, name);
        }
        assert_eq!(
            checked.len(),
            15,
            "all selected values must actually recheck"
        );
    });
}

#[test]
fn collision_pairs_require_valid_setup_and_checked_refusals() {
    run_with_stack(|| {
        let base = build_spec_with_stack();
        assert_eq!(PROOFS.len(), 39, "original named setup roots");
        for &(name, type_src, value_src) in PROOFS {
            let record = base.get_definition(name).expect("original setup root");
            assert_eq!(record.type_src, type_src, "{name}");
            assert_eq!(record.value_src.as_deref(), Some(value_src), "{name}");
            checked_value(&base, name);
        }
        checked_value(&base, "well_formed_ctor_decls_nonvacuity_witness");
        let mut checked = HashSet::new();
        for pair in PAIRS {
            assert!(checked.insert(pair.good_name), "duplicate pair");
            let mut spec = base.clone();
            let good_name = parsed_name(pair.good_source, pair.good_name);
            let bad_name = parsed_name(pair.bad_source, pair.bad_name);
            absent(&spec, &good_name, pair.good_name);
            absent(&spec, &bad_name, pair.bad_name);
            spec.add_recursive_def(pair.good_source, "Valid freshness companion")
                .unwrap_or_else(|error| {
                    panic!(
                        "{}: positive setup must be admitted: {error:?}",
                        pair.good_name
                    )
                });
            let good = spec
                .get_definition(pair.good_name)
                .expect("admitted positive companion");
            assert_eq!(good.type_src, pair.good_source, "{}", pair.good_name);
            assert_eq!(
                good.value_src.as_deref(),
                Some(pair.good_source),
                "{}",
                pair.good_name
            );
            checked_value(&spec, pair.good_name);
            reject_true_endpoint(&spec, &pair);
            let error = spec
                .add_recursive_def(pair.bad_source, "Changed collision claim")
                .expect_err("the changed collision claim must be refused after valid setup");
            assert_type_mismatch_rejection(&error, pair.bad_name);
            absent(&spec, &bad_name, pair.bad_name);
            // Refusal must leave the actual positive and original anchor usable.
            checked_value(&spec, pair.good_name);
            checked_value(&spec, pair.false_root);
        }
        assert_eq!(
            checked.len(),
            7,
            "all seven companions must be admitted and checked"
        );
    });
}
