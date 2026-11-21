// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicit semantic controls alongside the unchanged historical R17 probes.

use super::super::*;
use crate::spec::{SpecError, Specification};
use crate::test_utils::assert_type_mismatch_rejection;
use clean_kernel::env::{DeclarationVerification, DomainAxiomClosure};
use clean_kernel::{BinderInfo, Expr, ExprKind, Level, Name, TypeChecker, TypeError};
use serde_json::json;

struct Case {
    label: &'static str,
    original_name: &'static str,
    original: String,
    explicit: String,
    explicit_name: String,
    positive_name: String,
    positive: String,
}

fn case(
    label: &'static str,
    original_name: &'static str,
    original: String,
    ty: String,
    value: String,
) -> Case {
    // The R17 probes are now written in the explicit `@head` spelling: main's
    // class-73 respelling (eb030b9194) marked them in source. The historical
    // positional spelling is rebuilt here by unmarking exactly the constructor
    // heads whose uniform parameters are written. The pre-existing
    // @ListType.nil in DEADCONST is marked in every era, so it stays marked.
    assert!(original.contains("@Eq.refl "), "{original}");
    assert!(!original.contains("@@"));
    let deadconst_unmarked = DEADCONST.replace("(@ListType.nil Level)", "(ListType.nil Level)");
    let historical = original
        .replace("@Eq.refl ", "Eq.refl ")
        .replace("@Eq (", "Eq (")
        .replace("(@ListType.nil Level)", "(ListType.nil Level)")
        .replace("(@OptionType.none KExpr)", "(OptionType.none KExpr)")
        .replace("(@OptionType.none RecMeta)", "(OptionType.none RecMeta)")
        .replace(&deadconst_unmarked, DEADCONST);
    assert_eq!(historical.matches("@Eq.refl").count(), 0);
    assert_ne!(historical, original, "the historical spelling must differ");
    let explicit_name = format!("{original_name}_explicit");
    let explicit = original.replacen(
        &format!("def {original_name} :"),
        &format!("def {explicit_name} :"),
        1,
    );
    assert!(explicit.starts_with(&format!("def {explicit_name} :")));
    let positive_name = format!("r17_semantic_{label}_positive");
    let positive = format!("def {positive_name} : {ty} := {value}");
    Case {
        label,
        original_name,
        original: historical,
        explicit,
        explicit_name,
        positive_name,
        positive,
    }
}

fn cases() -> Vec<Case> {
    vec![
        case(
            "irrel",
            "r17_irrel_refl_probe",
            probe_irrel_refl(),
            ty_irrel_witness(),
            val_irrel_witness(),
        ),
        case(
            "zeta",
            "r17_zeta_junk_probe",
            probe_zeta_junk(),
            ty_zeta_reads_value(),
            val_zeta_reads_value(),
        ),
        case(
            "shape",
            "r17_konst_wrong_shape_probe",
            probe_konst_wrong_shape(),
            format!("WKC r12_piEnv {DEADCONST} Sk.ty"),
            src_konst_witness()
                .split_once(":=")
                .expect("canonical konst witness body")
                .1
                .trim()
                .to_owned(),
        ),
        case(
            "inertness",
            "r17_konst_delta_active_probe",
            probe_konst_delta_active(),
            ty_unrestricted_konst_refuted(),
            val_unrestricted_konst_refuted(),
        ),
    ]
}

fn closed(expr: &Expr) {
    assert!(!expr.has_fvar_quick());
    assert!(!expr.has_expr_mvar_quick());
    assert!(!expr.has_level_mvar_quick());
    assert!(!expr.has_loose_bvars());
}

fn full_positive(spec: &Specification, spelling: &str) {
    let name = Name::from_string(spelling);
    let info = spec
        .env()
        .get_const(&name)
        .expect("actual registered positive");
    let value = info.value.as_ref().expect("actual positive body");
    assert_eq!(info.kind, clean_kernel::ConstantKind::Definition);
    assert!(!value.collect_constants().contains(&name));
    let tracked = spec
        .definitions()
        .get(spelling)
        .expect("tracked normal declaration");
    assert!(!tracked.is_axiom);
    assert!(tracked.axiom_deps.is_empty());
    assert_eq!(tracked.elaborated_type.as_ref(), Some(&info.type_));
    assert_eq!(tracked.elaborated_value.as_ref(), Some(value));
    assert_eq!(
        spec.env().declaration_verification(&name),
        Some(DeclarationVerification::FullKernelCheck)
    );
    assert!(spec.env().get_constant_origin(&name).is_none());
    closed(&info.type_);
    closed(value);
    let mut tc = TypeChecker::with_mode(spec.env(), spec.env().mode());
    tc.set_level_params(info.level_params.clone());
    let sort = tc
        .infer_type_full(&info.type_)
        .expect("public full positive type check");
    assert!(matches!(tc.whnf(&sort).kind(), ExprKind::Sort(_)));
    let inferred = tc
        .infer_type_full(value)
        .expect("public full positive body inference");
    assert!(tc.is_def_eq(&inferred, &info.type_));
    tc.check_type(value, &info.type_)
        .expect("public whole positive body check");
    assert!(!tc.heartbeat_spent());
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
    assert!(spec
        .env()
        .axiom_deps(&name)
        .expect("stored domain closure")
        .is_empty());
    assert!(spec
        .env()
        .foundational_axiom_deps(&name)
        .expect("stored foundational closure")
        .is_empty());
    let mut closure = DomainAxiomClosure::new();
    assert!(closure.assumptions_of_name(spec.env(), &name).is_empty());
    assert!(crate::spec_axiom_closure::computed_axiom_closure(spec, spelling).is_empty());
    assert!(crate::spec_axiom_closure::computed_trust_markers(spec, spelling).is_empty());
    eprintln!(
        "r17-semantic-positive {}",
        json!({"name":spelling,"constant":info,"stored_axioms":[],"computed_axioms":[],"provenance":"FullKernelCheck","inferred_body_type":inferred,"public_type_and_body_checks":"PASS"})
    );
}

fn constructor_authority(spec: &Specification) {
    let env = spec.env();
    let mut records = Vec::new();
    for (spelling, owner, binders) in [
        (
            "Eq.refl",
            "Eq",
            vec![BinderInfo::Implicit, BinderInfo::Default],
        ),
        ("OptionType.none", "OptionType", vec![BinderInfo::Implicit]),
        ("ListType.nil", "ListType", vec![BinderInfo::Implicit]),
        ("WKC.konst", "WKC", vec![BinderInfo::Default; 5]),
    ] {
        let name = Name::from_string(spelling);
        let info = env
            .get_const(&name)
            .expect("genuine normal-prefix constructor");
        let metadata = env
            .get_constructor(&name)
            .expect("actual constructor metadata");
        assert_eq!(metadata.inductive_name, Name::from_string(owner));
        assert_eq!(metadata.type_, info.type_);
        let mut telescope = Vec::new();
        let mut actual = Vec::new();
        let mut ty = &info.type_;
        while let ExprKind::Pi(binder, domain, body) = ty.kind() {
            actual.push(binder.info);
            telescope.push(json!({"binder":binder,"domain":domain}));
            ty = body;
        }
        assert_eq!(
            actual, binders,
            "actual constructor telescope for {spelling}"
        );
        let mut tc = TypeChecker::with_mode(env, env.mode());
        tc.set_level_params(info.level_params.clone());
        let sort = tc
            .infer_type_full(&info.type_)
            .expect("full actual constructor type");
        assert!(matches!(tc.whnf(&sort).kind(), ExprKind::Sort(_)));
        let inferred = tc
            .infer_type_full(&Expr::const_(
                name.clone(),
                info.level_params
                    .iter()
                    .cloned()
                    .map(Level::param)
                    .collect::<Vec<_>>(),
            ))
            .expect("full actual constructor constant");
        assert!(tc.is_def_eq(&inferred, &info.type_));
        assert!(!tc.heartbeat_spent());
        assert_eq!(
            env.declaration_verification(&name),
            Some(DeclarationVerification::FullKernelCheck)
        );
        records.push(json!({"name":name,"constant":info,"constructor":metadata,"inferred_constant_type":inferred,"telescope":telescope,"result":ty,"public_binder_infos":env.get_param_binder_infos(&name),"public_typed_names":env.get_typed_param_names(&name)}));
    }
    let tc = TypeChecker::with_mode(env, env.mode());
    eprintln!(
        "r17-semantic-headers {}",
        json!({"records":records,"environment_mode":env.mode(),"kernel_theory":format!("{:?}",env.kernel_theory()),"checker_settings":format!("{:?}",env.checker_settings()),"models_lean_init":env.models_lean_init(),"cumulative":env.is_cumulative(),"tc_transparency":tc.transparency(),"tc_mode":tc.mode(),"tc_cumulative":tc.is_cumulative()})
    );
}

fn elaborate(spec: &Specification, source: &str) -> Expr {
    let term = spec
        .elaborate_source(source, "independent exact R17 semantic expression")
        .expect("the independent expression must elaborate before its semantic mismatch can count");
    closed(&term);
    term
}

fn independent_mismatch(spec: &Specification, case: &Case) {
    let (head, body) = case
        .explicit
        .split_once(":=")
        .expect("exact negative declaration body");
    let ty_source = head
        .strip_prefix(&format!("def {} : ", case.explicit_name))
        .expect("exact negative target");
    let target = elaborate(spec, ty_source.trim());
    let tc = TypeChecker::with_mode(spec.env(), spec.env().mode());
    let sort = tc
        .infer_type_full(&target)
        .expect("negative claim itself is well typed");
    assert!(matches!(tc.whnf(&sort).kind(), ExprKind::Sort(_)));
    let proof = if case.label == "inertness" {
        // The actual constructor's first premise, with the exact active name
        // and universe list. No reconstruction of a constructor header.
        let partial = elaborate(
            spec,
            "WKC.konst r12_piEnv kcre_witness_delta_head (@ListType.nil Level)",
        );
        let partial_type = tc
            .infer_type_full(&partial)
            .expect("actual partial constructor");
        let ExprKind::Pi(_, premise, _) = partial_type.kind() else {
            panic!("actual inertness premise missing")
        };
        let refl = elaborate(spec, "@Eq.refl (OptionType KExpr) (@OptionType.none KExpr)");
        let refl_type = tc
            .infer_type_full(&refl)
            .expect("candidate reflexivity proof itself fully checks");
        let failure = tc
            .check_type(&refl, premise)
            .expect_err("active definition cannot satisfy the actual inertness premise");
        assert!(
            matches!(failure, TypeError::TypeMismatch { .. }),
            "{failure:?}"
        );
        let rec_refl = elaborate(
            spec,
            "@Eq.refl (OptionType RecMeta) (@OptionType.none RecMeta)",
        );
        let rec_refl_type = tc
            .infer_type_full(&rec_refl)
            .expect("second written reflexivity argument itself fully checks");
        eprintln!(
            "r17-semantic-inertness-premise {}",
            json!({"partial_constructor":partial,"actual_partial_type":partial_type,"first_premise":premise,"proof":refl,"proof_type":refl_type,"second_argument_type":rec_refl_type,"public_error":format!("{failure:?}")})
        );
        Expr::apps(partial, [refl, rec_refl])
    } else {
        let proof = elaborate(spec, body.trim());
        let inferred = tc
            .infer_type_full(&proof)
            .expect("the independently elaborated candidate proof is well typed");
        eprintln!(
            "r17-semantic-typed-proof {}",
            json!({"case":case.label,"proof":proof,"inferred_type":inferred})
        );
        proof
    };
    let failure = tc
        .check_type(&proof, &target)
        .expect_err("exact proper negative must reach a public kernel mismatch");
    assert!(
        matches!(failure, TypeError::TypeMismatch { .. }),
        "{failure:?}"
    );
    assert!(!tc.heartbeat_spent());
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
    eprintln!(
        "r17-semantic-kernel-negative {}",
        json!({"case":case.label,"target":target,"proof":proof,"public_error":format!("{failure:?}"),"resource_cutoff":false})
    );
}

fn no_root(spec: &Specification, spelling: &str) {
    assert!(!spec.definitions().contains_key(spelling));
    assert!(spec.env().get_const(&Name::from_string(spelling)).is_none());
}

fn historical_class(error: &SpecError) -> &'static str {
    match error {
        SpecError::ParseError(_) => "historical_parser_refusal",
        SpecError::EnvError(_) => "historical_environment_refusal",
        SpecError::DeclarationBudgetExhausted { .. } => "historical_resource_cutoff_no_verdict",
        SpecError::ElabError(detail) | SpecError::TypeError(detail) => {
            let lower = detail.to_ascii_lowercase();
            if ["heartbeat", "fuel", "timeout", "budget exhausted"]
                .iter()
                .any(|word| lower.contains(word))
            {
                "historical_resource_or_diagnostic_unclassified"
            } else if ["unknown constant", "unknown name", "unknown identifier"]
                .iter()
                .any(|word| lower.contains(word))
            {
                "historical_name_resolution_refusal"
            } else if ["not a function", "too many arguments", "argument count"]
                .iter()
                .any(|word| lower.contains(word))
            {
                "historical_application_binding_refusal"
            } else if lower.contains("type mismatch") {
                "historical_type_mismatch_semantic_cause_unestablished"
            } else {
                "historical_typing_refusal_unclassified"
            }
        }
        _ => "historical_other_setup_refusal",
    }
}

fn check_case(label: &str) {
    let case = cases()
        .into_iter()
        .find(|case| case.label == label)
        .expect("specified semantic case");
    eprintln!(
        "r17-semantic-progress {}",
        json!({"case":label,"phase":"setup_started","semantic_negatives_completed":0})
    );
    let base = super::r17_spec();
    constructor_authority(&base);
    let mut historical = base.clone();
    no_root(&historical, case.original_name);
    let original_error = historical
        .add_recursive_def(&case.original, "unchanged historical R17 spelling")
        .expect_err("preserve the original historical refusal");
    no_root(&historical, case.original_name);
    eprintln!(
        "r17-semantic-historical {}",
        json!({"case":label,"source":case.original,"error":original_error.to_string(),"debug":format!("{original_error:?}"),"classification":historical_class(&original_error),"semantic_verdict":false,"reason":"Historical spelling is retained independently; any error is not semantic evidence."})
    );
    let mut positive = base.clone();
    positive
        .add_recursive_def(
            &case.positive,
            "actual canonical R17 semantic-positive pair",
        )
        .expect("positive pair registers through the normal public registrar");
    full_positive(&positive, &case.positive_name);
    independent_mismatch(&base, &case);
    let mut negative = base.clone();
    no_root(&negative, &case.explicit_name);
    let error = negative
        .add_recursive_def(
            &case.explicit,
            "proper explicit R17 semantic-negative counterpart",
        )
        .expect_err("the exact proper counterpart must refuse");
    assert_type_mismatch_rejection(&error, label);
    let detail = error.to_string().to_ascii_lowercase();
    for unrelated in [
        "unknown constant",
        "unknown name",
        "unknown identifier",
        "not a function",
        "too many arguments",
        "argument count",
        "parse error",
        "environment error",
    ] {
        assert!(!detail.contains(unrelated), "{label}: {error}");
    }
    no_root(&negative, &case.explicit_name);
    eprintln!(
        "r17-semantic-refusal {}",
        json!({"case":label,"source":case.explicit,"error":error.to_string(),"debug":format!("{error:?}"),"root_present":false,"semantic_negatives_completed":1})
    );
}

#[test]
fn test_r17_semantic_counterpart_sources_parse_and_preserve_parameters() {
    let cases = cases();
    assert_eq!(cases.len(), 4);
    for case in cases {
        crate::test_utils::parse_check(&case.original).expect("unchanged historical source parses");
        crate::test_utils::parse_check(&case.explicit).expect("proper counterpart source parses");
        crate::test_utils::parse_check(&case.positive).expect("canonical positive source parses");
        eprintln!(
            "r17-semantic-source {}",
            json!({"case":case.label,"original":case.original,"explicit":case.explicit,"positive":case.positive,"scope":"Source syntax/custody only; no semantic verdict until actual normal setup and public checks."})
        );
    }
}

#[test]
fn test_r17_semantic_irrelevance_has_checked_positive_and_specific_refusal() {
    check_case("irrel");
}
#[test]
fn test_r17_semantic_zeta_has_checked_positive_and_specific_refusal() {
    check_case("zeta");
}
#[test]
fn test_r17_semantic_konst_shape_has_checked_positive_and_specific_refusal() {
    check_case("shape");
}
#[test]
fn test_r17_semantic_konst_inertness_has_checked_positive_and_specific_refusal() {
    check_case("inertness");
}
