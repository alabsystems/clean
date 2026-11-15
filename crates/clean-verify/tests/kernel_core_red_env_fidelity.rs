// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Front #1 Stage 2 FIDELITY GATE for `kernel_core_red_env`.
//!
//! The reflection generator (`red_env_reflect` bin) emits the foundation-core
//! reflection of the live `Specification::new()` kernel environment as
//! committed generated artifacts. These tests re-walk the SAME live kernel
//! environment and compare the regenerated reflection 1:1 against the
//! committed artifacts — structural levels in both definitions and recursor signatures/RHSs,
//! plus the immediate-source-Lambda/MajorAfterMinors policy — so drift from `RecursorVal`s /
//! definition values and the registered `kernel_core_red_env` literal fails
//! loudly. Plus the interning injectivity test (trust edge 1) and the
//! one-rfl-at-scale probe (the Stage-4 feasibility preview).
//! Projection metadata is independently compared to actual inductive,
//! constructor and ConstantInfo records; its concrete product witness is
//! reconstructed and checked by the source kernel, not by the image producer.

use std::time::Instant;

use clean_kernel::{ConstantKind, Expr, ExprKind, Name, RecursorArgOrder, TypeChecker};
use clean_verify::red_env_reflect::{
    fidelity_check, parse_interning_tsv, reflect_foundation_core, ReflectedConstSig,
    ReflectedConstructor, ReflectedInductive, ReflectedProjectionWitness, SpecExpr, SpecLevel,
    COMMITTED_DEF_SCRIPT, COMMITTED_INTERNING_TSV, COMMITTED_SKIP_LEDGER, REFLECT_DEFS,
    REFLECT_INDUCTIVES,
};
use clean_verify::test_utils::{build_spec_with_stack, run_with_stack};

#[path = "common/kernel_core_red_env_metadata_readback.rs"]
mod metadata_readback;

/// Independent structural oracle: never calls the producer's reflection or
/// erasure functions, and checks every child rather than comparing two images
/// made by the same adapter.
fn assert_level_image(source: &clean_kernel::Level, image: &SpecLevel) {
    use clean_kernel::Level;
    match (source, image) {
        (Level::Zero, SpecLevel::Zero) => {}
        (Level::Param(name), SpecLevel::Param(key)) => {
            assert_eq!(&name.to_string(), key);
        }
        (Level::Succ(a), SpecLevel::Succ(b)) => assert_level_image(a, b),
        (Level::Max(a, b), SpecLevel::Max(x, y)) | (Level::IMax(a, b), SpecLevel::IMax(x, y)) => {
            assert_level_image(a, x);
            assert_level_image(b, y);
        }
        _ => panic!("source level and reflected constructor disagree: {source:?} / {image:?}"),
    }
}

fn assert_expr_image(source: &Expr, image: &SpecExpr) {
    match (source.kind(), image) {
        (ExprKind::MData(_, inner), _) => assert_expr_image(inner, image),
        (ExprKind::BVar(a), SpecExpr::BVar(b)) => assert_eq!(a, b),
        (ExprKind::Sort(level), SpecExpr::Sort(reflected)) => {
            assert_level_image(level, reflected);
        }
        (ExprKind::Const(name, levels), SpecExpr::Const(key, reflected)) => {
            assert_eq!(&name.to_string(), key);
            assert_eq!(
                levels.len(),
                reflected.len(),
                "constant universe argument arity"
            );
            for (level, reflected) in levels.iter().zip(reflected) {
                assert_level_image(level, reflected);
            }
        }
        (ExprKind::App(a, b), SpecExpr::App(x, y))
        | (ExprKind::Lam(_, a, b), SpecExpr::Lam(x, y))
        | (ExprKind::Pi(_, a, b), SpecExpr::Pi(x, y)) => {
            assert_expr_image(a, x);
            assert_expr_image(b, y);
        }
        (ExprKind::Let(_, a, b, c, _), SpecExpr::Let_(x, y, z)) => {
            assert_expr_image(a, x);
            assert_expr_image(b, y);
            assert_expr_image(c, z);
        }
        // A literal leaf is carried whole: its rendering goes through the
        // tagged codec and the string payload decoding (`render_literal`).
        (ExprKind::Lit(lit), SpecExpr::Lit(reflected)) => assert_eq!(lit, reflected),
        _ => panic!("source expression and reflected constructor disagree: {source:?} / {image:?}"),
    }
}

/// Signature-only oracle independent of producer capture/rendering. In
/// particular, compare actual structural identities rather than reparse display
/// names; body-less source entries are not axioms introduced by this adapter.
fn assert_const_signature_image(
    expected_name: &Name,
    source: &clean_kernel::ConstantInfo,
    image: &ReflectedConstSig,
) {
    assert_eq!(
        &source.name, expected_name,
        "actual-name ConstantInfo lookup"
    );
    assert_eq!(&image.name, expected_name, "structural source identity");
    assert_eq!(
        source.kind,
        ConstantKind::Definition,
        "bounded source-family kind"
    );
    assert!(source.value.is_none(), "signature-only source is body-less");
    assert_eq!(
        source.level_params, image.level_params,
        "exact ordered parameters"
    );
    assert_expr_image(&source.type_, &image.type_);
}

fn assert_inductive_image(
    expected: &Name,
    source: &clean_kernel::InductiveVal,
    constant: &clean_kernel::ConstantInfo,
    image: &ReflectedInductive,
) {
    assert_eq!(&source.name, expected, "actual inductive identity");
    assert_eq!(
        constant.level_params, source.level_params,
        "source parameters"
    );
    assert_eq!(constant.type_, source.type_, "source inductive signature");
    assert_const_signature_image(expected, constant, &image.signature);
    assert_eq!(image.num_params, source.num_params, "inductive parameters");
    assert_eq!(image.num_indices, source.num_indices, "inductive indices");
    assert_eq!(
        image.constructor_names, source.constructor_names,
        "ordered structural constructor identities"
    );
    assert_eq!(
        image.all_names, source.all_names,
        "exact final stored ordered mutual-family identities"
    );
}

fn assert_constructor_image(
    parent: &clean_kernel::InductiveVal,
    index: usize,
    source: &clean_kernel::ConstructorVal,
    constant: &clean_kernel::ConstantInfo,
    image: &ReflectedConstructor,
) {
    let expected = parent
        .constructor_names
        .get(index)
        .expect("source constructor slot");
    assert_eq!(&source.name, expected, "actual constructor identity");
    assert_eq!(source.inductive_name, parent.name, "actual source parent");
    assert_eq!(
        source.constructor_idx as usize, index,
        "actual source index"
    );
    assert_eq!(
        source.num_params, parent.num_params,
        "source parameter prefix"
    );
    assert_eq!(
        source.level_params, parent.level_params,
        "source universe order"
    );
    assert_eq!(
        constant.level_params, source.level_params,
        "source parameters"
    );
    assert_eq!(constant.type_, source.type_, "source constructor signature");
    assert_const_signature_image(expected, constant, &image.signature);
    assert_eq!(
        image.inductive_name, source.inductive_name,
        "reflected parent"
    );
    assert_eq!(
        image.num_params, source.num_params,
        "constructor parameters"
    );
    assert_eq!(image.num_fields, source.num_fields, "constructor fields");
    assert_eq!(
        image.constructor_idx, source.constructor_idx,
        "constructor index"
    );
}

/// Reconstruct the specified finite witness from actual source metadata and
/// source constants, never from reflected KExprs or the producer's adapter.
fn assert_projection_witness_image(
    env: &clean_kernel::env::Environment,
    image: &ReflectedProjectionWitness,
) {
    let prod = env
        .get_inductive(&Name::from_string("ProdType"))
        .expect("real product");
    assert_eq!(prod.num_params, 2);
    assert_eq!(prod.num_indices, 0);
    assert!(prod.level_params.is_empty());
    assert_eq!(prod.constructor_names.len(), 1);
    let ctor = env
        .get_constructor(&prod.constructor_names[0])
        .expect("real product constructor");
    assert_eq!(ctor.num_fields, 2);
    assert_eq!(ctor.inductive_name, prod.name);
    let source_constant = |name: &str| {
        let ci = env
            .get_const(&Name::from_string(name))
            .expect("actual witness constant");
        Expr::const_(ci.name.clone(), vec![])
    };
    let nat = source_constant("Nat");
    let zero = source_constant("Nat.zero");
    let one = Expr::app(source_constant("Nat.succ"), zero.clone());
    let value = Expr::apps(
        Expr::const_(ctor.name.clone(), vec![]),
        [nat.clone(), nat.clone(), zero.clone(), one.clone()],
    );
    let expected_type = Expr::apps(
        Expr::const_(prod.name.clone(), vec![]),
        [nat.clone(), nat.clone()],
    );
    let tc = TypeChecker::new(env);
    let inferred = tc
        .infer_type_full(&value)
        .expect("genuine product caller checks");
    assert_eq!(inferred, expected_type);
    assert_expr_image(&value, &image.value);
    assert_expr_image(&inferred, &image.type_);
    // These are actual production projection executions, not a claim that the
    // mathematical raw reduction relation already contains projection beta.
    for (index, expected) in [zero, one].into_iter().enumerate() {
        let projection = Expr::proj(prod.name.clone(), index as u32, value.clone());
        assert_eq!(
            tc.infer_type_full(&projection)
                .expect("actual projection checks"),
            nat
        );
        assert!(tc.is_def_eq(&projection, &expected), "field {index}");
    }
}

#[test]
fn test_projection_metadata_and_witness_against_actual_kernel_source() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let env = spec.env();
        let reflection = reflect_foundation_core(env).expect("source metadata captures");
        assert_eq!(reflection.inductives.len(), REFLECT_INDUCTIVES.len());
        assert!(
            !reflection.constructors.is_empty(),
            "real constructor metadata"
        );
        let mut constructors = reflection.constructors.iter();
        for (spelling, image) in REFLECT_INDUCTIVES.iter().zip(&reflection.inductives) {
            let expected = Name::from_string(spelling);
            let source = env
                .get_inductive(&expected)
                .expect("actual allowlisted inductive");
            let ci = env
                .get_const(&source.name)
                .expect("actual-name ConstantInfo");
            assert_inductive_image(&expected, source, ci, image);
            for (index, name) in source.constructor_names.iter().enumerate() {
                let ctor = env
                    .get_constructor(name)
                    .expect("actual ordered constructor");
                let ci = env
                    .get_const(&ctor.name)
                    .expect("actual-name constructor signature");
                let image = constructors.next().expect("no source constructor omitted");
                assert_constructor_image(source, index, ctor, ci, image);
            }
        }
        assert!(
            constructors.next().is_none(),
            "no extra or duplicated constructors"
        );
        let prod = reflection
            .inductives
            .iter()
            .find(|i| i.signature.name == Name::from_string("ProdType"))
            .expect("nonempty actual ProdType metadata");
        assert_eq!(
            prod.constructor_names,
            vec![Name::from_string("ProdType.mk")]
        );
        assert_projection_witness_image(
            env,
            reflection
                .projection_witness
                .as_ref()
                .expect("nonempty actual product witness"),
        );
    });
}

#[test]
fn test_independent_block_image_oracle_refuses_corruption() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let env = spec.env();
        let reflection = reflect_foundation_core(env).expect("source metadata captures");
        let name = Name::from_string("Nat");
        let source = env.get_inductive(&name).expect("actual Nat metadata");
        let ci = env.get_const(&name).expect("actual Nat signature");
        let image = reflection
            .inductives
            .iter()
            .find(|ind| ind.signature.name == name)
            .expect("actual Nat image");
        assert_eq!(source.all_names, vec![name.clone()]);
        assert_inductive_image(&name, source, ci, image);

        let mut missing = image.clone();
        missing.all_names.clear();
        let mut wrong_kind = image.clone();
        wrong_kind.all_names = source.constructor_names.clone();
        let mut duplicate = image.clone();
        duplicate.all_names.push(name.clone());
        for wrong in [missing, wrong_kind, duplicate] {
            assert!(
                std::panic::catch_unwind(|| assert_inductive_image(&name, source, ci, &wrong))
                    .is_err(),
                "independent actual-source comparison must reject changed block data"
            );
        }
    });
}

#[test]
fn test_independent_projection_metadata_oracle_refuses_corruption() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let env = spec.env();
        let reflection = reflect_foundation_core(env).expect("source metadata captures");
        let name = Name::from_string("Nat");
        let source = env.get_inductive(&name).expect("actual Nat metadata");
        let ci = env.get_const(&source.name).expect("actual Nat signature");
        let image = reflection
            .inductives
            .iter()
            .find(|i| i.signature.name == name)
            .expect("actual Nat image");
        assert_inductive_image(&name, source, ci, image);
        assert_eq!(
            source.constructor_names.len(),
            2,
            "nonvacuous ordering control"
        );
        let mut wrong_order = image.clone();
        wrong_order.constructor_names.reverse();
        let mut wrong_params = image.clone();
        wrong_params.num_params += 1;
        let mut wrong_indices = image.clone();
        wrong_indices.num_indices += 1;
        let mut wrong_type = image.clone();
        wrong_type.signature.type_ = SpecExpr::Sort(SpecLevel::Zero);
        for wrong in [wrong_order, wrong_params, wrong_indices, wrong_type] {
            assert!(
                std::panic::catch_unwind(|| assert_inductive_image(&name, source, ci, &wrong))
                    .is_err()
            );
        }
        // Synthetic source-record controls, not new admitted families. Match
        // the ordered pair in source metadata and ConstantInfo, then reverse
        // only the image; reversing real Nat's empty list would be vacuous.
        let params = vec![Name::from_string("z"), Name::from_string("a")];
        let mut poly_source = source.clone();
        poly_source.level_params = params.clone();
        let mut poly_ci = ci.clone();
        poly_ci.level_params = params.clone();
        let mut poly_image = image.clone();
        poly_image.signature.level_params = params.clone();
        assert_inductive_image(&name, &poly_source, &poly_ci, &poly_image);
        poly_image.signature.level_params.reverse();
        assert!(
            std::panic::catch_unwind(|| {
                assert_inductive_image(&name, &poly_source, &poly_ci, &poly_image);
            })
            .is_err(),
            "inductive signature universe order must not be ignored"
        );
        let ctor = env
            .get_constructor(&source.constructor_names[1])
            .expect("actual successor");
        let ci = env
            .get_const(&ctor.name)
            .expect("actual successor signature");
        let image = reflection
            .constructors
            .iter()
            .find(|c| c.signature.name == ctor.name)
            .expect("actual successor image");
        assert_constructor_image(source, 1, ctor, ci, image);
        let mut wrong_parent = image.clone();
        wrong_parent.inductive_name = Name::from_string("ProdType");
        let mut wrong_params = image.clone();
        wrong_params.num_params += 1;
        let mut wrong_fields = image.clone();
        wrong_fields.num_fields += 1;
        let mut wrong_index = image.clone();
        wrong_index.constructor_idx = 0;
        let mut wrong_type = image.clone();
        wrong_type.signature.type_ = SpecExpr::Sort(SpecLevel::Zero);
        for wrong in [
            wrong_parent,
            wrong_params,
            wrong_fields,
            wrong_index,
            wrong_type,
        ] {
            assert!(std::panic::catch_unwind(|| assert_constructor_image(
                source, 1, ctor, ci, &wrong
            ))
            .is_err());
        }
        // Repeat the ordered-universe control through the constructor oracle.
        let mut source = source.clone();
        source.level_params = params.clone();
        let mut ctor = ctor.clone();
        ctor.level_params = params.clone();
        let mut ci = ci.clone();
        ci.level_params = params.clone();
        let mut correct = image.clone();
        correct.signature.level_params = params;
        assert_constructor_image(&source, 1, &ctor, &ci, &correct);
        let mut wrong = correct;
        wrong.signature.level_params.reverse();
        assert!(std::panic::catch_unwind(|| assert_constructor_image(
            &source, 1, &ctor, &ci, &wrong
        ))
        .is_err());
        let witness = reflection
            .projection_witness
            .as_ref()
            .expect("actual product witness");
        assert_projection_witness_image(env, witness);
        let mut wrong_value = witness.clone();
        wrong_value.value = SpecExpr::BVar(0);
        let mut wrong_type = witness.clone();
        wrong_type.type_ = SpecExpr::Sort(SpecLevel::Zero);
        for wrong in [wrong_value, wrong_type] {
            assert!(
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    assert_projection_witness_image(env, &wrong);
                }))
                .is_err(),
                "actual source witness value and inferred type must be compared"
            );
        }
    });
}

#[test]
fn test_independent_nat_signature_oracle_refuses_name_params_and_type_drift() {
    let name = Name::anon().str("nested.u");
    let params = vec![Name::from_string("z"), Name::from_string("a")];
    let source = clean_kernel::ConstantInfo::new(
        name.clone(),
        params.clone(),
        Expr::sort(clean_kernel::Level::Param(params[0].clone())),
        None,
        false,
    );
    let correct = ReflectedConstSig {
        name: name.clone(),
        level_params: params,
        type_: SpecExpr::Sort(SpecLevel::Param("z".to_string())),
    };
    assert_const_signature_image(&name, &source, &correct);
    let mut wrong_name = correct.clone();
    wrong_name.name = Name::anon().str("nested").str("u");
    assert_eq!(wrong_name.name.to_string(), name.to_string());
    let mut wrong_params = correct.clone();
    wrong_params.level_params.reverse();
    let mut wrong_type = correct.clone();
    wrong_type.type_ = SpecExpr::Sort(SpecLevel::Zero);
    for wrong in [wrong_name, wrong_params, wrong_type] {
        assert!(
            std::panic::catch_unwind(|| assert_const_signature_image(&name, &source, &wrong))
                .is_err(),
            "independent oracle must refuse structural identity, ordering, or type drift"
        );
    }
}

/// Independent source-policy oracle: inspect the immediate production AST tag
/// before the image traversal erases metadata. An identical KExpr image cannot
/// establish that production selected the standard lambda branch.
fn assert_immediate_rule_rhs_image(source: &Expr, image: &SpecExpr) {
    assert!(
        source.is_lam(),
        "active reflected rule requires immediate source Lambda"
    );
    assert_expr_image(source, image);
}

#[test]
fn test_independent_rule_policy_rejects_metadata_wrapped_lambda_with_same_image() {
    let bare = Expr::lam(
        clean_kernel::BinderInfo::Default,
        Expr::sort(clean_kernel::Level::Param(Name::from_string("u"))),
        Expr::bvar(0),
    );
    let image = SpecExpr::Lam(
        Box::new(SpecExpr::Sort(SpecLevel::Param("u".to_string()))),
        Box::new(SpecExpr::BVar(0)),
    );
    let wrapped = Expr::mdata(
        vec![(
            Name::from_string("branch-policy"),
            clean_kernel::MDataValue::Bool(true),
        )],
        bare.clone(),
    );
    assert_expr_image(&bare, &image);
    assert_expr_image(&wrapped, &image);
    assert_immediate_rule_rhs_image(&bare, &image);
    assert!(
        std::panic::catch_unwind(|| assert_immediate_rule_rhs_image(&wrapped, &image)).is_err()
    );
}

#[test]
fn test_independent_fidelity_oracle_rejects_parameter_erasure_and_constructor_drift() {
    use clean_kernel::Level;
    use std::sync::Arc;
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let source = Expr::const_str_levels(
        "Head",
        vec![Level::IMax(
            Arc::new(Level::Param(u)).into(),
            Arc::new(Level::Param(v)).into(),
        )],
    );
    let correct = SpecExpr::Const(
        "Head".to_string(),
        vec![SpecLevel::IMax(
            Box::new(SpecLevel::Param("u".to_string())),
            Box::new(SpecLevel::Param("v".to_string())),
        )],
    );
    assert_expr_image(&source, &correct);
    let mutations = [
        SpecExpr::Const(
            "Head".to_string(),
            vec![SpecLevel::IMax(
                Box::new(SpecLevel::Zero),
                Box::new(SpecLevel::Zero),
            )],
        ),
        SpecExpr::Const(
            "Head".to_string(),
            vec![SpecLevel::Max(
                Box::new(SpecLevel::Param("u".to_string())),
                Box::new(SpecLevel::Param("v".to_string())),
            )],
        ),
        SpecExpr::Const(
            "Head".to_string(),
            vec![SpecLevel::IMax(
                Box::new(SpecLevel::Param("v".to_string())),
                Box::new(SpecLevel::Param("u".to_string())),
            )],
        ),
        SpecExpr::Const("Head".to_string(), vec![]),
    ];
    for mutation in mutations {
        assert!(
            std::panic::catch_unwind(|| assert_expr_image(&source, &mutation)).is_err(),
            "independent traversal must reject erased, renamed, reordered or missing universe data"
        );
    }
    let source_sort = Expr::sort(Level::Param(Name::from_string("u")));
    let erased_sort = SpecExpr::Sort(SpecLevel::Zero);
    assert!(std::panic::catch_unwind(|| assert_expr_image(&source_sort, &erased_sort)).is_err());
    assert_expr_image(
        &source_sort,
        &SpecExpr::Sort(SpecLevel::Param("u".to_string())),
    );
}

/// THE FIDELITY GATE: regenerating the reflection from the live kernel env
/// must reproduce the committed def script, interning table, and skip
/// ledger byte-for-byte (the renderer is deterministic, so byte equality IS
/// equality of the bounded structural image, not a production refinement proof).
#[test]
fn test_fidelity_gate_regenerated_reflection_matches_committed_artifacts() {
    run_with_stack(|| {
        // Exercise the generator's artifact-independent full-build path with a
        // harmless extra marker. Seeing the marker live proves this build
        // consumed the supplied in-memory script rather than the committed
        // `include_str!` payload; the reflection itself must remain identical.
        let injected_script =
            format!("def kcre_full_validation_probe : Nat := Nat.zero\n{COMMITTED_DEF_SCRIPT}");
        let spec =
            clean_verify::Specification::new_with_red_env_reflection_script(&injected_script)
                .expect("full spec should build from the fresh in-memory script");
        let injected = spec
            .env()
            .get_const(&Name::from_string("kcre_full_validation_probe"))
            .expect("full spec must consume the injected script");
        assert!(
            injected.value.is_some(),
            "injected validation marker must be a value-bearing definition"
        );
        let reflection = fidelity_check(
            spec.env(),
            COMMITTED_DEF_SCRIPT,
            COMMITTED_INTERNING_TSV,
            COMMITTED_SKIP_LEDGER,
        )
        .expect("regenerated reflection must match the committed generated artifacts (no drift)");
        assert!(
            !reflection.recs.is_empty() && !reflection.defs.is_empty(),
            "reflection must be non-empty (foundation core present)"
        );

        // Regeneration must not depend on loading the artifact it replaces.
        // The dedicated seed contains exactly the allowlisted source
        // declarations and must render byte-identically to the final full
        // environment.
        let seed = clean_verify::Specification::new_red_env_reflection_seed()
            .expect("artifact-independent reflection seed should build");
        let seeded =
            reflect_foundation_core(seed.env()).expect("seed structural names are unambiguous");
        assert_eq!(
            seeded
                .def_script()
                .expect("seed reflection should render safely"),
            reflection
                .def_script()
                .expect("full reflection should render safely"),
            "artifact-independent seed and full live environment must generate the same script"
        );
        assert_eq!(
            seeded.interning_tsv(),
            reflection.interning_tsv(),
            "seed and full environment must generate the same interning table"
        );
        assert_eq!(
            seeded
                .skip_ledger_md()
                .expect("seed ledger should render safely"),
            reflection
                .skip_ledger_md()
                .expect("full ledger should render safely"),
            "seed and full environment must generate the same coverage ledger"
        );
    });
}

/// Field-for-field walk DIRECTLY against the kernel's `RecursorVal`s (not via
/// the renderer): every reflected recursor mirrors its kernel counterpart's
/// ordered universe parameters, structural schematic type, metadata counts,
/// and per-rule (constructor name, num_fields, structural schematic RHS).
/// Source branch selection is checked before the independent image traversal.
#[test]
fn test_fidelity_gate_field_for_field_against_kernel_recursors() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let env = spec.env();
        let reflection =
            reflect_foundation_core(env).expect("live structural names are unambiguous");
        for rec in &reflection.recs {
            let rv = env
                .get_recursor(&Name::from_string(&rec.name))
                .unwrap_or_else(|| panic!("{} should be a kernel recursor", rec.name));
            let ci = env
                .get_const(&rv.name)
                .unwrap_or_else(|| panic!("{} should have an actual-name signature", rec.name));
            assert_eq!(ci.name, rv.name, "{}: actual-name ConstantInfo", rec.name);
            assert_eq!(
                ci.level_params, rv.level_params,
                "{}: exact ordered universes in both source records",
                rec.name
            );
            assert_eq!(
                ci.type_, rv.type_,
                "{}: exact source schematic signature",
                rec.name
            );
            assert_eq!(
                rec.level_params,
                rv.level_params
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
                "{}: reflected signature preserves source parameter order",
                rec.name
            );
            assert_expr_image(&rv.type_, &rec.type_);
            assert_eq!(rec.num_params, rv.num_params, "{}: num_params", rec.name);
            assert_eq!(rec.num_motives, rv.num_motives, "{}: num_motives", rec.name);
            assert_eq!(rec.num_minors, rv.num_minors, "{}: num_minors", rec.name);
            assert_eq!(rec.num_indices, rv.num_indices, "{}: num_indices", rec.name);
            assert_eq!(
                rv.arg_order,
                RecursorArgOrder::MajorAfterMinors,
                "{}: only the MajorAfterMinors layout is reflected",
                rec.name
            );
            assert_eq!(
                rec.rules.len(),
                rv.rules.len(),
                "{}: rule count (one per constructor)",
                rec.name
            );
            for (refl_rule, kernel_rule) in rec.rules.iter().zip(rv.rules.iter()) {
                assert_eq!(
                    refl_rule.ctor,
                    kernel_rule.constructor_name.to_string(),
                    "{}: rule constructor name",
                    rec.name
                );
                assert_eq!(
                    refl_rule.num_fields, kernel_rule.num_fields,
                    "{}/{}: num_fields",
                    rec.name, refl_rule.ctor
                );
                assert_immediate_rule_rhs_image(&kernel_rule.rhs, &refl_rule.rhs);
            }
        }
        for def in &reflection.defs {
            let ci = env
                .get_const(&Name::from_string(&def.name))
                .unwrap_or_else(|| panic!("{} should be a kernel constant", def.name));
            assert_eq!(
                ci.kind,
                ConstantKind::Definition,
                "{}: ordinary-definition domain, independent of reducibility hints",
                def.name,
            );
            let value = ci
                .value
                .as_ref()
                .unwrap_or_else(|| panic!("{} should have a kernel value", def.name));
            assert_expr_image(value, &def.value);
            assert_expr_image(&ci.type_, &def.type_);
            assert_eq!(
                def.level_params,
                ci.level_params
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
                "{}: exact ordered parameters from the same ConstantInfo as type/value",
                def.name,
            );
            assert_eq!(
                def.is_reducible, ci.is_reducible,
                "{}: reducibility",
                def.name
            );
        }
        // Required typing-data slice is not the delta allowlist. Source keys
        // come from actual family metadata, and lookup uses those structural Names.
        let nat_rec = env
            .get_recursor(&Name::from_string("Nat.rec"))
            .expect("actual Nat recursor");
        let nat = env
            .get_inductive(&nat_rec.inductive_name)
            .expect("actual Nat family");
        assert_eq!(nat.constructor_names.len(), 2);
        let expected_names = [
            &nat.name,
            &nat.constructor_names[0],
            &nat.constructor_names[1],
            &nat_rec.name,
        ];
        assert_eq!(reflection.nat_signatures.len(), expected_names.len());
        for (image, expected) in reflection.nat_signatures.iter().zip(expected_names) {
            let ci = env
                .get_const(expected)
                .expect("required actual-name ConstantInfo");
            assert_const_signature_image(expected, ci, image);
            // Measure completed source-builder provenance, not the provisional
            // StructuralOnly marker used while generated recursors are staged.
            // This regression is not a formal proof of validator soundness.
            let verification = env
                .declaration_verification(expected)
                .expect("completed Nat-family entry has explicit source provenance");
            assert_eq!(
                verification,
                clean_kernel::DeclarationVerification::FullKernelCheck,
                "{expected}: completed source checks must precede the final stamp"
            );
            eprintln!("nat_signature_source_provenance {expected}: {verification:?}");
        }
        let rec_signature = &reflection.nat_signatures[3];
        assert_eq!(rec_signature.level_params, nat_rec.level_params);
        assert_expr_image(&nat_rec.type_, &rec_signature.type_);

        // Every allowlisted item is either reflected or in the skip ledger
        // with a reason (coverage-with-skips: nothing silently dropped).
        for ind in REFLECT_INDUCTIVES {
            let rec_name = format!("{ind}.rec");
            let reflected = reflection.recs.iter().any(|r| r.name == rec_name);
            let skipped = reflection
                .skips
                .iter()
                .any(|s| s.item.starts_with(&rec_name) && !s.item.contains("K-extension"));
            assert!(
                reflected || skipped,
                "{rec_name}: must be reflected or skip-ledgered"
            );
        }
        for def in REFLECT_DEFS {
            let ci = env
                .get_const(&Name::from_string(def))
                .unwrap_or_else(|| panic!("{def}: current allowlisted definition must exist"));
            assert_eq!(
                ci.kind,
                ConstantKind::Definition,
                "{def}: a current source-kind change requires an explicit allowlist-policy review",
            );
            let reflected = reflection.defs.iter().any(|d| &d.name == def);
            let skipped = reflection.skips.iter().any(|s| &s.item == def);
            assert!(
                reflected || skipped,
                "{def}: must be reflected or skip-ledgered"
            );
        }
    });
}

/// Trust edge 1: distinct semantic-name strings get distinct tags. This is not
/// an injectivity theorem for arbitrary structural kernel Name trees: their
/// display strings can conflate numeric and string components. The literal
/// adapter's canonical one-component Nat/String names form a bounded case.
#[test]
fn test_interning_table_injective() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let reflection =
            reflect_foundation_core(spec.env()).expect("live structural names are unambiguous");
        assert!(
            reflection.interning_injective(),
            "interning table must be injective"
        );
        // Reuse the same whole-table parser as semantic source consumers.
        let committed = parse_interning_tsv(COMMITTED_INTERNING_TSV)
            .expect("committed interning table must satisfy the full format");
        assert_eq!(
            committed.len(),
            reflection.interning.len(),
            "committed table row count matches regenerated interning"
        );
    });
}

/// `kernel_core_red_env` is registered as a VALUE-FUL definition (lowers to
/// `Declaration::Definition` — census-neutral, ratchet-clean), parallel to
/// `the_red_env` (which is NOT swapped in Stage 2).
#[test]
fn test_kernel_core_red_env_registered_census_neutral() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let def = spec
            .definitions()
            .get("kernel_core_red_env")
            .expect("kernel_core_red_env should be registered");
        assert!(!def.is_axiom, "kernel_core_red_env must not be an axiom");
        assert!(
            def.value_src.is_some(),
            "kernel_core_red_env must be value-ful"
        );
        let ci = spec
            .env()
            .get_const(&Name::from_string("kernel_core_red_env"))
            .expect("kernel_core_red_env should be a kernel constant");
        assert!(
            ci.value.is_some(),
            "kernel_core_red_env must lower to a value-ful kernel Definition (census-neutral)"
        );
        // The generated helper pool (kcre_nat_* / kcre_name_*) lowers to
        // value-ful kernel Definitions too (census-neutral).
        for helper in ["kcre_nat_0", "kcre_name_0"] {
            let hci = spec
                .env()
                .get_const(&Name::from_string(helper))
                .unwrap_or_else(|| panic!("{helper} should be a kernel constant"));
            assert!(hci.value.is_some(), "{helper} must be value-ful");
        }
        // the_red_env is registered and — post Front #1 Stage 3 — is the
        // value-level ALIAS of kernel_core_red_env.
        let tre = spec
            .definitions()
            .get("the_red_env")
            .expect("the_red_env must still be registered");
        assert!(
            tre.value_src
                .as_deref()
                .is_some_and(|v| v.contains("kernel_core_red_env")),
            "the_red_env must be the Stage-3 alias of kernel_core_red_env, got: {:?}",
            tre.value_src
        );
    });
}

/// THE ONE-RFL-AT-SCALE PROBE (Stage-4 feasibility preview): the kernel must
/// whnf-EVALUATE each Stage-1 closure checker fold over the full reflected
/// env down to a Bool CONSTRUCTOR (fold does not stick), and the cost is
/// measured. NOTE the honest expectation: the Stage-1 checkers test
/// `bvar_ceiling rhs = 0`, an ADD-based over-approximation that only
/// certifies bvar-FREE rhs/values; real kernel rule rhss are closed lambdas
/// WITH bvars, so the checker may evaluate to `Bool.false` even though the
/// closure interfaces hold. This test gates EVALUATION (the scaling
/// question); the computed verdicts + timings are printed for the report.
#[test]
fn test_one_rfl_probe_checker_folds_evaluate_over_reflected_env() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let tc = TypeChecker::new(spec.env());
        for (checker, proj) in [
            ("rec_env_closed_b", "red_rec"),
            ("rec_env_lift_closed_b", "red_rec"),
            ("def_env_closed_b", "red_def"),
            ("def_env_lift_closed_b", "red_def"),
        ] {
            let e = Expr::app(
                Expr::const_str(checker),
                Expr::app(
                    Expr::const_str(proj),
                    Expr::const_str("kernel_core_red_env"),
                ),
            );
            let t = Instant::now();
            let w = tc.whnf(&e);
            let dt = t.elapsed();
            let verdict = match w.kind() {
                ExprKind::Const(n, _) => n.to_string(),
                other => panic!(
                    "{checker} fold STUCK over kernel_core_red_env: whnf head {other:?} \
                     (expected a Bool constructor)"
                ),
            };
            assert!(
                verdict == "Bool.true" || verdict == "Bool.false",
                "{checker}: whnf must reach a Bool constructor, got {verdict}"
            );
            println!(
                "one-rfl probe: {checker} ({proj} kernel_core_red_env) = {verdict} in {:.3}s",
                dt.as_secs_f64()
            );
        }

        // Aggregate per-element cost (the TRUE-case fold cost the Bool.and
        // short-circuit hides): force the full per-element checker test
        // `nat_eqb (bvar_ceiling <term>) 0` for every reflected rule rhs and
        // definition type/value. Every element must EVALUATE to a Bool constructor; the
        // total is the measured one-rfl budget for a Stage-4 depth-aware
        // checker at real-env scale.
        let reflection =
            reflect_foundation_core(spec.env()).expect("live structural names are unambiguous");
        let mut elements = Vec::new();
        for rec in &reflection.recs {
            for rule in &rec.rules {
                elements.push((format!("{}/{}", rec.name, rule.ctor), &rule.rhs));
            }
        }
        for def in &reflection.defs {
            elements.push((format!("{} (type)", def.name), &def.type_));
            elements.push((def.name.clone(), &def.value));
        }
        assert!(
            !elements.is_empty(),
            "reflected env must contribute probe elements"
        );
        let mut total = std::time::Duration::ZERO;
        for (label, term) in &elements {
            let reflected_term = reflection
                .kexpr_term(term)
                .unwrap_or_else(|error| panic!("{label}: reflected term must render: {error}"));
            let e = Expr::apps(
                Expr::const_str("nat_eqb"),
                [
                    Expr::app(Expr::const_str("bvar_ceiling"), reflected_term),
                    Expr::const_str("kcre_nat_0"),
                ],
            );
            let t = Instant::now();
            let w = tc.whnf(&e);
            total += t.elapsed();
            match w.kind() {
                ExprKind::Const(n, _)
                    if n.to_string() == "Bool.true" || n.to_string() == "Bool.false" => {}
                other => panic!("element probe {label} STUCK: whnf head {other:?}"),
            }
        }
        println!(
            "one-rfl element probes: {} elements fully forced in {:.3}s total",
            elements.len(),
            total.as_secs_f64()
        );
    });
}
