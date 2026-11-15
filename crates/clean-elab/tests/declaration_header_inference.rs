// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Frozen official Lean 4.35 controls: header completion and inference.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file_with_diagnostics;

fn failed(result: &ElabResult) -> bool {
    match result {
        ElabResult::Failed { .. } => true,
        ElabResult::Multiple(results) => results.iter().any(failed),
        _ => false,
    }
}

#[test]
fn declaration_header_inference_matches_frozen_oracle() {
    let cases = [
        ("untyped_unused", include_str!("../../../reports/header-inference-2026-11-12/fixtures/untyped_unused.lean"), false),
        ("untyped_identity", include_str!("../../../reports/header-inference-2026-11-12/fixtures/untyped_identity.lean"), false),
        ("untyped_from_body", include_str!("../../../reports/header-inference-2026-11-12/fixtures/untyped_from_body.lean"), true),
        ("placeholder_from_body", include_str!("../../../reports/header-inference-2026-11-12/fixtures/placeholder_from_body.lean"), true),
        ("placeholder_ascribed", include_str!("../../../reports/header-inference-2026-11-12/fixtures/placeholder_ascribed.lean"), false),
        ("untyped_ascribed", include_str!("../../../reports/header-inference-2026-11-12/fixtures/untyped_ascribed.lean"), false),
        ("later_binder_constrains", include_str!("../../../reports/header-inference-2026-11-12/fixtures/later_binder_constrains.lean"), true),
        ("result_constrains", include_str!("../../../reports/header-inference-2026-11-12/fixtures/result_constrains.lean"), true),
        ("def_result_hole", include_str!("../../../reports/header-inference-2026-11-12/fixtures/def_result_hole.lean"), false),
        ("theorem_result_hole", include_str!("../../../reports/header-inference-2026-11-12/fixtures/theorem_result_hole.lean"), false),
        ("theorem_tactic_hole", include_str!("../../../reports/header-inference-2026-11-12/fixtures/theorem_tactic_hole.lean"), false),
        ("inferred_alias", include_str!("../../../reports/header-inference-2026-11-12/fixtures/inferred_alias.lean"), false),
        ("polymorphic_header", include_str!("../../../reports/header-inference-2026-11-12/fixtures/polymorphic_header.lean"), true),
        ("unused_implicit", include_str!("../../../reports/header-inference-2026-11-12/fixtures/unused_implicit.lean"), false),
        ("example_inferred", include_str!("../../../reports/header-inference-2026-11-12/fixtures/example_inferred.lean"), true),
        ("example_ascribed", include_str!("../../../reports/header-inference-2026-11-12/fixtures/example_ascribed.lean"), false),
        ("default_constrains", include_str!("../../../reports/header-inference-2026-11-12/fixtures/default_constrains.lean"), true),
        ("body_hole", include_str!("../../../reports/header-inference-2026-11-12/fixtures/body_hole.lean"), false),
        ("explicit_polymorphic", include_str!("../../../reports/header-inference-2026-11-12/fixtures/explicit_polymorphic.lean"), true),
        ("expected_lambda", include_str!("../../../reports/header-inference-2026-11-12/fixtures/expected_lambda.lean"), true),
        ("example_result_hole", include_str!("../../../reports/header-inference-2026-11-12/fixtures/example_result_hole.lean"), false),
        ("operator_from_body", include_str!("../../../reports/header-inference-2026-11-12/fixtures/operator_from_body.lean"), true),
    ];
    let mut mismatches = Vec::new();
    for (name, source, accepted) in cases {
        let parsed = parse_file_with_diagnostics(source).expect("syntax");
        assert!(
            parsed.diagnostics.is_empty(),
            "{name}: {:?}",
            parsed.diagnostics
        );
        let mut context = FileContext::new();
        context.set_file_header(&parsed.header);
        let mut env = Environment::with_prelude();
        let mut errors = Vec::new();
        for decl in parsed.decls {
            let decl = preprocess_decl_with_context(&decl, &mut context);
            match elaborate_decl_and_register_with_context(&mut env, &decl, &mut context) {
                Ok(result) if failed(&result) => errors.push(format!("{result:?}")),
                Ok(_) => {}
                Err(error) => errors.push(error.to_string()),
            }
        }
        if errors.is_empty() != accepted {
            mismatches.push(format!(
                "{name}: expected accepted={accepted}, errors={errors:?}"
            ));
        }
        if !accepted && !errors.is_empty() {
            assert!(
                env.get_const(&Name::from_string("f")).is_none(),
                "{name}: failed declaration registered"
            );
        }
    }
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}

#[test]
fn additional_header_contexts_match_frozen_oracle() {
    let cases = [
        ("explicit_identity", include_str!("../../../reports/header-inference-2026-11-12/additional-fixtures/explicit_identity.lean"), true),
        ("polymorphic_lambda", include_str!("../../../reports/header-inference-2026-11-12/additional-fixtures/polymorphic_lambda.lean"), true),
        ("lambda_unresolved_inner", include_str!("../../../reports/header-inference-2026-11-12/additional-fixtures/lambda_unresolved_inner.lean"), false),
        ("local_inference", include_str!("../../../reports/header-inference-2026-11-12/additional-fixtures/local_inference.lean"), true),
        ("well_founded_header_hole", include_str!("../../../reports/header-inference-2026-11-12/additional-fixtures/well_founded_header_hole.lean"), false),
        ("mutual_header_hole", include_str!("../../../reports/header-inference-2026-11-12/additional-fixtures/mutual_header_hole.lean"), false),
        ("partial_header_hole", include_str!("../../../reports/header-inference-2026-11-12/additional-fixtures/partial_header_hole.lean"), false),
        ("partial_typed", include_str!("../../../reports/header-inference-2026-11-12/additional-fixtures/partial_typed.lean"), true),
        ("default_unknown", include_str!("../../../reports/header-inference-2026-11-12/additional-fixtures/default_unknown.lean"), true),
        ("default_wrong_type", include_str!("../../../reports/header-inference-2026-11-12/additional-fixtures/default_wrong_type.lean"), false),
        ("recursor_binders", include_str!("../../../reports/header-inference-2026-11-12/additional-fixtures/recursor_binders.lean"), true),
    ];
    let mut mismatches = Vec::new();
    for (name, source, accepted) in cases {
        let parsed = parse_file_with_diagnostics(source).expect("syntax");
        assert!(
            parsed.diagnostics.is_empty(),
            "{name}: {:?}",
            parsed.diagnostics
        );
        let mut context = FileContext::new();
        context.set_file_header(&parsed.header);
        let mut env = Environment::with_prelude();
        let mut errors = Vec::new();
        for decl in parsed.decls {
            let decl = preprocess_decl_with_context(&decl, &mut context);
            match elaborate_decl_and_register_with_context(&mut env, &decl, &mut context) {
                Ok(result) if failed(&result) => errors.push(format!("{result:?}")),
                Ok(_) => {}
                Err(error) => errors.push(error.to_string()),
            }
        }
        if errors.is_empty() != accepted {
            mismatches.push(format!(
                "{name}: expected accepted={accepted}, errors={errors:?}"
            ));
        }
        if !accepted && !errors.is_empty() {
            assert!(
                env.get_const(&Name::from_string("f")).is_none(),
                "{name}: failed declaration registered"
            );
        }
    }
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}

#[test]
fn prelude_class_carriers_are_explicit() {
    use clean_kernel::{BinderInfo, ExprKind};
    let env = Environment::with_prelude();
    for name in [
        "Repr", "ToString", "Hashable", "BEq", "Neg", "Ord", "Min", "Max", "Zero", "One", "Add",
        "Mul", "Sub",
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .expect("prelude class");
        let ExprKind::Pi(binder, _, _) = info.type_.kind() else {
            panic!("{name}: expected carrier binder");
        };
        assert_eq!(binder.info, BinderInfo::Default, "{name}");
    }
}

#[test]
fn subtype_predicate_can_be_named() {
    let source =
        "def sub : Subtype (fun n : Nat => n = 0) := Subtype.mk (p := fun n : Nat => n = 0) 0 rfl";
    let parsed = parse_file_with_diagnostics(source).expect("syntax");
    assert!(parsed.diagnostics.is_empty());
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    let result = elaborate_decl_and_register_with_context(&mut env, &parsed.decls[0], &mut context)
        .expect("named predicate");
    assert!(!failed(&result));
    assert!(env.get_const(&Name::from_string("sub")).is_some());
}

#[test]
fn application_arity_controls_match_frozen_oracle() {
    let cases = [
        (include_str!("../../../reports/header-inference-2026-11-12/arity-fixtures/recursor_positional.lean"), false),
        (include_str!("../../../reports/header-inference-2026-11-12/arity-fixtures/recursor_explicit.lean"), true),
        (include_str!("../../../reports/header-inference-2026-11-12/arity-fixtures/projection_positional.lean"), false),
        (include_str!("../../../reports/header-inference-2026-11-12/arity-fixtures/projection_explicit.lean"), true),
        (include_str!("../../../reports/header-inference-2026-11-12/arity-fixtures/class_projection_positional.lean"), true),
        (include_str!("../../../reports/header-inference-2026-11-12/arity-fixtures/class_projection_explicit.lean"), true),
        (include_str!("../../../reports/header-inference-2026-11-12/arity-fixtures/eq_positional.lean"), false),
        (include_str!("../../../reports/header-inference-2026-11-12/arity-fixtures/eq_explicit.lean"), true),
        (include_str!("../../../reports/header-inference-2026-11-12/arity-fixtures/negative_inferred.lean"), true),
        (include_str!("../../../reports/header-inference-2026-11-12/arity-fixtures/unsolved_lambda.lean"), false),
        (include_str!("../../../reports/header-inference-2026-11-12/arity-fixtures/list_holes.lean"), false),
    ];
    for (source, accepted) in cases {
        let parsed = parse_file_with_diagnostics(source).expect("oracle syntax");
        assert!(parsed.diagnostics.is_empty());
        let mut env = Environment::with_prelude();
        let mut context = FileContext::new();
        context.set_file_header(&parsed.header);
        let mut errors = Vec::new();
        for declaration in parsed.decls {
            let declaration = preprocess_decl_with_context(&declaration, &mut context);
            match elaborate_decl_and_register_with_context(&mut env, &declaration, &mut context) {
                Ok(result) if failed(&result) => errors.push(format!("{result:?}")),
                Ok(_) => {}
                Err(error) => errors.push(error.to_string()),
            }
        }
        assert_eq!(errors.is_empty(), accepted, "{source}\n{errors:?}");
    }
}

#[test]
fn raw_runtime_q_plan_is_not_a_checked_declaration() {
    let source = "def runtimePrototype := fun (e : Type) => match e with | q($x) => x | _ => e";
    let parsed = parse_file_with_diagnostics(source).expect("prototype syntax");
    assert!(parsed.diagnostics.is_empty());
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    let result = elaborate_decl_and_register_with_context(&mut env, &parsed.decls[0], &mut context);
    assert!(result.as_ref().map_or(true, failed));
    assert!(env
        .get_const(&Name::from_string("runtimePrototype"))
        .is_none());
}

/// `(x : T := by tac)` is Lean's `binderTactic`: the header holds
/// `autoParam T stx` and the tactic is never run there, so a script that
/// would fail (or an unknown name inside it) does not reject the header
/// (elab/2862.lean). `(x : T := (by tac))` is a `binderDefault`, whose term
/// pinned Lean v4.30.0-rc2 elaborates against `T` and rejects here.
#[test]
fn test_header_binder_tactic_is_not_run_but_parenthesized_default_is() {
    let cases = [
        ("def f (h : False := by trivial) : Nat := 0", true),
        (
            "def f (n : Nat) (h : n = n := by exact unknownThing) : Nat := n",
            true,
        ),
        ("axiom f (h : False := by trivial) : False", true),
        ("example (h : False := by trivial) : False := h", true),
        ("def f (h : False := (by trivial)) : Nat := 0", false),
        (
            "def f (x : Nat := true) (h : x = x := by rfl) : Nat := x",
            false,
        ),
    ];
    let mut mismatches = Vec::new();
    for (source, accepted) in cases {
        let parsed = parse_file_with_diagnostics(source).expect("syntax");
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
        let mut context = FileContext::new();
        context.set_file_header(&parsed.header);
        let mut env = Environment::with_prelude();
        let mut errors = Vec::new();
        for decl in parsed.decls {
            let decl = preprocess_decl_with_context(&decl, &mut context);
            match elaborate_decl_and_register_with_context(&mut env, &decl, &mut context) {
                Ok(result) if failed(&result) => errors.push(format!("{result:?}")),
                Ok(_) => {}
                Err(error) => errors.push(error.to_string()),
            }
        }
        if errors.is_empty() != accepted {
            mismatches.push(format!(
                "{source}: expected accepted={accepted}, errors={errors:?}"
            ));
        }
        if !accepted {
            assert!(
                env.get_const(&Name::from_string("f")).is_none(),
                "{source}: failed declaration registered"
            );
        }
    }
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}
