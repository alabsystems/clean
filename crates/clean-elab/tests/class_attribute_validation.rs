// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Live source registration controls measured against official Lean v4.35.0.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::ConstantKind;
use clean_kernel::{Environment, Name};
use clean_parser::parse_file_with_diagnostics;

fn collect(result: ElabResult, errors: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for result in results {
                collect(result, errors);
            }
        }
        ElabResult::Failed { error, .. } => errors.push(error.to_string()),
        _ => {}
    }
}

fn run_in(env: &mut Environment, source: &str) -> Vec<String> {
    let report = parse_file_with_diagnostics(source).expect("control must parse");
    assert!(report.diagnostics.is_empty(), "{:?}", report.diagnostics);
    assert!(!report.decls.is_empty(), "control cannot skip its subject");
    let mut file = FileContext::new();
    let mut errors = Vec::new();
    for decl in &report.decls {
        let decl = preprocess_decl_with_context(decl, &mut file);
        match elaborate_decl_and_register_with_context(env, &decl, &mut file) {
            Ok(result) => collect(result, &mut errors),
            Err(error) => errors.push(error.to_string()),
        }
    }
    errors
}

#[test]
fn class_attribute_target_and_parameter_cohort() {
    let cases = [
        ("def_annotation", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/def_annotation.lean"), false),
        ("def_command", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/def_command.lean"), false),
        ("opaque", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/opaque.lean"), false),
        ("abbrev", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/abbrev.lean"), false),
        ("theorem", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/theorem.lean"), false),
        ("constructor", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/constructor.lean"), false),
        ("duplicate", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/duplicate.lean"), false),
        ("structure", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/structure.lean"), true),
        ("inductive", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/inductive.lean"), true),
        ("axiom_command", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/axiom_command.lean"), true),
        ("axiom_annotation", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/axiom_annotation.lean"), true),
        ("outparam", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/outparam.lean"), true),
        ("bad_outparam", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/bad_outparam.lean"), false),
        ("good_outparam", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/good_outparam.lean"), true),
        ("retained_definition", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/retained_definition.lean"), false),
        ("axiom_bad_outparam", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/axiom_bad_outparam.lean"), false),
        ("promoted_instance", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/promoted_instance.lean"), true),
        ("semi_outparam", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/semi_outparam.lean"), true),
        ("class_def_must_fail", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/class_def_must_fail.lean"), false),
        ("classBadOutParam", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/classBadOutParam.lean"), false),
        ("opaque_no_body_command", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/opaque_no_body_command.lean"), false),
        ("opaque_no_body_annotation", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/opaque_no_body_annotation.lean"), false),
        ("builtin_inductive", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/builtin_inductive.lean"), true),
        ("indexed_inductive", include_str!("../../../reports/class-attribute-2026-11-12/fixtures/indexed_inductive.lean"), true),
    ];
    for (name, source, accept) in cases {
        let mut env = Environment::with_prelude();
        let errors = run_in(&mut env, source);
        if accept {
            assert!(errors.is_empty(), "{name}: {errors:?}");
            let (class_name, params, outs, semis): (&str, usize, &[usize], &[usize]) = match name {
                "builtin_inductive" => ("Nat", 0, &[], &[]),
                "indexed_inductive" => ("Eq", 3, &[], &[]),
                "outparam" => ("C", 2, &[1], &[]),
                "good_outparam" => ("C", 3, &[0, 1], &[]),
                "promoted_instance" => ("C", 2, &[0, 1], &[]),
                "semi_outparam" => ("C", 2, &[], &[1]),
                _ => ("C", 1, &[], &[]),
            };
            let info = env
                .get_class_info(&Name::from_string(class_name))
                .expect("class flag must be registered, not ignored");
            assert_eq!(info.num_params, params, "{name}");
            assert_eq!(info.out_params, outs, "{name}");
            assert_eq!(info.semi_out_params, semis, "{name}");
        } else {
            let expected = if name == "duplicate" {
                "class has already been declared"
            } else if name.contains("bad_outparam") || name == "classBadOutParam" {
                "depends on `outParam`"
            } else {
                "invalid 'class'"
            };
            assert!(
                errors.iter().any(|e| e.contains(expected)),
                "{name}: wrong refusal or acceptance: {errors:?}"
            );
            let bad = match name {
                "theorem" => "bad",
                "constructor" => "C.mk",
                "bad_outparam" | "axiom_bad_outparam" => "C",
                "classBadOutParam" => "C1",
                "class_def_must_fail" => "Foo",
                "duplicate" => "",
                _ => "Bad",
            };
            if name != "duplicate" {
                assert!(
                    !env.is_class(&Name::from_string(bad)),
                    "{name}: invalid target gained class metadata"
                );
            }
            if name == "retained_definition" {
                assert!(
                    env.get_const(&Name::from_string("Bad")).is_some(),
                    "Lean retains the checked definition after its attribute fails"
                );
            }
        }
    }
}

#[test]
fn ordinary_class_cannot_replace_unowned_axiom_metadata() {
    let mut env = Environment::with_prelude();
    let name = Name::from_string("Fact");
    // This is deliberately a raw caller-created axiom and class row. Earlier
    // source registration treated its shape as bootstrap authority. The source
    // boundary now preserves it and refuses replacement; genuine builtin Fact
    // completion is covered through its actual creator in the LIB controls.
    use clean_kernel::{BinderInfo, Declaration, Expr, Level};
    let prop = Expr::sort(Level::zero());
    env.add_decl(Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, prop.clone(), prop),
    })
    .expect("checked raw axiom type");
    env.register_class(clean_kernel::env::KernelClassInfo {
        name: name.clone(),
        num_params: 1,
        out_params: vec![],
        semi_out_params: vec![],
    });
    let before = env.get_const(&name).expect("raw axiom").clone();
    let metadata = env.get_class_info(&name).expect("raw class row").clone();
    let errors = run_in(&mut env, "class Fact (p : Prop) : Prop where\n  out : p\n");
    assert!(!errors.is_empty());
    assert_eq!(env.get_const(&name), Some(&before));
    assert_eq!(env.get_class_info(&name), Some(&metadata));
    assert!(env.get_inductive(&name).is_none());
}

#[test]
fn source_opaque_kind_survives_environment_clone_without_hiding_axiom_storage() {
    let mut env = Environment::with_prelude();
    assert!(run_in(&mut env, "opaque Hidden : Type\n").is_empty());
    let name = Name::from_string("Hidden");
    assert_eq!(
        env.get_const(&name).expect("opaque exists").kind,
        ConstantKind::Axiom
    );
    let mut consumer = env.clone();
    let errors = run_in(&mut consumer, "attribute [class] Hidden\n");
    assert!(
        errors.iter().any(|e| e.contains("invalid 'class'")),
        "{errors:?}"
    );
    assert!(!consumer.is_class(&name));
    assert_eq!(
        consumer
            .get_const(&name)
            .expect("assumption remains visible")
            .kind,
        ConstantKind::Axiom
    );
}
