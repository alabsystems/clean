// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Batteries4.35 command bodies. Import/bootstrap parity is outside this test.
//! The separate data-axiom code generation refusal is tracked by its oracle
//! report and the historical noncomputability class, not credited here.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{ConstantKind, Environment, Name};
use clean_parser::parse_file_with_diagnostics;
fn failed(result: &ElabResult) -> bool {
    match result {
        ElabResult::Failed { .. } => true,
        ElabResult::Multiple(results) => results.iter().any(failed),
        _ => false,
    }
}
#[test]
fn alias_commands_preserve_complete_target_telescopes() {
    let cases = [
        ("plain_poly", include_str!("../../../reports/header-inference-2026-11-12/alias-fixtures/plain_poly.lean"), true),
        ("plain_theorem", include_str!("../../../reports/header-inference-2026-11-12/alias-fixtures/plain_theorem.lean"), true),
        ("iff_poly", include_str!("../../../reports/header-inference-2026-11-12/alias-fixtures/iff_poly.lean"), true),
        ("iff_one", include_str!("../../../reports/header-inference-2026-11-12/alias-fixtures/iff_one.lean"), true),
        ("iff_universe", include_str!("../../../reports/header-inference-2026-11-12/alias-fixtures/iff_universe.lean"), true),
        ("iff_wrong_shape", include_str!("../../../reports/header-inference-2026-11-12/alias-fixtures/iff_wrong_shape.lean"), false),
        ("plain_unknown", include_str!("../../../reports/header-inference-2026-11-12/alias-fixtures/plain_unknown.lean"), false),
        ("plain_local", include_str!("../../../reports/header-inference-2026-11-12/alias-fixtures/plain_local.lean"), false),
        ("iff_three", include_str!("../../../reports/header-inference-2026-11-12/alias-fixtures/iff_three.lean"), false),
        ("explicit_id", include_str!("../../../reports/header-inference-2026-11-12/alias-fixtures/explicit_id.lean"), false),
        ("module_alias", include_str!("../../../reports/header-inference-2026-11-12/alias-fixtures/module_alias.lean"), true),
        ("module_abbrev_alias", include_str!("../../../reports/header-inference-2026-11-12/alias-fixtures/module_abbrev_alias.lean"), true),
        ("reducible", include_str!("../../../reports/header-inference-2026-11-12/alias-fixtures/reducible.lean"), true),
    ];
    let mut mismatches = Vec::new();
    for (name, source, accepted) in cases {
        let mut env = Environment::with_prelude();
        let mut errors = Vec::new();
        match parse_file_with_diagnostics(source) {
            Err(error) => errors.push(error.to_string()),
            Ok(parsed) => {
                errors.extend(parsed.diagnostics.iter().map(|error| format!("{error:?}")));
                let mut context = FileContext::new();
                context.set_main_module(Name::from_string(name));
                context.set_file_header(&parsed.header);
                for decl in parsed.decls {
                    let decl = preprocess_decl_with_context(&decl, &mut context);
                    match elaborate_decl_and_register_with_context(&mut env, &decl, &mut context) {
                        Ok(result) if failed(&result) => errors.push(format!("{result:?}")),
                        Ok(_) => {}
                        Err(error) => errors.push(error.to_string()),
                    }
                }
            }
        }
        if errors.is_empty() != accepted {
            mismatches.push(format!(
                "{name}: expected accepted={accepted}, errors={errors:?}; f={:?}, id={:?}",
                env.get_const(&Name::from_string("f"))
                    .map(|info| &info.type_),
                env.get_const(&Name::from_string("id"))
                    .map(|info| &info.type_),
            ));
        }
        if accepted && errors.is_empty() {
            let alias = env.get_const(&Name::from_string("f")).expect("alias");
            let theorem = matches!(
                name,
                "plain_theorem" | "iff_poly" | "iff_one" | "iff_universe"
            );
            assert_eq!(
                alias.kind,
                if theorem {
                    ConstantKind::Theorem
                } else {
                    ConstantKind::Definition
                },
                "{name}"
            );
            if theorem {
                assert!(
                    env.axiom_deps(&Name::from_string("f"))
                        .expect("computed axiom closure")
                        .is_empty(),
                    "{name}: alias cannot add axioms"
                );
            }
            if matches!(
                name,
                "plain_poly"
                    | "plain_theorem"
                    | "module_alias"
                    | "module_abbrev_alias"
                    | "reducible"
            ) {
                let original = env
                    .get_const(&Name::from_string("original"))
                    .expect("target");
                assert_eq!(alias.type_, original.type_, "{name}");
                assert_eq!(alias.level_params, original.level_params, "{name}");
            }
        }
    }
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}

#[test]
fn alias_metadata_keeps_a_declared_prefix_when_the_target_returns_a_function() {
    let source = "\
def original (n : Nat) : Nat → Nat := fun m => n
alias prefixAlias := original
example : prefixAlias (n := 2) 3 = 2 := rfl
";
    let parsed = parse_file_with_diagnostics(source).expect("prefix alias source parses");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    for decl in parsed.decls {
        let decl = preprocess_decl_with_context(&decl, &mut context);
        let result = elaborate_decl_and_register_with_context(&mut env, &decl, &mut context)
            .expect("prefix alias and named application register");
        assert!(!failed(&result), "{result:?}");
    }
    let alias = Name::from_string("prefixAlias");
    assert_eq!(
        env.get_typed_param_names(&alias),
        Some([Name::from_string("n")].as_slice()),
        "the unnamed returned function argument is not declared metadata"
    );
    assert_eq!(
        env.get_const(&alias).expect("alias").type_,
        env.get_const(&Name::from_string("original"))
            .expect("target")
            .type_
    );
}
