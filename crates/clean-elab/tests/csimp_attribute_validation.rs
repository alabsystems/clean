// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file_with_diagnostics;

fn failure(result: &ElabResult) -> Option<String> {
    match result {
        ElabResult::Failed { error, .. } => Some(error.to_string()),
        ElabResult::Multiple(results) => results.iter().find_map(failure),
        _ => None,
    }
}

#[test]
fn local_csimp_scope_keeps_compiled_bodies_and_later_global_updates() {
    use clean_compiler::lcnf::{Code, DeclValue, LetValue};
    use clean_compiler::to_lcnf::constant_to_decl_with_meaning;
    use clean_compiler::CodeMeaning;
    use clean_kernel::Name;
    let cases: &[(&str, &str, &[(&str, &str)])] = &[
        (
            "proved_runtime",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/proved_runtime.lean"),
            &[("caller", "fast")],
        ),
        (
            "scoped_namespace",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/scoped_namespace.lean"),
            &[
                ("N.inside", "fast"),
                ("outside", "slow"),
                ("opened", "fast"),
            ],
        ),
        (
            "scoped_open",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/scoped_open.lean"),
            &[
                ("N.inside", "fast"),
                ("outside", "slow"),
                ("opened", "fast"),
            ],
        ),
        (
            "scoped_open_in",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/scoped_open_in.lean"),
            &[("temporary", "fast"), ("outside", "slow")],
        ),
        (
            "scoped_reopen",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/scoped_reopen.lean"),
            &[
                ("before", "scopedFast"),
                ("after", "globalFast"),
                ("reopened", "globalFast"),
            ],
        ),
        (
            "local_scope",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/local_scope.lean"),
            &[("inside", "fast"), ("outside", "slow")],
        ),
        (
            "local_nested",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/local_nested.lean"),
            &[
                ("outer", "localFast"),
                ("inner", "innerFast"),
                ("resumed", "localFast"),
                ("outside", "globalFast"),
            ],
        ),
        (
            "local_global_later",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/local_global_later.lean"),
            &[
                ("inside", "localFast"),
                ("during", "globalFast"),
                ("outside", "globalFast"),
            ],
        ),
    ];
    for (case, source, bodies) in cases {
        let mut env = Environment::with_prelude();
        env.init_io_ops().expect("CLI IO");
        let mut context = FileContext::new();
        let parsed = parse_file_with_diagnostics(source).expect("scope syntax");
        assert!(parsed.diagnostics.is_empty());
        for declaration in parsed.decls {
            let declaration = preprocess_decl_with_context(&declaration, &mut context);
            let result =
                elaborate_decl_and_register_with_context(&mut env, &declaration, &mut context)
                    .expect("scope registration");
            assert!(failure(&result).is_none());
        }
        for (owner, expected) in *bodies {
            let info = env.get_const(&Name::from_string(owner)).expect("body");
            let lowered = constant_to_decl_with_meaning(&env, info, CodeMeaning::LeanCompiled)
                .expect("lower")
                .expect("code");
            let DeclValue::Code(body) = lowered.body else {
                panic!("code body");
            };
            let Code::Let(binding, _) = *body else {
                panic!("constant reference");
            };
            let LetValue::Const { name, .. } = binding.value else {
                panic!("callee");
            };
            assert_eq!(name, Name::from_string(expected), "{case}: {owner}");
        }
        if *case == "proved_runtime" {
            let theorem = Name::from_string("replacement");
            assert!(matches!(
                env.get_const(&theorem).expect("proved rule").kind,
                clean_kernel::ConstantKind::Theorem
            ));
            assert!(env
                .axiom_deps(&theorem)
                .expect("transitive axiom closure")
                .is_empty());
            continue;
        }
        if case.starts_with("scoped_") {
            assert_eq!(
                env.is_csimp(&Name::from_string("N.replacement")),
                *case != "scoped_open_in",
                "{case}: marker visibility"
            );
            continue;
        }
        let local = if *case == "local_scope" {
            "replacement"
        } else {
            "localEq"
        };
        assert!(
            !env.is_csimp(&Name::from_string(local)),
            "expired marker: {case}"
        );
        if *case != "local_scope" {
            assert!(env.is_csimp(&Name::from_string("globalEq")));
        }
    }
}

#[test]
fn stale_local_rule_token_cannot_retire_a_later_registration_after_rollback() {
    use clean_kernel::{Declaration, Expr, Name};
    let mut env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let eq = Expr::apps(
        Expr::const_(
            Name::from_string("Eq"),
            vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
        ),
        [
            Expr::arrow(nat.clone(), nat),
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
            Expr::const_(Name::from_string("Nat.succ"), vec![]),
        ],
    );
    let theorem = Name::from_string("ruleIdentity");
    env.add_decl(Declaration::Axiom {
        name: theorem.clone(),
        level_params: vec![],
        type_: eq,
    })
    .expect("explicit test assumption");
    let checkpoint = env.clone();
    let stale = clean_kernel::env::csimp::register_local(&mut env, &theorem).expect("first local");
    env = checkpoint;
    let current =
        clean_kernel::env::csimp::register_local(&mut env, &theorem).expect("second local");
    assert_ne!(stale, current);
    clean_kernel::env::csimp::retire_local(&mut env, stale);
    assert!(env.is_csimp(&theorem));
    let owner = Name::from_string("unscopedBody");
    clean_kernel::env::csimp::record_compiled(&mut env, [owner.clone()]);
    clean_kernel::env::csimp::begin_source_module(&mut env, Name::from_string("NewModule"), vec![]);
    assert!(
        !env.is_csimp(&theorem),
        "a programmatic local rule must not leak into a source module"
    );
    assert!(clean_kernel::env::csimp::rules_for(&env, None).is_empty());
    assert_eq!(
        clean_kernel::env::csimp::rules_for(&env, Some(&owner)).len(),
        1
    );
    clean_kernel::env::csimp::retire_local(&mut env, current);
    assert!(!env.is_csimp(&theorem));
}

#[test]
fn csimp_lowering_preserves_body_order_kernel_values_and_runtime_closure() {
    use clean_compiler::lcnf::{Code, DeclValue, LetValue};
    use clean_compiler::to_lcnf::{
        constant_to_decl_in_runtime_closure, constant_to_decl_with_meaning,
    };
    use clean_compiler::{CodeMeaning, RuntimeBindingClosure};
    use clean_kernel::{Declaration, Expr, Name, TypeChecker};
    let name = |s: &str| Name::from_string(s);
    let mut env = Environment::with_prelude();
    env.init_io_ops().expect("CLI IO environment");
    let mut context = FileContext::new();
    let parsed = parse_file_with_diagnostics(include_str!(
        "../../../reports/csimp-2026-11-12/fixtures/order.lean"
    ))
    .expect("measured source parses");
    assert!(parsed.diagnostics.is_empty());
    for declaration in parsed.decls {
        let declaration = preprocess_decl_with_context(&declaration, &mut context);
        let result = elaborate_decl_and_register_with_context(&mut env, &declaration, &mut context)
            .expect("source admission");
        assert!(failure(&result).is_none());
    }
    let callee = |env: &Environment, owner: &str, meaning| {
        let info = env.get_const(&name(owner)).expect("source definition");
        let lowered = constant_to_decl_with_meaning(env, info, meaning)
            .expect("lowering")
            .expect("executable body");
        let DeclValue::Code(body) = lowered.body else {
            panic!("source body, not extern");
        };
        let Code::Let(binding, _) = *body else {
            panic!("constant-reference body");
        };
        let LetValue::Const { name, .. } = binding.value else {
            panic!("constant callee");
        };
        name
    };
    assert_eq!(
        callee(&env, "before", CodeMeaning::LeanCompiled),
        name("slow")
    );
    assert_eq!(
        callee(&env, "after", CodeMeaning::LeanCompiled),
        name("fast")
    );
    assert_eq!(
        callee(&env, "after", CodeMeaning::KernelValue),
        name("slow")
    );
    assert!(
        TypeChecker::new(&env).is_def_eq(&Expr::const_(name("after"), vec![]), &Expr::nat_lit(1))
    );
    let early = RuntimeBindingClosure::check(&env, &[name("before")]).expect("early closure");
    let late = RuntimeBindingClosure::check(&env, &[name("after")])
        .expect("late closure includes replacement target");
    assert!(env.forget_decl(&name("fast")));
    env.add_decl(Declaration::Definition {
        name: name("fast"),
        level_params: vec![],
        type_: Expr::const_(name("Nat"), vec![]),
        value: Expr::nat_lit(3),
        is_reducible: false,
    })
    .expect("changed target");
    let before = env.get_const(&name("before")).expect("before");
    let after = env.get_const(&name("after")).expect("after");
    assert!(
        constant_to_decl_in_runtime_closure(&env, before, &early).is_ok(),
        "an unrelated later target is outside the earlier body"
    );
    assert!(
        constant_to_decl_in_runtime_closure(&env, after, &late).is_err(),
        "changing a runtime-only replacement target invalidates evidence"
    );
}

#[test]
fn csimp_theorem_shapes_through_source_registration() {
    let cases = [
        (
            "polymorphic",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/polymorphic.lean"),
            true,
        ),
        (
            "concrete_universe",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/concrete_universe.lean"),
            false,
        ),
        (
            "repeated_universe",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/repeated_universe.lean"),
            false,
        ),
        (
            "valid",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/valid.lean"),
            true,
        ),
        (
            "invalid_parameter",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/invalid_parameter.lean"),
            false,
        ),
        (
            "invalid_value",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/invalid_value.lean"),
            false,
        ),
        (
            "private",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/private.lean"),
            true,
        ),
        (
            "historical",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/historical.lean"),
            false,
        ),
        (
            "runtime",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/runtime.lean"),
            true,
        ),
        (
            "order",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/order.lean"),
            true,
        ),
    ];
    for (name, source, accept) in cases {
        let mut env = Environment::with_prelude();
        if matches!(name, "runtime" | "order") {
            env.init_io_ops().expect("shipping CLI's IO declarations");
        }
        let initial = env.constants().filter(|c| env.is_csimp(&c.name)).count();
        let mut context = FileContext::new();
        let parsed = parse_file_with_diagnostics(source).expect("valid fixture syntax");
        assert!(
            parsed.diagnostics.is_empty(),
            "{name}: {:?}",
            parsed.diagnostics
        );
        assert!(!parsed.decls.is_empty());
        let mut errors = Vec::new();
        for declaration in parsed.decls {
            let declaration = preprocess_decl_with_context(&declaration, &mut context);
            let error = match elaborate_decl_and_register_with_context(
                &mut env,
                &declaration,
                &mut context,
            ) {
                Ok(result) => failure(&result),
                Err(error) => Some(error.to_string()),
            };
            if let Some(error) = error {
                errors.push(error);
                break;
            }
        }
        let registered = env.constants().filter(|c| env.is_csimp(&c.name)).count();
        if accept {
            assert!(errors.is_empty(), "{name}: {errors:?}");
            assert_eq!(
                registered,
                initial + 1,
                "{name}: attribute must take effect"
            );
        } else {
            assert!(
                errors
                    .iter()
                    .any(|e| e.contains("invalid 'csimp' theorem")
                        && e.contains("constant replacement")),
                "{name}: {errors:?}"
            );
            assert_eq!(
                registered, initial,
                "{name}: invalid attribute cannot register"
            );
        }
    }
}

#[test]
fn source_module_rules_follow_dependencies_and_preserve_body_views() {
    use clean_kernel::{env::csimp, Name};
    fn elaborate(env: &mut Environment, source: &str) {
        let mut context = FileContext::new();
        let parsed = parse_file_with_diagnostics(source).expect("module syntax");
        assert!(parsed.diagnostics.is_empty());
        for decl in parsed.decls {
            let decl = preprocess_decl_with_context(&decl, &mut context);
            let result = elaborate_decl_and_register_with_context(env, &decl, &mut context)
                .expect("module declaration");
            assert!(failure(&result).is_none());
        }
    }
    let name = Name::from_string;
    let mut env = Environment::with_prelude();
    csimp::begin_source_module(&mut env, name("Base"), vec![]);
    elaborate(&mut env, "def slow : Nat := 1\ndef fast : Nat := 2");
    csimp::begin_source_module(&mut env, name("A"), vec![name("Base")]);
    elaborate(
        &mut env,
        "axiom replacement : slow = fast\nattribute [csimp] replacement\ndef fromA : Nat := slow",
    );
    csimp::begin_source_module(&mut env, name("B"), vec![name("Base")]);
    elaborate(&mut env, "def fromB : Nat := slow");
    assert!(csimp::rules_for(&env, None).is_empty());
    assert!(
        !env.is_csimp(&name("replacement")),
        "sibling module does not import A's attribute"
    );
    csimp::begin_source_module(&mut env, name("Main"), vec![name("A"), name("B")]);
    elaborate(&mut env, "def fromMain : Nat := slow");
    assert!(env.is_csimp(&name("replacement")));
    for owner in ["fromA", "fromMain"] {
        let rules = csimp::rules_for(&env, Some(&name(owner)));
        assert_eq!(rules.len(), 1, "{owner}");
        assert_eq!(rules[0].to, name("fast"));
    }
    assert!(csimp::rules_for(&env, Some(&name("fromB"))).is_empty());
    csimp::begin_source_module(&mut env, name("Local"), vec![name("Base")]);
    elaborate(&mut env, "axiom localReplacement : slow = fast\nattribute [local csimp] localReplacement\ndef fromLocal : Nat := slow");
    assert_eq!(csimp::rules_for(&env, None).len(), 1);
    csimp::begin_source_module(&mut env, name("Importer"), vec![name("Local")]);
    assert!(csimp::rules_for(&env, None).is_empty());
    assert!(!env.is_csimp(&name("localReplacement")));
    assert_eq!(csimp::rules_for(&env, Some(&name("fromLocal"))).len(), 1);
}

#[test]
fn csimp_attribute_arguments_are_rejected_instead_of_discarded() {
    for source in [
        include_str!("../../../reports/csimp-2026-11-12/fixtures/argument_nat.lean"),
        include_str!("../../../reports/csimp-2026-11-12/fixtures/argument_ident.lean"),
        include_str!("../../../reports/csimp-2026-11-12/fixtures/argument_local.lean"),
    ] {
        match parse_file_with_diagnostics(source) {
            Err(error) => assert!(error.to_string().contains("takes no arguments")),
            Ok(parsed) => assert!(
                parsed
                    .diagnostics
                    .iter()
                    .any(|d| format!("{d:?}").contains("takes no arguments")),
                "invalid csimp arguments must prevent a successful source check"
            ),
        }
    }
}

#[test]
fn portable_csimp_snapshots_preserve_bodies_and_deduplicate_dependency_imports() {
    use clean_kernel::{env::csimp, env::TrustedEnvExt, ConstantKind, Declaration, Name};
    fn elaborate(env: &mut Environment, source: &str) {
        let mut context = FileContext::new();
        let parsed = parse_file_with_diagnostics(source).expect("module syntax");
        assert!(parsed.diagnostics.is_empty());
        for decl in parsed.decls {
            let decl = preprocess_decl_with_context(&decl, &mut context);
            let result = elaborate_decl_and_register_with_context(env, &decl, &mut context)
                .expect("module admission");
            assert!(failure(&result).is_none());
        }
    }
    let n = Name::from_string;
    let mut base = Environment::with_prelude();
    csimp::begin_source_module(&mut base, n("Base"), vec![]);
    elaborate(
        &mut base,
        "def slow : Nat := 1\ndef fast : Nat := 2\ndef final : Nat := 3",
    );
    let mut a = base.clone();
    csimp::begin_source_module(&mut a, n("A"), vec![n("Base")]);
    elaborate(&mut a, "axiom globalRule : slow = fast\nattribute [csimp] globalRule\ndef fromA : Nat := slow\nsection\naxiom localRule : slow = final\nattribute [local csimp] localRule\ndef localBody : Nat := slow\nend\nnamespace N\naxiom scopedRule : slow = final\nattribute [scoped csimp] scopedRule\ndef scopedBody : Nat := slow\nend N\ndef afterA : Nat := slow");
    let mut b = base.clone();
    csimp::begin_source_module(&mut b, n("B"), vec![n("Base")]);
    elaborate(&mut b, "def fromB : Nat := slow");
    let mut c = a.clone();
    csimp::begin_source_module(&mut c, n("C"), vec![n("A")]);
    elaborate(
        &mut c,
        "axiom lastRule : slow = final\nattribute [csimp] lastRule\ndef fromC : Nat := slow",
    );
    let extension = n("Clean.compiler.csimpSource");
    let export = |env: &Environment| {
        env.export_extension_states()
            .into_iter()
            .find(|(name, _)| name == &extension)
            .expect("compiler payload")
            .1
    };
    let exports = [export(&a), export(&b), export(&c)];
    for order in [[2, 0, 1], [0, 1, 2]] {
        let mut imported = Environment::with_prelude();
        // Re-admit the exact logical declarations, independently of compiler metadata.
        for (source, names) in [
            (
                &c,
                vec![
                    "slow",
                    "fast",
                    "final",
                    "globalRule",
                    "fromA",
                    "localRule",
                    "localBody",
                    "N.scopedRule",
                    "N.scopedBody",
                    "afterA",
                    "lastRule",
                    "fromC",
                ],
            ),
            (&b, vec!["fromB"]),
        ] {
            for name in names {
                let info = source.get_const(&n(name)).expect("logical declaration");
                let decl = match info.kind {
                    ConstantKind::Axiom => Declaration::Axiom {
                        name: info.name.clone(),
                        level_params: info.level_params.clone(),
                        type_: info.type_.clone(),
                    },
                    ConstantKind::Definition => Declaration::Definition {
                        name: info.name.clone(),
                        level_params: info.level_params.clone(),
                        type_: info.type_.clone(),
                        value: info.value.clone().expect("body"),
                        is_reducible: info.is_reducible,
                    },
                    _ => panic!("unexpected fixture declaration"),
                };
                imported.add_decl(decl).expect("checked logical import");
            }
        }
        imported.register_persistent_extension(extension.clone());
        for (index, module) in order.into_iter().enumerate() {
            imported.add_persistent_extension_entries(&extension, index, exports[module].clone());
        }
        imported.materialize_extension_states();
        assert!(!csimp::has_invalid_metadata(&imported));
        assert_eq!(
            csimp::rules_for(&imported, None)
                .first()
                .map(|r| r.theorem.clone()),
            Some(n("lastRule")),
            "programmatic import view"
        );
        assert!(imported.is_csimp(&n("globalRule")));
        assert!(imported.is_csimp(&n("lastRule")));
        assert!(!imported.is_csimp(&n("localRule")));
        csimp::begin_source_module(&mut imported, n("Main"), vec![n("C"), n("A"), n("B")]);
        for (owner, expected) in [
            ("fromA", Some("fast")),
            ("afterA", Some("fast")),
            ("localBody", Some("final")),
            ("N.scopedBody", Some("final")),
            ("fromB", None),
            ("fromC", Some("final")),
        ] {
            let actual = csimp::rules_for(&imported, Some(&n(owner)));
            assert_eq!(
                actual.first().map(|r| r.to.clone()),
                expected.map(n),
                "{order:?}: {owner}"
            );
        }
        assert_eq!(csimp::rules_for(&imported, None)[0].theorem, n("lastRule"));
        assert!(!imported.is_csimp(&n("localRule")));
        let tokens =
            csimp::activate_namespace(&mut imported, &n("N")).expect("imported scoped definition");
        assert_eq!(
            tokens.len(),
            1,
            "duplicate dependency must not repeat scoped definitions"
        );
        assert_eq!(
            csimp::rules_for(&imported, None)[0].theorem,
            n("N.scopedRule")
        );
        for token in tokens {
            csimp::retire_local(&mut imported, token);
        }
        assert_eq!(csimp::rules_for(&imported, None)[0].theorem, n("lastRule"));
        // Exercise real lowering after import, including a body-local rule that is
        // correctly absent from the importer's active global rules.
        let info = imported.get_const(&n("localBody")).expect("body");
        clean_compiler::to_lcnf::constant_to_decl_with_meaning(
            &imported,
            info,
            clean_compiler::CodeMeaning::LeanCompiled,
        )
        .expect("imported compiler consumer")
        .expect("code");
    }
    let mut corrupt = Environment::with_prelude();
    corrupt.register_persistent_extension(extension.clone());
    corrupt.add_persistent_extension_entries(
        &extension,
        0,
        vec![clean_kernel::env::EnvExtensionEntry {
            name: n("snapshot.v1"),
            data: clean_kernel::env::EnvExtensionEntryData::Object(vec![1, 2, 3]),
        }],
    );
    corrupt.materialize_extension_states();
    assert!(csimp::has_invalid_metadata(&corrupt));
    assert!(clean_compiler::resolve_csimp_dependencies(
        &corrupt,
        &n("any"),
        vec![n("Nat.zero")],
        clean_compiler::CodeMeaning::LeanCompiled
    )
    .is_err());
    assert!(clean_compiler::resolve_csimp_dependencies(
        &corrupt,
        &n("any"),
        vec![n("Nat.zero")],
        clean_compiler::CodeMeaning::KernelValue
    )
    .is_ok());
}

#[test]
fn module_headers_enforce_public_compiler_attributes_and_keep_local_positives() {
    use clean_kernel::Name;
    let cases = [
        (
            "private_global",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/header_private_global.lean"),
            false,
        ),
        (
            "default_global",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/header_default_global.lean"),
            false,
        ),
        (
            "private_scoped",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/header_private_scoped.lean"),
            false,
        ),
        (
            "private_local",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/header_private_local.lean"),
            true,
        ),
        (
            "public_axiom",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/header_public_axiom.lean"),
            true,
        ),
        (
            "public_section",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/header_public_section.lean"),
            true,
        ),
        (
            "section_restore",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/header_section_restore.lean"),
            true,
        ),
        (
            "legacy_private",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/private.lean"),
            true,
        ),
    ];
    for (name, source, accepted) in cases {
        let parsed = parse_file_with_diagnostics(source).expect("header syntax");
        assert!(
            parsed.diagnostics.is_empty(),
            "{name}: {:?}",
            parsed.diagnostics
        );
        let mut context = FileContext::new();
        context.set_main_module(Name::from_string(name));
        context.set_file_header(&parsed.header);
        let mut env = Environment::with_prelude();
        let mut errors = Vec::new();
        for decl in parsed.decls {
            let decl = preprocess_decl_with_context(&decl, &mut context);
            match elaborate_decl_and_register_with_context(&mut env, &decl, &mut context) {
                Ok(result) => {
                    if let Some(error) = failure(&result) {
                        errors.push(error);
                    }
                }
                Err(error) => errors.push(error.to_string()),
            }
        }
        if accepted {
            assert!(errors.is_empty(), "{name}: {errors:?}");
        } else {
            assert!(
                errors.iter().any(|error| error.contains("must be public")),
                "{name}: {errors:?}"
            );
        }
    }
}

#[test]
fn syntactic_rfl_defeq_validation_respects_definition_exposure() {
    use clean_kernel::Name;
    let cases = [
        (
            "plain",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/exposure_plain_public.lean"),
            false,
        ),
        (
            "explicit",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/exposure_explicit_refl.lean"),
            true,
        ),
        (
            "reflexive",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/exposure_reflexive.lean"),
            true,
        ),
        (
            "private",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/exposure_private.lean"),
            true,
        ),
        (
            "exposed",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/exposure_exposed_defs.lean"),
            true,
        ),
        (
            "abbrev",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/exposure_abbrev.lean"),
            true,
        ),
        (
            "section",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/exposure_section.lean"),
            true,
        ),
        (
            "parenthesized",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/exposure_parenthesized.lean"),
            true,
        ),
        (
            "by_rfl",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/exposure_by_rfl.lean"),
            true,
        ),
        (
            "parameters",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/exposure_parameters.lean"),
            true,
        ),
        (
            "explicit_defeq",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/exposure_explicit_defeq.lean"),
            false,
        ),
        (
            "no_expose",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/exposure_no_expose.lean"),
            false,
        ),
        (
            "section_override",
            include_str!(
                "../../../reports/csimp-2026-11-12/fixtures/exposure_section_override.lean"
            ),
            false,
        ),
        (
            "public_helper",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/exposure_public_helper.lean"),
            false,
        ),
        (
            "example",
            include_str!("../../../reports/csimp-2026-11-12/fixtures/exposure_example.lean"),
            true,
        ),
    ];
    for (name, source, accepted) in cases {
        let report = parse_file_with_diagnostics(source).expect("exposure syntax");
        assert!(
            report.diagnostics.is_empty(),
            "{name}: {:?}",
            report.diagnostics
        );
        let mut context = FileContext::new();
        context.set_main_module(Name::from_string(name));
        context.set_file_header(&report.header);
        let mut env = Environment::with_prelude();
        let mut errors = Vec::new();
        for decl in report.decls {
            let decl = preprocess_decl_with_context(&decl, &mut context);
            match elaborate_decl_and_register_with_context(&mut env, &decl, &mut context) {
                Ok(result) => {
                    if let Some(error) = failure(&result) {
                        errors.push(error);
                    }
                }
                Err(error) => errors.push(error.to_string()),
            }
        }
        if accepted {
            assert!(errors.is_empty(), "{name}: {errors:?}");
            let replacement = Name::from_string("replacement");
            if env.get_const(&replacement).is_some() {
                let attrs = env.get_ext_state::<clean_kernel::env::AttrExtState>(
                    clean_kernel::env::attr_ext_idx(),
                );
                let tagged = matches!(
                    name,
                    "reflexive" | "exposed" | "abbrev" | "section" | "parameters"
                );
                for attr in ["defeq", "backward_defeq"] {
                    assert_eq!(
                        attrs.is_some_and(
                            |state| state.has_attr(&replacement, &Name::from_string(attr))
                        ),
                        tagged,
                        "{name}: {attr}"
                    );
                }
            }
        } else {
            assert!(
                errors
                    .iter()
                    .any(|error| error.contains("Not a definitional equality")),
                "{name}: {errors:?}"
            );
        }
        // Export validation never discards the real implementation bodies.
        assert!(env
            .get_const(&Name::from_string("slow"))
            .expect("definition")
            .value
            .is_some());
    }
}

#[test]
fn source_loader_availability_does_not_authorize_sibling_compiler_rules() {
    use clean_kernel::{env::csimp, Name};
    fn elaborate(env: &mut Environment, module: &str, available: &[&str], source: &str) {
        let mut context = FileContext::new();
        context.set_main_module(Name::from_string(module));
        for name in available {
            context.mark_import_satisfied_from_source(&Name::from_string(name));
        }
        let parsed = parse_file_with_diagnostics(source).expect("module syntax");
        assert!(parsed.diagnostics.is_empty());
        for decl in parsed.decls {
            let decl = preprocess_decl_with_context(&decl, &mut context);
            let result = elaborate_decl_and_register_with_context(env, &decl, &mut context)
                .expect("module declaration");
            assert!(failure(&result).is_none(), "{module}: {result:?}");
        }
    }
    let mut env = Environment::with_prelude();
    elaborate(
        &mut env,
        "Base",
        &[],
        "def slow : Nat := 1\ndef fast : Nat := 2",
    );
    elaborate(&mut env, "A", &["Base"], "import Base\naxiom replacement : slow = fast\nattribute [csimp] replacement\ndef fromA : Nat := slow");
    elaborate(
        &mut env,
        "B",
        &["Base", "A"],
        "import Base\ndef fromB : Nat := slow",
    );
    assert!(csimp::rules_for(&env, Some(&Name::from_string("fromB"))).is_empty());
    elaborate(
        &mut env,
        "C",
        &["Base", "A", "B"],
        "import A\ndef fromC : Nat := slow",
    );
    let rules = csimp::rules_for(&env, Some(&Name::from_string("fromC")));
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].theorem, Name::from_string("replacement"));
}
