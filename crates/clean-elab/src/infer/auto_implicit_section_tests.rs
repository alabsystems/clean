// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::{Environment, Name};

fn run_source(
    source: &str,
) -> (
    Environment,
    Vec<Result<crate::ElabResult, crate::ElabError>>,
) {
    let mut env = Environment::with_prelude();
    let mut file = crate::FileContext::new();
    let declarations = clean_parser::parse_file(source).expect("actual source parses");
    let results = declarations
        .iter()
        .map(|decl| {
            let decl = crate::preprocess_decl_with_context(decl, &mut file);
            crate::elaborate_decl_and_register_with_context(&mut env, &decl, &mut file).and_then(
                |result| {
                    let mut leaves = Vec::new();
                    result.leaf_decls(&mut leaves);
                    let error = leaves.iter().find_map(|leaf| match leaf {
                        crate::ElabResult::Failed { error, .. } => Some((**error).clone()),
                        _ => None,
                    });
                    match error {
                        Some(error) => Err(error),
                        None => Ok(result),
                    }
                },
            )
        })
        .collect();
    (env, results)
}

#[test]
fn section_auto_order_public_nonrecursive_positive_and_negative_twins() {
    let header = "section\nvariable (p : Prop)\ntheorem own (x : α) (hp : p) : x = x := rfl\nend\n";
    for (call, accepted) in [
        ("@own True Nat 3 True.intro", true),
        ("@own Nat True 3 True.intro", false),
    ] {
        let (env, results) = run_source(&format!("{header}theorem use : (3 : Nat) = 3 := {call}"));
        assert!(results[0].is_ok(), "{results:?}");
        assert_eq!(
            results.last().unwrap().is_ok(),
            accepted,
            "{call}: {results:?}"
        );
        assert_eq!(env.get_const(&Name::anon().str("use")).is_some(), accepted);
    }
}

#[test]
fn section_auto_order_public_definition_and_named_arguments() {
    let source = "section\nvariable (p : Prop)\ndef identityOwn (x : α) (hp : p) : α := x\nend\ntheorem use : @identityOwn True Nat 3 True.intro = 3 := rfl\ntheorem named : identityOwn (p := True) (x := 3) (hp := True.intro) = 3 := rfl";
    let (_, results) = run_source(source);
    assert!(results.iter().all(Result::is_ok), "{results:?}");
}

#[test]
fn section_auto_order_public_recursive_header_matches_its_forward_signature() {
    let header = "section\nvariable (p : Prop)\ntheorem ownRec (x : α) (hp : p) : ∀ n : Nat, x = x\n | 0 => rfl\n | n + 1 => by exact @ownRec α x hp n\nend\n";
    for (call, accepted) in [
        ("@ownRec True Nat 3 True.intro 2", true),
        ("@ownRec Nat True 3 True.intro 2", false),
    ] {
        let (_, results) = run_source(&format!("{header}theorem use : (3 : Nat) = 3 := {call}"));
        assert!(results[0].is_ok(), "{results:?}");
        assert_eq!(
            results.last().unwrap().is_ok(),
            accepted,
            "{call}: {results:?}"
        );
    }
}

#[test]
fn section_auto_order_captured_carrier_precedes_sections_and_own_auto() {
    let header = "section\nvariable (q : α → Prop)\nvariable (p : Prop)\ntheorem capturedOwn (x : α) (y : β) (hp : p) (hq : q x) : y = y := rfl\nend\n";
    for (call, accepted) in [
        (
            "@capturedOwn Nat (fun _ => True) True Bool 3 true True.intro True.intro",
            true,
        ),
        (
            "@capturedOwn Nat Bool (fun _ => True) True 3 true True.intro True.intro",
            false,
        ),
    ] {
        let (_, results) = run_source(&format!("{header}theorem use : true = true := {call}"));
        assert!(results[0].is_ok(), "{results:?}");
        assert_eq!(
            results.last().unwrap().is_ok(),
            accepted,
            "{call}: {results:?}"
        );
    }
}

#[test]
fn section_auto_order_type_only_and_opaque_declarations() {
    for declaration in ["axiom own", "opaque own"] {
        let source = format!("section\nvariable (p : Prop)\n{declaration} (x : α) (hp : p) : Nat\nend\nnoncomputable def use : Nat := @own True Nat 3 True.intro");
        let (_, results) = run_source(&source);
        assert!(
            results.iter().all(Result::is_ok),
            "{declaration}: {results:?}"
        );
    }
}

#[test]
fn section_auto_order_tracked_public_fixtures() {
    for source in [
        include_str!("../../../../tests/fixtures/section_auto_order/positive.lean"),
        include_str!("../../../../tests/fixtures/section_auto_order/declaration_kinds.lean"),
        include_str!("../../../../tests/fixtures/section_auto_order/relative_methods.lean"),
        include_str!("../../../../tests/fixtures/section_auto_order/relative_nontoplevel.lean"),
        include_str!("../../../../tests/fixtures/section_auto_order/wf_own.lean"),
    ] {
        let (_, results) = run_source(source);
        assert!(results.iter().all(Result::is_ok), "{results:?}");
    }
}

#[test]
fn section_auto_order_dependent_auto_uses_captured_section_locals() {
    let source = "section\nvariable (A : Type) (f : A → Type)\ndef dependent (x : f a) : f a := x\nend\ntheorem use : @dependent Nat (fun _ => Nat) 2 3 = 3 := rfl";
    let (_, results) = run_source(source);
    assert!(results.iter().all(Result::is_ok), "{results:?}");
}

#[test]
fn section_auto_order_prunes_unused_explicit_section_before_own_auto() {
    let source = "section\nvariable (unused : Nat)\ndef pruned (x : α) : α := by exact x\nend\ntheorem use : @pruned Nat 3 = 3 := rfl";
    let (_, results) = run_source(source);
    assert!(results.iter().all(Result::is_ok), "{results:?}");
}

#[test]
fn section_auto_order_axiom_prunes_unused_activated_instance() {
    for (header, positional, named) in [
        (
            "(x : Nat) (hp : p)",
            "@own True 3 True.intro",
            "own (p := True) (x := 3) (hp := True.intro)",
        ),
        (
            "(x : α) (y : β) (hp : p)",
            "@own True Nat Bool 3 true True.intro",
            "own (p := True) (x := 3) (y := true) (hp := True.intro)",
        ),
    ] {
        let source = format!("section\nvariable (p : Prop) [Decidable p]\naxiom own {header} : Nat\nend\nnoncomputable def positional : Nat := {positional}\nnoncomputable def named : Nat := {named}");
        let (_, results) = run_source(&source);
        assert!(results.iter().all(Result::is_ok), "{results:?}");
    }
}

#[test]
fn section_auto_order_ordinary_recursion_captures_sections_and_keeps_own_arguments() {
    let (_, results) = run_source(include_str!(
        "../../../../tests/fixtures/section_auto_order/ordinary_recursive.lean"
    ));
    let errors: Vec<_> = results
        .iter()
        .enumerate()
        .filter_map(|(index, result)| {
            result
                .as_ref()
                .err()
                .map(|error| format!("declaration {index}: {error}"))
        })
        .collect();
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}

#[test]
fn section_auto_order_ordinary_recursion_refuses_supplied_captures_and_nondecreasing_calls() {
    for (source, name) in [
        (include_str!("../../../../tests/fixtures/section_auto_order/ordinary_recursive_extra_section.lean"), "recOwn"),
        (include_str!("../../../../tests/fixtures/section_auto_order/ordinary_recursive_extra_section_ordinary_use.lean"), "recOwn"),
        (include_str!("../../../../tests/fixtures/section_auto_order/ordinary_recursive_extra_implicit_section.lean"), "recLength"),
        (include_str!("../../../../tests/fixtures/section_auto_order/ordinary_recursive_nondecreasing.lean"), "badRec"),
        (include_str!("../../../../tests/fixtures/section_auto_order/ordinary_recursive_extra_section_auto.lean"), "ordinaryMixed"),
    ] {
        let (env, results) = run_source(source);
        assert!(results.iter().any(Result::is_err), "{results:?}");
        assert!(env.get_const(&Name::from_string(name)).is_none(), "bad recursive definition registered");
    }
}

#[test]
fn section_auto_order_known_gap_unused_section_auto_is_not_pruned() {
    let (env, results) = run_source(include_str!(
        "../../../../tests/fixtures/section_auto_order/known_gap_unused_section_carrier.lean"
    ));
    for name in ["pruned", "prunedThm", "prunedRec"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "missing declaration {name}: {results:?}"
        );
    }
    for name in ["usePruned", "usePrunedThm", "usePrunedRec"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "known gap closed for {name}"
        );
    }
    let failures: Vec<_> = results
        .iter()
        .filter_map(|result| result.as_ref().err())
        .collect();
    assert_eq!(failures.len(), 3, "{results:?}");
    assert!(
        failures
            .iter()
            .all(|error| matches!(error, crate::ElabError::TypeMismatch { .. })),
        "{failures:?}"
    );
}

#[test]
fn section_auto_order_known_gap_mutual_uses_its_separate_generalizer() {
    let (env, results) = run_source(include_str!(
        "../../../../tests/fixtures/section_auto_order/known_gap_mutual_section.lean"
    ));
    assert!(
        env.get_const(&Name::from_string("mutualOwn")).is_some(),
        "{results:?}"
    );
    let error = results
        .last()
        .expect("external use present")
        .as_ref()
        .expect_err("known mutual section-order gap closed");
    assert!(
        matches!(error, crate::ElabError::TypeMismatch { .. }),
        "{error:?}"
    );
    assert!(env.get_const(&Name::from_string("use")).is_none());
}

#[test]
fn section_auto_order_well_founded_sections_require_capture_metadata() {
    let (env, results) = run_source(include_str!(
        "../../../../tests/fixtures/section_auto_order/wf_extra_section.lean"
    ));
    let error = results
        .first()
        .expect("definition present")
        .as_ref()
        .expect_err("extra captured section argument accepted");
    assert!(
        matches!(error, crate::ElabError::Unsupported { feature } if feature.contains("requires the original section locals")),
        "{error:?}"
    );
    assert!(env.get_const(&Name::from_string("wfOwn")).is_none());

    let (env, results) = run_source(include_str!(
        "../../../../tests/fixtures/section_auto_order/known_gap_wf_section.lean"
    ));
    let error = results
        .first()
        .expect("definition present")
        .as_ref()
        .expect_err("known WF capture gap closed");
    assert!(
        matches!(error, crate::ElabError::TypeMismatch { .. }),
        "{error:?}"
    );
    assert!(env.get_const(&Name::from_string("wfOwn")).is_none());
}

#[test]
fn section_auto_order_known_gap_bare_namespace_method_keeps_legacy_routing() {
    let (env, results) = run_source(include_str!(
        "../../../../tests/fixtures/section_auto_order/known_gap_namespace_method.lean"
    ));
    assert!(
        env.get_const(&Name::from_string("List.sectionCount"))
            .is_none(),
        "bare namespace method gap closed: {results:?}"
    );
    let failures: Vec<_> = results
        .iter()
        .filter_map(|result| result.as_ref().err())
        .collect();
    assert!(!failures.is_empty(), "bare namespace method gap closed");
    assert!(
        failures
            .iter()
            .any(|error| error.to_string().contains("sectionCount")),
        "{failures:?}"
    );
}
