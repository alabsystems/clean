// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use clean::kernel::{Environment, Name};
use clean::{check_source, CheckConfig, DeclWarning, EnvironmentExt};

#[test]
fn public_api_checks_and_loads_sources_incrementally() {
    let config = CheckConfig::default();

    let checked =
        check_source("def answer : Nat := 42", &config).expect("one-shot checking should succeed");
    assert!(checked.is_fully_verified(), "expected a clean check result");
    assert_eq!(checked.passed_count, 1, "expected one passed declaration");
    assert_eq!(
        checked.failed_count(),
        0,
        "expected zero failed declarations"
    );
    assert_eq!(checked.warning_count(), 0, "expected zero warnings");
    assert!(!checked.has_failures(), "expected a failure-free result");
    assert!(!checked.has_warnings(), "expected a warning-free result");
    assert_eq!(checked.declarations.len(), 1, "expected one declaration");
    assert_eq!(checked.declarations[0].name, "answer");
    assert!(checked.declarations[0].passed);

    let mut allow_sorry = CheckConfig::default();
    allow_sorry.allow_sorry = true;
    let warned = check_source("theorem deferred : True := sorry", &allow_sorry)
        .expect("allow_sorry should still return a structured result");
    assert_eq!(
        warned.failed_count(),
        0,
        "sorry allowance should avoid failures"
    );
    assert_eq!(
        warned.warning_count(),
        1,
        "expected one warning-bearing declaration"
    );
    assert!(
        !warned.has_failures(),
        "allow_sorry should keep the result non-failing"
    );
    assert!(warned.has_warnings(), "sorry should surface as a warning");
    assert!(
        warned
            .declarations
            .iter()
            .filter_map(|decl| decl.warning.as_ref())
            .any(|warning| warning.is_sorry()),
        "expected a sorry-classified warning"
    );
    assert!(
        !warned.is_fully_verified(),
        "sorry should still block full verification"
    );

    let mut env = Environment::try_with_prelude().expect("prelude should initialize");
    let first = env
        .load_lean_source("def base : Nat := 7", &config)
        .expect("initial load should succeed");
    assert!(
        first.is_fully_verified(),
        "expected the first load to be clean"
    );

    let second = env
        .load_lean_source("def derived : Nat := base", &config)
        .expect("incremental load should succeed");
    assert!(
        second.is_fully_verified(),
        "expected the second load to be clean"
    );
    assert!(
        env.get_const(&Name::from_string("base")).is_some(),
        "base should remain available in the environment"
    );
    assert!(
        env.get_const(&Name::from_string("derived")).is_some(),
        "derived should be registered in the environment"
    );
}

#[test]
fn public_api_treats_trust_warnings_as_not_fully_verified() {
    let result = check_source(
        "theorem trustedDebt : True := trustedArith",
        &CheckConfig::default(),
    )
    .expect("trustedArith source should still return a structured result");

    assert_eq!(result.warning_count(), 1);
    assert!(result.has_warnings());
    assert!(!result.has_failures());
    assert!(
        result
            .declarations
            .iter()
            .filter_map(|decl| decl.warning.as_ref())
            .any(|warning| matches!(warning, DeclWarning::TrustedArith)),
        "expected a trustedArith warning"
    );
    assert!(
        !result.is_fully_verified(),
        "trusted warnings should still block a fully verified verdict"
    );
}
