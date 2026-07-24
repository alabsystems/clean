// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end elaboration pin for the B16 `structure … where make ::` grammar.
//! The parser preserving `ctor_name` is insufficient by itself: preprocessing,
//! elaboration, kernel registration, construction, and projections must all use
//! the authored constructor rather than silently falling back to `mk`.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn collect_failures(result: &ElabResult, failures: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for result in results {
                collect_failures(result, failures);
            }
        }
        ElabResult::Failed { name, error, .. } => failures.push(format!("{name}: {error}")),
        _ => {}
    }
}

fn elaborate_file(source: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let mut file_context = FileContext::new();
    let declarations = parse_file(source).expect("B16 custom-constructor source must parse");
    for declaration in &declarations {
        let processed = preprocess_decl_with_context(declaration, &mut file_context);
        let result = elaborate_decl_and_register(&mut env, &processed)
            .unwrap_or_else(|error| panic!("B16 custom constructor must elaborate: {error}"));
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        assert!(
            failures.is_empty(),
            "inner B16 declaration failures: {failures:?}"
        );
    }
    env
}

#[test]
fn custom_structure_constructor_survives_parse_to_kernel() {
    let env = elaborate_file(
        "structure Point where\n  make ::\n  x : Nat\n  y : Nat\n\n\
         def p : Point := Point.make 1 2\n\
         theorem point_x : p.x = 1 := rfl\n\
         theorem point_y : p.y = 2 := rfl",
    );

    let point = env
        .get_inductive(&Name::from_string("Point"))
        .expect("Point inductive must register");
    assert_eq!(
        point.constructor_names,
        vec![Name::from_string("Point.make")],
        "the authored constructor name must reach kernel metadata"
    );
    assert!(
        env.get_constructor(&Name::from_string("Point.make"))
            .is_some(),
        "Point.make must be the registered constructor"
    );
    assert!(
        env.get_const(&Name::from_string("Point.mk")).is_none(),
        "custom-constructor structures must not silently register Point.mk"
    );
    for theorem in ["point_x", "point_y"] {
        assert!(env.get_const(&Name::from_string(theorem)).is_some());
        assert!(
            env.axiom_deps(&Name::from_string(theorem))
                .expect("theorem must have provenance")
                .is_empty(),
            "{theorem} must remain axiom-free"
        );
    }
}
